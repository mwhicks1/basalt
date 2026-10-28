/*
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
*/
#include <lean/lean.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

/* libFuzzer's driver entry point. Two spellings, selected at compile time:

   - Default (LLVM >= 12): the stable C entry `LLVMFuzzerRunDriver`.
   - `-DBASALT_FUZZ_LEGACY_DRIVER`: clang 11 and earlier expose no C entry, so we call the C++
     symbol `fuzzer::FuzzerDriver` by its mangled name.

   `fuzz-run/build.sh` picks the spelling by probing the runtime archive for the C entry. */
#ifdef BASALT_FUZZ_LEGACY_DRIVER
extern int _ZN6fuzzer12FuzzerDriverEPiPPPcPFiPKhmE(
    int *argc, char ***argv, int (*cb)(const uint8_t *, size_t));
#define BASALT_FUZZER_RUN_DRIVER _ZN6fuzzer12FuzzerDriverEPiPPPcPFiPKhmE
#else
extern int LLVMFuzzerRunDriver(
    int *argc, char ***argv, int (*cb)(const uint8_t *, size_t));
#define BASALT_FUZZER_RUN_DRIVER LLVMFuzzerRunDriver
#endif

/* libFuzzer's own default mutation suite, callable on any buffer we hand it. Declared here rather
   than included because the vendored runtime ships no headers. */
extern size_t LLVMFuzzerMutate(uint8_t *Data, size_t Size, size_t MaxSize);

static lean_object *g_run = NULL;   /* the Lean closure `ByteArray -> IO UInt8`, held for the run */
static int g_guided;                /* libFuzzer's buffer is the input (`go`, not `goRandom`)      */

__attribute__((noreturn)) static void basalt_fuzz_die(const char *what) {
  fprintf(stderr, "[basalt] fatal: %s\n", what);
  fflush(NULL);
  exit(1);
}

static void *basalt_grow_buf(void *p, size_t *cap, size_t need, size_t elt) {
  if (need <= *cap) return p;
  size_t c = *cap ? *cap : 64;
  while (c < need) c *= 2;
  void *q = realloc(p, c * elt);
  if (!q) basalt_fuzz_die("out of memory");
  *cap = c;
  return q;
}

/* ---------------------------------------------------------------------------------------------
   The coverage counters

   SanitizerCoverage's 8-bit counters and PC table are the linker-concatenated `__sancov_*`
   sections, in the same object order. libFuzzer resets the counters before every run, so after a
   run they are that run's.
   --------------------------------------------------------------------------------------------- */

#ifdef __APPLE__
#include <mach-o/dyld.h>
extern uint8_t __start___sancov_cntrs[] __asm("section$start$__DATA$__sancov_cntrs");
extern uint8_t __stop___sancov_cntrs[] __asm("section$end$__DATA$__sancov_cntrs");
extern const uintptr_t __start___sancov_pcs[] __asm("section$start$__DATA$__sancov_pcs");
extern const uintptr_t __stop___sancov_pcs[] __asm("section$end$__DATA$__sancov_pcs");
/* `nm` prints Mach-O addresses unslid, so an offset is the PC less the image's ASLR slide. */
static uintptr_t basalt_image_base(void) { return (uintptr_t)_dyld_get_image_vmaddr_slide(0); }
#else
extern uint8_t __start___sancov_cntrs[] __attribute__((weak));
extern uint8_t __stop___sancov_cntrs[] __attribute__((weak));
extern const uintptr_t __start___sancov_pcs[] __attribute__((weak));
extern const uintptr_t __stop___sancov_pcs[] __attribute__((weak));
extern const char __executable_start[] __attribute__((weak));
static uintptr_t basalt_image_base(void) { return (uintptr_t)__executable_start; }
#endif

/* How many counters this binary has (the ELF symbols are weak, so absent ones are null). */
static size_t basalt_ncounters(void) {
  uintptr_t start = (uintptr_t)__start___sancov_cntrs, stop = (uintptr_t)__stop___sancov_cntrs;
  return start != 0 && stop > start ? (size_t)(stop - start) : 0;
}

/* Cumulative edge coverage, for comparing backends. libFuzzer reports only a campaign-wide count,
   which also counts Basalt's own plumbing, and that differs between backends. So when
   `BASALT_COV_OUT` names a file, `g_cov.first[i]` records the 1-based index of the first run that hit
   edge `i`, and at exit every edge is written as `<offset> <first>` (`0` = never hit), the offset
   from the executable base so `nm` can attribute it to a function. `<file>.time` gives the
   milliseconds elapsed at every 1000th run. */
static struct {
  uint32_t *first;
  size_t n;
  uint32_t runs;
  FILE *time;
  struct timespec t0;
} g_cov;

static void basalt_cov_accumulate(void) {
  g_cov.runs++;
  for (size_t i = 0; i < g_cov.n; i++)
    if (__start___sancov_cntrs[i] && !g_cov.first[i]) g_cov.first[i] = g_cov.runs;
  if (g_cov.time && g_cov.runs % 1000 == 0) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    long ms = (t.tv_sec - g_cov.t0.tv_sec) * 1000 + (t.tv_nsec - g_cov.t0.tv_nsec) / 1000000;
    fprintf(g_cov.time, "%u %ld\n", g_cov.runs, ms);
  }
}

static void basalt_cov_dump(void) {
  const char *path = getenv("BASALT_COV_OUT");
  if (!g_cov.first || !path) return;
  FILE *f = fopen(path, "w");
  if (!f) return;
  for (size_t i = 0; i < g_cov.n; i++)
    fprintf(f, "%lx %u\n", (unsigned long)(__start___sancov_pcs[2 * i] - basalt_image_base()),
            (unsigned)g_cov.first[i]);
  fclose(f);
  if (g_cov.time) fflush(g_cov.time);
}

static void basalt_cov_init(void) {
  const char *path = getenv("BASALT_COV_OUT");
  g_cov.n = basalt_ncounters();
  if (!path || !g_cov.n) return;
  if ((size_t)(__stop___sancov_pcs - __start___sancov_pcs) != 2 * g_cov.n) return;
  g_cov.first = calloc(g_cov.n, sizeof *g_cov.first);
  if (!g_cov.first) return;
  atexit(basalt_cov_dump);
  char tpath[4096];
  snprintf(tpath, sizeof tpath, "%s.time", path);
  g_cov.time = fopen(tpath, "w");
  clock_gettime(CLOCK_MONOTONIC, &g_cov.t0);
}

/* ---------------------------------------------------------------------------------------------
   Features, as libFuzzer counts them

   A feature is an edge together with the bucket of its 8-bit counter (1, 2, 3, 4–7, 8–15, 16–31,
   32–127, 128+). libFuzzer's own bookkeeping (`TracePC::CollectFeatures`) is internal C++ with no
   stable entry, so a hybrid campaign reads the counters itself after each test to judge its novelty.
   --------------------------------------------------------------------------------------------- */

/* libFuzzer's `CounterToFeature`: an 8-bit counter's hit-count bucket, 0..7. */
static inline uint32_t basalt_bucket(uint8_t c) {
  return c >= 128 ? 7 : c >= 32 ? 6 : c >= 16 ? 5 : c >= 8 ? 4 : c >= 4 ? 3 : c - 1;
}

static struct {
  size_t    n;               /* counters                                                          */
  uint32_t *run;             /* the last run's features (counter index * 8 + bucket)              */
  size_t    nrun;
} g_feat;

static void basalt_feat_init(void) {
  g_feat.n = basalt_ncounters();
  if (!g_feat.n) basalt_fuzz_die("no SanitizerCoverage counters in this binary");
  g_feat.run = malloc(g_feat.n * sizeof *g_feat.run);
  if (!g_feat.run) basalt_fuzz_die("out of memory for the coverage map");
}

/* Read the last run's features into `g_feat.run`. */
static void basalt_feat_read(void) {
  const uint8_t *c = __start___sancov_cntrs;
  size_t nf = 0;
  for (size_t i = 0; i < g_feat.n; i++) {
    /* Most counters are zero; skip them a word at a time. */
    if ((i & 7) == 0 && i + 8 <= g_feat.n) {
      uint64_t w;
      memcpy(&w, c + i, 8);
      if (!w) { i += 7; continue; }
    }
    if (c[i]) g_feat.run[nf++] = (uint32_t)(i * 8 + basalt_bucket(c[i]));
  }
  g_feat.nrun = nf;
}

static inline int basalt_bit(const uint8_t *map, uint32_t f) { return map[f >> 3] & (1u << (f & 7)); }
static inline void basalt_set_bit(uint8_t *map, uint32_t f) { map[f >> 3] |= (uint8_t)(1u << (f & 7)); }

/* Mark the last run's features in `seen` (a bit per feature), and in `also` if given; how many
   were new to `seen`. */
static size_t basalt_feat_mark(uint8_t *seen, uint8_t *also) {
  size_t fresh = 0;
  for (size_t i = 0; i < g_feat.nrun; i++) {
    uint32_t f = g_feat.run[i];
    if (basalt_bit(seen, f)) continue;
    basalt_set_bit(seen, f);
    if (also) basalt_set_bit(also, f);
    fresh++;
  }
  return fresh;
}

/* ---------------------------------------------------------------------------------------------
   Hybrid campaigns (`--hybrid`)

   One libFuzzer loop, two modes. In a *random* round the callback ignores libFuzzer's buffer, runs
   the property at `RecordGen`, and returns -1, so libFuzzer neither keeps the input nor records its
   features; this file judges each test's novelty itself and keeps the recorded bytes of the new ones.
   In a *fuzz* round the callback runs libFuzzer's buffer at `FuzzGen` as usual. On a switch to fuzzing
   a set cover of the random round's finds is queued, and the custom mutator hands the queue to
   libFuzzer one seed per call, so each enters the corpus by libFuzzer's own admission rule. When to
   switch is `basalt_hy_step`'s decision; fuzz-run/README.md gives the rules.
   --------------------------------------------------------------------------------------------- */

enum { HY_FUZZ = 0, HY_RANDOM = 1 };
enum { RULE_STALE = 0, RULE_WINDOW = 1, RULE_FIXED = 2 };

/* The first tests of a round, which no rule ends it within. */
#define BASALT_STALE_FLOOR 256

typedef struct {
  uint8_t  *buf;
  size_t    size;
  uint32_t *feats;           /* its features, as `g_feat.run`                                     */
  size_t    nfeats;
} basalt_seed;

static struct {
  int          on, rule, mode, started;
  lean_object *run_random;   /* `ByteArray -> IO UInt8`, the `RecordGen` callback                 */
  lean_object *offered;      /* the bytes the last random test recorded                           */
  uint64_t     budget;       /* -runs, or 0 if unbounded                                          */
  uint64_t     fixed;        /* `fixed`: the random round's length                                */
  double       a, b;         /* `stale`: E's multiple; `window`: φ and c                          */
  uint8_t     *seen;         /* a bit per feature some test of either mode reached                */
  uint8_t     *fresh;        /* the same, for features first reached in this random round         */
  uint64_t     total, n;     /* tests run: in the campaign, in this round                         */
  uint64_t     finds;        /* F: tests that reached a feature no earlier test did               */
  double       len_sum;      /* the finds' lengths in bytes, summed                               */
  uint64_t     last_find;    /* the round's test of its last find (0: none)                       */
  uint64_t     block_start, block_finds;  /* `window`: the current window's start and finds       */
  basalt_seed *seeds;        /* this random round's finds                                         */
  size_t       nseeds, cap;
  basalt_seed *queue;        /* the cover, waiting to be handed to libFuzzer                       */
  size_t       nqueue, qpos;
} g_hy;

static void basalt_hy_keep(lean_object *bytes) {
  if (g_hy.nseeds == g_hy.cap) {
    size_t cap = g_hy.cap ? 2 * g_hy.cap : 256;
    basalt_seed *p = realloc(g_hy.seeds, cap * sizeof *p);
    if (!p) basalt_fuzz_die("out of memory keeping random-round seeds");
    g_hy.seeds = p;
    g_hy.cap = cap;
  }
  basalt_seed *sd = &g_hy.seeds[g_hy.nseeds++];
  sd->size = lean_sarray_size(bytes);
  sd->buf = malloc(sd->size ? sd->size : 1);
  sd->feats = malloc((g_feat.nrun ? g_feat.nrun : 1) * sizeof *sd->feats);
  if (!sd->buf || !sd->feats) basalt_fuzz_die("out of memory keeping random-round seeds");
  memcpy(sd->buf, lean_sarray_cptr(bytes), sd->size);
  memcpy(sd->feats, g_feat.run, g_feat.nrun * sizeof *sd->feats);
  sd->nfeats = g_feat.nrun;
}

/* A max-heap of seed indices by (gain, then smaller input). */
static size_t *g_heap, g_heap_n;
static size_t *g_gain;
static int basalt_heap_above(size_t a, size_t b) {
  if (g_gain[a] != g_gain[b]) return g_gain[a] > g_gain[b];
  return g_hy.seeds[a].size < g_hy.seeds[b].size;
}
static void basalt_heap_push(size_t x) {
  size_t i = g_heap_n++;
  g_heap[i] = x;
  while (i && basalt_heap_above(g_heap[i], g_heap[(i - 1) / 2])) {
    size_t p = (i - 1) / 2, t = g_heap[i];
    g_heap[i] = g_heap[p]; g_heap[p] = t; i = p;
  }
}
static size_t basalt_heap_pop(void) {
  size_t top = g_heap[0];
  g_heap[0] = g_heap[--g_heap_n];
  size_t i = 0;
  for (;;) {
    size_t l = 2 * i + 1, r = l + 1, m = i;
    if (l < g_heap_n && basalt_heap_above(g_heap[l], g_heap[m])) m = l;
    if (r < g_heap_n && basalt_heap_above(g_heap[r], g_heap[m])) m = r;
    if (m == i) break;
    size_t t = g_heap[i]; g_heap[i] = g_heap[m]; g_heap[m] = t; i = m;
  }
  return top;
}

/* Queue a greedy set cover of this random round's new features — not of every feature its seeds hit,
   most of which an earlier round already covers. Lazy greedy: a seed's gain only falls as others are
   chosen, so a popped seed whose recomputed gain still tops the heap is the greedy choice. Seeds left
   out are freed; chosen ones move to the queue. */
static void basalt_hy_cover(void) {
  size_t n = g_hy.nseeds;
  uint8_t *covered = calloc(g_feat.n, 1);
  g_heap = malloc((n ? n : 1) * sizeof *g_heap);
  g_gain = malloc((n ? n : 1) * sizeof *g_gain);
  basalt_seed *q = malloc((n ? n : 1) * sizeof *q);
  if (!covered || !g_heap || !g_gain || !q) basalt_fuzz_die("out of memory compressing seeds");
  g_heap_n = 0;
  for (size_t i = 0; i < n; i++) {
    size_t gain = 0;
    for (size_t j = 0; j < g_hy.seeds[i].nfeats; j++) gain += basalt_bit(g_hy.fresh, g_hy.seeds[i].feats[j]) != 0;
    g_gain[i] = gain;
    basalt_heap_push(i);
  }
  size_t nq = 0;
  while (g_heap_n) {
    size_t i = basalt_heap_pop();
    basalt_seed *sd = &g_hy.seeds[i];
    size_t gain = 0;
    for (size_t j = 0; j < sd->nfeats; j++)
      gain += basalt_bit(g_hy.fresh, sd->feats[j]) && !basalt_bit(covered, sd->feats[j]);
    if (!gain) continue;
    g_gain[i] = gain;
    if (g_heap_n && basalt_heap_above(g_heap[0], i)) { basalt_heap_push(i); continue; }
    for (size_t j = 0; j < sd->nfeats; j++) basalt_set_bit(covered, sd->feats[j]);
    q[nq] = *sd;
    q[nq++].feats = NULL;                               /* freed with the rest, below            */
    sd->buf = NULL;                                     /* moved to the queue                    */
  }
  for (size_t i = 0; i < n; i++) { free(g_hy.seeds[i].buf); free(g_hy.seeds[i].feats); }
  for (size_t i = g_hy.qpos; i < g_hy.nqueue; i++) free(g_hy.queue[i].buf);
  free(g_hy.queue);
  g_hy.queue = q; g_hy.nqueue = nq; g_hy.qpos = 0;
  g_hy.nseeds = 0;
  memset(g_hy.fresh, 0, g_feat.n);
  fprintf(stderr, "[basalt] random round: %zu finds, %zu seeds after set cover\n", n, nq);
  free(covered); free(g_heap); free(g_gain); g_heap = NULL; g_gain = NULL;
}

static void basalt_hy_switch(void) {
  fprintf(stderr, "[basalt] switch to %s after test %llu (%llu in the round; %llu finds)\n",
          g_hy.mode == HY_RANDOM ? "fuzzing" : "random", (unsigned long long)g_hy.total,
          (unsigned long long)g_hy.n, (unsigned long long)g_hy.finds);
  if (g_hy.mode == HY_RANDOM) basalt_hy_cover();
  g_hy.mode = g_hy.mode == HY_RANDOM ? HY_FUZZ : HY_RANDOM;
  g_hy.n = g_hy.last_find = g_hy.block_start = g_hy.block_finds = 0;
}

/* A round's stale effort, `E = L̄ · ln L̄` for `L̄` the finds' mean length in bytes: about the
   random-position mutations it takes to touch each of an input's `L̄` bytes once, the coupon
   collector's bound. Fuzzing spends that per corpus input, and the campaign's finds stand in for the
   corpus's size. */
static double basalt_stale_effort(void) {
  double lbar = g_hy.finds ? g_hy.len_sum / (double)g_hy.finds : 1;
  double e = lbar > 1 ? lbar * log(lbar) : 1;
  if (g_hy.mode == HY_FUZZ) e *= (double)(g_hy.finds ? g_hy.finds : 1);
  return e * g_hy.a;
}

/* The window rule's window: long enough that a round still finding at the rate worth staying for
   would show `c` finds in it. That rate is `φ · F / H`, at which the rest of the budget `H` would add
   a further `φ` of the finds so far; without `-runs`, `H` is the round's own length. Recomputed after
   every test, since `F` and `H` move. */
static uint64_t basalt_window(void) {
  uint64_t h = g_hy.budget ? (g_hy.budget > g_hy.total ? g_hy.budget - g_hy.total : 1)
                           : (g_hy.n ? g_hy.n : 1);
  double rate = g_hy.a * (double)(g_hy.finds ? g_hy.finds : 1) / (double)h;
  double w = g_hy.b / rate;
  return w > 1e18 ? (uint64_t)1e18 : (uint64_t)w + 1;
}

/* After every test once the loop has started: count it, and switch if the rule says so. `fresh` is
   whether it was a find, `len` its length in bytes. */
static void basalt_hy_step(int fresh, uint64_t len) {
  g_hy.n++;
  g_hy.total++;
  if (fresh) { g_hy.finds++; g_hy.len_sum += (double)len; g_hy.last_find = g_hy.n; }
  switch (g_hy.rule) {
  case RULE_FIXED:
    if (g_hy.mode == HY_RANDOM && g_hy.n >= g_hy.fixed) basalt_hy_switch();
    return;
  case RULE_STALE:
    if (g_hy.n >= BASALT_STALE_FLOOR && (double)(g_hy.n - g_hy.last_find) >= basalt_stale_effort())
      basalt_hy_switch();
    return;
  case RULE_WINDOW:
    if (g_hy.mode != HY_RANDOM) return;
    g_hy.block_finds += fresh != 0;
    if (g_hy.n - g_hy.block_start < basalt_window()) return;
    if ((double)g_hy.block_finds < g_hy.b) { basalt_hy_switch(); return; }
    g_hy.block_start = g_hy.n;
    g_hy.block_finds = 0;
    return;
  }
}

/* The custom mutator's share: before libFuzzer's first mutation the campaign enters its random
   round; in a random round the buffer is ignored, so it is returned as is; and a queued seed replaces
   the mutation, so libFuzzer runs it and admits it on its own terms. Returns 0 to leave the call to
   the ordinary mutator. */
static size_t basalt_hy_mutate(uint8_t *Data, size_t Size, size_t MaxSize) {
  if (!g_hy.started) {
    g_hy.started = 1;
    g_hy.mode = HY_RANDOM;
  }
  if (g_hy.mode == HY_RANDOM) {
    if (!Size) { Data[0] = 0; return 1; }
    return Size;
  }
  while (g_hy.qpos < g_hy.nqueue) {
    basalt_seed *sd = &g_hy.queue[g_hy.qpos++];
    size_t n = sd->size < MaxSize ? sd->size : MaxSize;
    if (n) memcpy(Data, sd->buf, n);
    free(sd->buf);
    sd->buf = NULL;
    if (n) return n;
  }
  return 0;
}

/* Called from the `RecordGen` callback with the bytes the test recorded; held until its coverage has
   been judged. */
LEAN_EXPORT lean_object *basalt_hybrid_offer(lean_object *bytes) {
  if (g_hy.offered) lean_dec(g_hy.offered);
  g_hy.offered = bytes;
  return lean_box(0);
}

/* Arm a hybrid campaign; called before `basalt_fuzz_go`. `rule`, `fixed`, `a` and `b` are
   `SwitchRule.encode`'s. */
LEAN_EXPORT lean_object *basalt_hybrid_config(lean_object *run_random, uint8_t rule, uint64_t fixed,
                                              double a, double b, uint64_t budget) {
#ifdef BASALT_FUZZ_LEGACY_DRIVER
  /* The legacy driver ignores a `-1` return, so it would admit a random round's buffers, which are
     not those tests' inputs, into the corpus. */
  basalt_fuzz_die("--hybrid needs libFuzzer from LLVM 12 or later (this one ignores a -1 return)");
#endif
  g_hy.on = 1;
  g_hy.run_random = run_random;
  g_hy.rule = rule;
  g_hy.fixed = fixed;
  g_hy.a = a;
  g_hy.b = b;
  g_hy.budget = budget;
  return lean_io_result_mk_ok(lean_box(0));             /* `IO`, unlike the `BaseIO` externs here */
}

/* ---------------------------------------------------------------------------------------------
   Truncation (`--truncate`)

   Before libFuzzer mutates the input it has just run, the input is cut to the bytes its run read,
   so that the mutation lands on bytes the run used. The cut input runs exactly as before, since
   `readByte` reads `0` past the end. Only the input just run is cut: an input libFuzzer picks from
   its corpus to start a mutation chain has no run at hand to say how much of it was read.
   --------------------------------------------------------------------------------------------- */

static int g_trunc;           /* `--truncate`                                                    */

static struct {
  uint64_t runs;              /* tests on libFuzzer's buffer                                     */
  uint64_t random;            /* a hybrid campaign's random-round tests                         */
  uint64_t starved;           /* runs that read past the end of their buffer                    */
  uint64_t max_deficit;       /* how far off `-max_len` is, if it is                            */
  uint64_t cut, cut_bytes;    /* inputs truncated, and the bytes that removed                   */
} g_stats;

static uint64_t g_cursor;     /* the bytes the current run read, from `basalt_fuzz_note_cursor`  */

/* The last run's input and how many bytes it read. */
static struct { uint8_t *buf; size_t size, cap; uint64_t cursor; int valid; } g_last;

/* Called from Lean at the end of each run with how many bytes it read, past the end included.
   Called while `LLVMFuzzerTestOneInput` is still on the stack, so it is the current run's. */
LEAN_EXPORT lean_object *basalt_fuzz_note_cursor(uint64_t cursor) {
  g_cursor = cursor;
  return lean_box(0);                               /* Unit */
}

/* After a run, under `--truncate` or `--cmp`: remember it as the last run. */
static void basalt_after_run(const uint8_t *Data, size_t Size) {
  g_last.buf = basalt_grow_buf(g_last.buf, &g_last.cap, Size ? Size : 1, 1);
  if (Size) memcpy(g_last.buf, Data, Size);
  g_last.size = Size;
  g_last.cursor = g_cursor;
  g_last.valid = 1;
}

/* The size to cut `Data` to before mutating it: its cursor, if it is the last run's input. */
static size_t basalt_truncate(const uint8_t *Data, size_t Size) {
  if (!g_last.valid || Size != g_last.size || (Size && memcmp(Data, g_last.buf, Size) != 0))
    return Size;
  uint64_t cursor = g_last.cursor;
  if (cursor >= Size) return Size;
  if (cursor == 0) cursor = 1;          /* libFuzzer's mutators want a nonempty input               */
  g_stats.cut++;
  g_stats.cut_bytes += Size - cursor;
  return (size_t)cursor;
}

/* ---------------------------------------------------------------------------------------------
   Recorded draws (`--cmp`)

   Under `--cmp` every run records its draws (`FuzzState.trace`) and hands them over once, after the
   run. Planting into an input needs its run's draws: the last run's, when libFuzzer mutates the input
   it just ran, or else a cache's, which keeps the draws of every input that reached a feature new to
   libFuzzer — the inputs it puts in its corpus (it can also keep an input that is smaller than another
   with the same features, which this misses). The cache holds at most `BASALT_TRACE_CACHE_MB`
   megabytes; past that, inputs are planted into only when they start no chain.
   --------------------------------------------------------------------------------------------- */

#define BASALT_TRACE_CACHE_MB 256

static int g_cmp;             /* `--cmp`                                                          */

/* The last run's draws, four words each (`FuzzState.trace`, decoded). */
static struct { uint64_t *w; size_t n, cap; } g_tr;

/* Called from Lean after a recorded run with its draws, packed. */
LEAN_EXPORT lean_object *basalt_fuzz_note_trace(b_lean_obj_arg arr) {
  size_t n = lean_sarray_size(arr) / 8;
  const uint8_t *p = lean_sarray_cptr(arr);
  g_tr.w = basalt_grow_buf(g_tr.w, &g_tr.cap, n ? n : 1, sizeof *g_tr.w);
  for (size_t i = 0; i < n; i++) {
    uint64_t x = 0;
    for (int k = 7; k >= 0; k--) x = (x << 8) | p[8 * i + k];
    g_tr.w[i] = x;
  }
  g_tr.n = n;
  return lean_box(0);
}

/* SplitMix64's finalizer, as a hash. */
static inline uint64_t basalt_mix64(uint64_t z) {
  z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
  z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
  return z ^ (z >> 31);
}

static uint64_t basalt_hash_buf(const uint8_t *d, size_t n) {
  uint64_t h = 0xcbf29ce484222325ULL;
  for (size_t i = 0; i < n; i++) h = (h ^ d[i]) * 0x100000001b3ULL;
  return basalt_mix64(h) | 1;           /* never 0, which marks an empty slot                       */
}

/* An open-addressed table of inputs, keyed by their bytes, with their runs' draws. */
typedef struct {
  uint64_t  key;
  uint8_t  *buf;
  size_t    size;
  uint64_t *w;
  size_t    n;
} basalt_entry;

static struct { basalt_entry *e; size_t cap, n, bytes; uint64_t full; } g_cache;

/* Per counter, a bit per bucket that some run libFuzzer judged reached (`Features`). */
static uint8_t *g_cmp_seen;

static basalt_entry *basalt_cache_find(const uint8_t *d, size_t size) {
  if (!g_cache.cap) return NULL;
  uint64_t key = basalt_hash_buf(d, size);
  for (size_t i = key & (g_cache.cap - 1);; i = (i + 1) & (g_cache.cap - 1)) {
    basalt_entry *e = &g_cache.e[i];
    if (!e->key) return NULL;
    if (e->key == key && e->size == size && (!size || memcmp(e->buf, d, size) == 0)) return e;
  }
}

/* Keep the last run's draws for its input `d`, unless the cache is full. */
static void basalt_cache_put(const uint8_t *d, size_t size) {
  size_t need = size + g_tr.n * sizeof *g_tr.w + sizeof(basalt_entry);
  if (g_cache.bytes + need > (size_t)BASALT_TRACE_CACHE_MB << 20) { g_cache.full++; return; }
  if (basalt_cache_find(d, size)) return;
  if (2 * (g_cache.n + 1) > g_cache.cap) {
    size_t cap = g_cache.cap ? 2 * g_cache.cap : 4096;
    basalt_entry *e = calloc(cap, sizeof *e);
    if (!e) basalt_fuzz_die("out of memory caching draws");
    for (size_t i = 0; i < g_cache.cap; i++)
      if (g_cache.e[i].key) {
        size_t j = g_cache.e[i].key & (cap - 1);
        while (e[j].key) j = (j + 1) & (cap - 1);
        e[j] = g_cache.e[i];
      }
    free(g_cache.e);
    g_cache.e = e;
    g_cache.cap = cap;
  }
  uint64_t key = basalt_hash_buf(d, size);
  size_t j = key & (g_cache.cap - 1);
  while (g_cache.e[j].key) j = (j + 1) & (g_cache.cap - 1);
  basalt_entry *e = &g_cache.e[j];
  e->buf = malloc(size ? size : 1);
  e->w = malloc((g_tr.n ? g_tr.n : 1) * sizeof *e->w);
  if (!e->buf || !e->w) basalt_fuzz_die("out of memory caching draws");
  if (size) memcpy(e->buf, d, size);
  memcpy(e->w, g_tr.w, g_tr.n * sizeof *e->w);
  e->key = key; e->size = size; e->n = g_tr.n;
  g_cache.n++;
  g_cache.bytes += need;
}

/* The draws of `Data`'s run: the last run's, or the cache's; NULL if neither knows it. */
static const uint64_t *basalt_trace_of(const uint8_t *Data, size_t Size, size_t *n) {
  if (g_last.valid && Size == g_last.size && (!Size || memcmp(Data, g_last.buf, Size) == 0)) {
    *n = g_tr.n;
    return g_tr.w;
  }
  basalt_entry *e = basalt_cache_find(Data, Size);
  if (!e) return NULL;
  *n = e->n;
  return e->w;
}

/* ---------------------------------------------------------------------------------------------
   Planting compared values (`--cmp`)

   libFuzzer's `Mutate_AddWordFromTORC`, at the level of draws: one more mutator beside libFuzzer's
   thirteen, taking 1/14 of the custom mutator's calls. It takes a pair `(A, B)` the instrumented code
   compared and, in a random direction, finds a recorded draw whose *decoded* value is `A` and writes
   `B + d` there, `d` in {-1, 0, +1} as libFuzzer's `Arg + Rand(-1, 1)`; with no such draw, any draw
   whose range admits it, as libFuzzer falls back to a random position. libFuzzer's own version writes
   the word into bytes, which `choose` then reduces modulo its range; writing `v` into a draw
   overwrites exactly its `bytesFor (hi - lo + 1)` bytes with `v - lo`, big-endian, which `drawStep`
   decodes back to `v`. A harvested literal (`harvested_literals%`) is an unpaired constant and goes
   the second way. A value whose plant reached a new feature is kept, and a third of the picks reuse
   one, as libFuzzer's persistent auto-dictionary does.

   The pairs come from SanitizerCoverage's `trace-cmp` hooks, wrapped at link time (`--wrap`, so the
   runtime's own hooks still run), and from Lean `Nat` comparisons, which compare tagged pointers:
   `nat_hook.h`, force-included into the targets' code, hands their untagged operands to
   `basalt_nat_cmp` while `basalt_nat_hook_on` is set.
   --------------------------------------------------------------------------------------------- */

/* Read by `nat_hook.h`'s wrappers. */
int basalt_nat_hook_on = 0;

/* The mutator's PRNG, seeded from libFuzzer's `Seed` on every call, so `-seed` fixes it. */
static uint64_t g_rng;
static inline uint64_t basalt_rand(void) { g_rng += 0x9e3779b97f4a7c15ULL; return basalt_mix64(g_rng); }
static inline uint64_t basalt_below(uint64_t n) { return n ? basalt_rand() % n : 0; }

/* The comparison pairs, as libFuzzer's tables of recent compares keep them: a slot per `a ^ b`, later
   pairs evicting earlier ones. A Lean scalar compared by the inlined fast path arrives tagged
   (`2n+1`), so a pair of odd operands is also kept untagged. */
#define BASALT_PAIRS 1024
static struct { uint64_t a[BASALT_PAIRS], b[BASALT_PAIRS]; uint8_t used[BASALT_PAIRS]; size_t n; } g_pairs;

static inline void basalt_pair_add(uint64_t a, uint64_t b) {
  if (a == b) return;
  size_t i = basalt_mix64(a ^ b) & (BASALT_PAIRS - 1);
  if (!g_pairs.used[i]) { g_pairs.used[i] = 1; g_pairs.n++; }
  g_pairs.a[i] = a; g_pairs.b[i] = b;
}
static inline void basalt_cmp_seen(uint64_t a, uint64_t b) {
  if (!g_cmp) return;
  basalt_pair_add(a, b);
  if ((a & 1) && (b & 1)) basalt_pair_add(a >> 1, b >> 1);
}

#ifdef BASALT_CMP_WRAP
extern void __real___sanitizer_cov_trace_cmp8(uint64_t, uint64_t);
extern void __real___sanitizer_cov_trace_const_cmp8(uint64_t, uint64_t);
extern void __real___sanitizer_cov_trace_cmp4(uint32_t, uint32_t);
extern void __real___sanitizer_cov_trace_const_cmp4(uint32_t, uint32_t);
void __wrap___sanitizer_cov_trace_cmp8(uint64_t a, uint64_t b) {
  basalt_cmp_seen(a, b); __real___sanitizer_cov_trace_cmp8(a, b);
}
void __wrap___sanitizer_cov_trace_const_cmp8(uint64_t a, uint64_t b) {
  basalt_cmp_seen(a, b); __real___sanitizer_cov_trace_const_cmp8(a, b);
}
void __wrap___sanitizer_cov_trace_cmp4(uint32_t a, uint32_t b) {
  basalt_cmp_seen(a, b); __real___sanitizer_cov_trace_cmp4(a, b);
}
void __wrap___sanitizer_cov_trace_const_cmp4(uint32_t a, uint32_t b) {
  basalt_cmp_seen(a, b); __real___sanitizer_cov_trace_const_cmp4(a, b);
}
#endif

/* A Lean `Nat` comparison's untagged operands (`nat_hook.h`), for `--cmp` and for libFuzzer's own table
   of recent compares. */
#ifdef BASALT_CMP_WRAP
void basalt_nat_cmp(uint64_t a, uint64_t b) { basalt_cmp_seen(a, b); __real___sanitizer_cov_trace_cmp8(a, b); }
#else
extern void __sanitizer_cov_trace_cmp8(uint64_t, uint64_t);
void basalt_nat_cmp(uint64_t a, uint64_t b) { basalt_cmp_seen(a, b); __sanitizer_cov_trace_cmp8(a, b); }
#endif

/* The target's own literals. */
static struct { uint64_t *v; size_t n, cap; int off; } g_lits;

LEAN_EXPORT lean_object *basalt_cmp_literal(uint64_t n) {
  g_lits.v = basalt_grow_buf(g_lits.v, &g_lits.cap, g_lits.n + 1, sizeof *g_lits.v);
  g_lits.v[g_lits.n++] = n;
  return lean_box(0);
}

LEAN_EXPORT lean_object *basalt_cmp_arm(uint8_t literals) {
  g_cmp = 1;
  basalt_nat_hook_on = 1;
  g_lits.off = !literals;
  return lean_io_result_mk_ok(lean_box(0));
}

/* Values whose plant reached a new feature, oldest overwritten first. */
#define BASALT_KEPT 256
static struct { uint64_t v[BASALT_KEPT]; size_t n, next; } g_kept;

static struct {
  uint64_t planted, matched, literals, kept, untraced;  /* `literals`: plants of a literal       */
  uint64_t ok, bad, gone;                /* the next run decoded the plant, decoded otherwise, or
                                            never reached the draw                                */
  int pending; uint64_t at, v;           /* the plant the next run should decode                  */
} g_pl;

/* `Basalt.Fuzz.bytesFor (hi - lo + 1)`. */
static size_t basalt_draw_width(uint64_t lo, uint64_t hi) {
  uint64_t span = hi - lo;
  size_t bits = 0;
  while (bits < 64 && (span >> bits)) bits++;
  return (bits + 7) / 8;
}

/* Write `v` into draw `d` of trace `tw`; the new size, or 0 if it does not fit. */
static size_t basalt_write_draw(const uint64_t *tw, uint8_t *Data, size_t Size, size_t MaxSize,
                                size_t d, uint64_t v) {
  const uint64_t *w = tw + 4 * d;
  uint64_t lo = w[0], hi = w[1], at = w[3];
  if (hi < lo || v < lo || v > hi || v == w[2]) return 0;
  size_t width = basalt_draw_width(lo, hi);
  if (at + width > MaxSize) return 0;
  if (at + width > Size) { memset(Data + Size, 0, at + width - Size); Size = at + width; }
  uint64_t raw = v - lo;
  for (size_t k = 0; k < width; k++) Data[at + width - 1 - k] = (uint8_t)(raw >> (8 * k));
  g_pl.pending = 1; g_pl.at = at; g_pl.v = v;
  g_pl.planted++;
  return Size;
}

/* Maybe plant a value into `Data`, whose run's trace is `tw` (`n` words); its new size, or 0 to
   leave the call to libFuzzer's suite. */
static size_t basalt_cmp(const uint64_t *tw, size_t n, uint8_t *Data, size_t Size, size_t MaxSize,
                         unsigned Seed) {
  g_rng = Seed;
  if (basalt_below(14)) return 0;
  if (!tw) { g_pl.untraced++; return 0; }
  size_t nd = n / 4;
  if (!nd) return 0;
  int64_t dl = (int64_t)basalt_below(3) - 1;
  size_t nlits = g_lits.off ? 0 : g_lits.n;
  uint64_t want, from = 0;
  int paired = 0, lit = 0;
  uint64_t r = basalt_below(3);
  if (r == 0 && g_kept.n) want = g_kept.v[basalt_below(g_kept.n)];
  else if ((r == 1 || !nlits) && g_pairs.n) {
    size_t i = basalt_below(BASALT_PAIRS);
    while (!g_pairs.used[i]) i = (i + 1) & (BASALT_PAIRS - 1);
    int flip = basalt_rand() & 1;
    from = flip ? g_pairs.b[i] : g_pairs.a[i];
    want = flip ? g_pairs.a[i] : g_pairs.b[i];
    paired = 1;
  } else if (nlits) { want = g_lits.v[basalt_below(nlits)]; lit = 1; }
  else return 0;
  want += (uint64_t)dl;
  if (paired) {                           /* where the compared value was, among up to 8 draws  */
    size_t pos[8], np = 0, start = basalt_below(nd);
    for (size_t q = 0; q < nd && np < 8; q++) {
      size_t d = (start + q) % nd;
      if (tw[4 * d + 2] == from) pos[np++] = d;
    }
    if (np) {
      size_t got = basalt_write_draw(tw, Data, Size, MaxSize, pos[basalt_below(np)], want);
      if (got) { g_pl.matched++; return got; }
    }
  }
  for (int t = 0; t < 8; t++) {           /* else any draw whose range admits it                */
    size_t got = basalt_write_draw(tw, Data, Size, MaxSize, basalt_below(nd), want);
    if (got) { g_pl.literals += lit; return got; }
  }
  return 0;
}

/* After a run: did the draw a plant wrote decode to the planted value? A changed earlier draw can
   move control flow off it (`gone`), but a draw starting at the offset must hold the value. And a
   plant that reached a new feature is kept for reuse. */
static void basalt_cmp_after(size_t fresh) {
  if (!g_pl.pending) return;
  g_pl.pending = 0;
  size_t d = 0, nd = g_tr.n / 4;
  while (d < nd && g_tr.w[4 * d + 3] != g_pl.at) d++;
  if (d == nd) g_pl.gone++;
  else if (g_tr.w[4 * d + 2] == g_pl.v) g_pl.ok++;
  else g_pl.bad++;
  if (!fresh) return;
  for (size_t i = 0; i < g_kept.n; i++) if (g_kept.v[i] == g_pl.v) return;
  g_kept.v[g_kept.next] = g_pl.v;
  g_kept.next = (g_kept.next + 1) % BASALT_KEPT;
  if (g_kept.n < BASALT_KEPT) g_kept.n++;
  g_pl.kept++;
}

/* The campaign's buffer statistics, on stderr. Called from two disjoint exits — `atexit` for the
   `-runs`-exhausted path, and the failure path below, which `abort()`s past `atexit` handlers.
   Printed from C rather than returned to Lean because a `String`-returning extern is the one shape
   of this bridge that gets the `BaseIO` ABI wrong silently. */
static void basalt_fuzz_report_stats(void) {
  if (!g_stats.runs && !g_stats.random) return;
  fprintf(stderr, "[basalt] runs %llu", (unsigned long long)(g_stats.runs + g_stats.random));
  if (g_hy.on) fprintf(stderr, " (%llu in random rounds)", (unsigned long long)g_stats.random);
  fprintf(stderr, ", starved %llu (max deficit %llu B)", (unsigned long long)g_stats.starved,
          (unsigned long long)g_stats.max_deficit);
  if (g_trunc)
    fprintf(stderr, "; truncated %llu inputs, %.1f bytes each on average",
            (unsigned long long)g_stats.cut,
            g_stats.cut ? (double)g_stats.cut_bytes / (double)g_stats.cut : 0.0);
  fprintf(stderr, "\n");
  if (g_cmp)
    fprintf(stderr, "[basalt] cmp: %llu planted (%llu where the compared value was, %llu of literals, "
            "%llu kept); %zu pairs, %zu literals; %llu inputs with no draws known; the next run "
            "decoded %llu as planted, %llu otherwise, and %llu never reached the draw; %zu inputs' draws "
            "cached, %.1f MB (%llu not, the cache full)\n",
            (unsigned long long)g_pl.planted, (unsigned long long)g_pl.matched,
            (unsigned long long)g_pl.literals, (unsigned long long)g_pl.kept, g_pairs.n,
            g_lits.off ? 0 : g_lits.n, (unsigned long long)g_pl.untraced,
            (unsigned long long)g_pl.ok, (unsigned long long)g_pl.bad, (unsigned long long)g_pl.gone,
            g_cache.n, (double)g_cache.bytes / 1e6, (unsigned long long)g_cache.full);
}

/* This replaces libFuzzer's mutator: a hybrid campaign's share first (`basalt_hy_mutate`), then
   truncation under `--truncate`, then under `--cmp` sometimes a planted value (`basalt_cmp`), and
   otherwise libFuzzer's default suite.

   `Seed` is libFuzzer's own PRNG output and is unused.

   The visibility attribute is load-bearing: libFuzzer finds this by
   `dlsym(RTLD_DEFAULT, "LLVMFuzzerCustomMutator")`, so under the hidden-visibility default the
   symbol stays `private external`, the lookup fails silently, and the campaign runs the default
   mutators untruncated. `fuzz-run/build.sh` checks the linked binary exports it. */
__attribute__((visibility("default")))
size_t LLVMFuzzerCustomMutator(uint8_t *Data, size_t Size, size_t MaxSize, unsigned Seed) {
  (void)Seed;
  if (g_hy.on) {
    size_t hy = basalt_hy_mutate(Data, Size, MaxSize);
    if (hy) return hy;
  }
  size_t n = 0;
  const uint64_t *tw = g_cmp ? basalt_trace_of(Data, Size, &n) : NULL;   /* before cutting `Data` */
  if (g_trunc) Size = basalt_truncate(Data, Size);
  if (g_cmp) {
    size_t planted = basalt_cmp(tw, n, Data, Size, MaxSize, Seed);
    if (planted) return planted;
  }
  return LLVMFuzzerMutate(Data, Size, MaxSize);
}

/* Apply a Lean `ByteArray -> IO UInt8` callback to a copy of libFuzzer's buffer; the code it returns. */
static uint8_t basalt_apply(lean_object *f, const uint8_t *Data, size_t Size) {
  lean_object *arr = lean_alloc_sarray(1, Size, Size);
  memcpy(lean_sarray_cptr(arr), Data, Size);
  lean_inc(f);                                        /* apply consumes the function object   */
  lean_object *res = lean_apply_2(f, arr, lean_io_mk_world());
  if (!lean_io_result_is_ok(res)) {
    /* An exception -- this signals a broken harness, so end the campaign. */
    lean_io_result_show_error(res);
    lean_dec(res);
    basalt_fuzz_die("the property raised an exception");
  }
  uint8_t code = (uint8_t)lean_unbox(lean_io_result_get_value(res));
  lean_dec(res);
  return code;
}

/* A random round's test: the buffer is not its input, so libFuzzer must neither keep it nor learn
   from its coverage (-1). */
static int basalt_hy_random_test(const uint8_t *Data, size_t Size) {
  uint8_t code = basalt_apply(g_hy.run_random, Data, Size);
  g_stats.random++;
  if (g_cov.first) basalt_cov_accumulate();
  if (code == 1) {
    /* The Lean side reported it and saved the recorded bytes. Exit past libFuzzer: its exit hook
       would save the buffer in hand as the crash, and that buffer is not this test's input. */
    basalt_cov_dump();
    basalt_fuzz_report_stats();
    fflush(NULL);
    _exit(77);
  }
  size_t fresh = 0;
  if (code != 2) {
    basalt_feat_read();
    fresh = basalt_feat_mark(g_hy.seen, g_hy.fresh);
    if (fresh && g_hy.offered) basalt_hy_keep(g_hy.offered);
  }
  basalt_hy_step(fresh != 0, g_hy.offered ? lean_sarray_size(g_hy.offered) : 0);
  return -1;
}

/* Libfuzzer harness -- called by libFuzzer loop during testing.
   Failure model follows bolero (lib/bolero-libfuzzer): the Lean closure prints the counterexample,
   returns code 1, and we abort(). libFuzzer's signal handler then saves the crashing input as an
   artifact (reproduce with `basalt-fuzz replay`) and exits with its error code. */
int LLVMFuzzerTestOneInput(const uint8_t *Data, size_t Size) {
  if (g_hy.on && g_hy.started && g_hy.mode == HY_RANDOM) return basalt_hy_random_test(Data, Size);
  g_cursor = 0;
  uint8_t code = basalt_apply(g_run, Data, Size);

  g_stats.runs++;
  if (g_cov.first) basalt_cov_accumulate();
  if (g_guided) {
    if (g_cursor > Size) {
      g_stats.starved++;
      if (g_cursor - Size > g_stats.max_deficit) g_stats.max_deficit = g_cursor - Size;
    }
    if (g_trunc || g_cmp) basalt_after_run(Data, Size);
  }
  int hy = g_hy.on && g_hy.started;
  size_t new_lf = 0, new_hy = 0;
  if ((g_cmp || hy) && code != 2) {       /* libFuzzer ignores a rejected run's features too  */
    basalt_feat_read();
    if (g_cmp) new_lf = basalt_feat_mark(g_cmp_seen, NULL);
    if (hy) new_hy = basalt_feat_mark(g_hy.seen, NULL);
  }
  if (g_cmp) {
    if (new_lf) basalt_cache_put(Data, Size);
    basalt_cmp_after(new_lf);
  }
  if (hy) basalt_hy_step(new_hy != 0, g_cursor);

  if (code == 1) {
    basalt_cov_dump();                                /* abort() skips the atexit handlers     */
    basalt_fuzz_report_stats();
    fflush(NULL);                                     /* the Lean side flushed its own handles */
    abort();                                          /* property failed → libFuzzer saves it */
  }
  return (code == 2) ? -1 : 0;    /* discard → not added to the corpus (LLVM >= 12; the legacy
                                     driver ignores the code) */
}

/* Called from Lean's `main` via @[extern]. Stores the closure and hands control to libFuzzer.
   Returns only if the campaign completes without a failure (a failure aborts the process). */
LEAN_EXPORT lean_object *basalt_fuzz_go(lean_object *run, lean_object *argv, uint8_t guided,
                                        uint8_t truncate) {
  g_run = run;
  g_guided = guided;
  g_trunc = guided && truncate;
  if (g_guided) atexit(basalt_fuzz_report_stats);  /* the `-runs`-exhausted path exits here */
  if (g_hy.on || g_cmp) basalt_feat_init();
  if (g_cmp && !(g_cmp_seen = calloc(g_feat.n, 1))) basalt_fuzz_die("out of memory for --cmp");
  if (g_hy.on) {
    g_hy.seen = calloc(g_feat.n, 1);
    g_hy.fresh = calloc(g_feat.n, 1);
    if (!g_hy.seen || !g_hy.fresh) basalt_fuzz_die("out of memory for the hybrid campaign's coverage map");
  }
  basalt_cov_init();

  /* `av` and its strings are deliberately never freed: the driver may rewrite both `argc` and `av`
     as it consumes its own flags, so the pointers we would free are not the ones we allocated. */
  size_t n = lean_array_size(argv);
  char **av = (char **)malloc((n + 2) * sizeof(char *));
  if (!av) basalt_fuzz_die("out of memory building the fuzzer command line");
  av[0] = strdup("basalt-fuzz");
  for (size_t i = 0; i < n; i++)
    av[i + 1] = strdup(lean_string_cstr(lean_array_get_core(argv, i)));
  for (size_t i = 0; i < n + 1; i++)
    if (!av[i]) basalt_fuzz_die("out of memory building the fuzzer command line");
  av[n + 1] = NULL;
  int argc = (int)n + 1;

  BASALT_FUZZER_RUN_DRIVER(&argc, &av, LLVMFuzzerTestOneInput);

  lean_dec(g_run);
  g_run = NULL;
  lean_dec(argv);
  return lean_io_result_mk_ok(lean_box(0));
}
