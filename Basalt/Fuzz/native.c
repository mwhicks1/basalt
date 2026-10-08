/*
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
*/
#include <lean/lean.h>
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

__attribute__((noreturn)) static void basalt_fuzz_die(const char *what) {
  fprintf(stderr, "[basalt] fatal: %s\n", what);
  fflush(NULL);
  exit(1);
}

/* ---------------------------------------------------------------------------------------------
   Buffer growth (`--grow`, off by default)

   A generator can outrun its buffer, and `Basalt.Fuzz.readByte` gives it `0` past the end. Those
   zeros are invisible to the fuzzer: not being in the input, no byte mutator can reach the positions
   that produced them. `--grow` materializes them — a run reports how far it overshot, and the next
   mutation starts from the extended form.

   fuzz-run/README.md gives the design and some preliminary experimental data.
   --------------------------------------------------------------------------------------------- */

static int g_grow = 0;

/* If the last run reported a deficit, it is stored in `g_last_run_deficit`. That run's buffer
   is stored in `g_short`. The custom mutator checks if the last run had a deficit, and if
   the to-be mutated buffer is the same as last one, in which case it will zero-extend that
   buffer before mutating it. */
static uint32_t g_last_run_deficit = 0;

static struct {
  uint8_t *buf;
  size_t   cap;               /* allocated, never shrunk; see `basalt_fuzz_record_short`        */
  size_t   size;
} g_short;

/* Stats about the fuzzing run. */
static struct {
  uint64_t runs;
  uint64_t starved;           /* runs that read past the end of their buffer                    */
  uint32_t max_deficit;       /* how far off `-max_len` is, if it is                            */
  uint64_t grew;
  uint64_t cap_blocked;       /* wanted more but was already at `-max_len`                      */
} g_stats;

/* Called from Lean at the conclusion of a single property test run to note whether the run
   demanded more bytes than were available (so deficit is non-zero). Called while
   `LLVMFuzzerTestOneInput` is still on the stack, so `g_last_run_deficit` is the current run's. */
LEAN_EXPORT lean_object *basalt_fuzz_note_deficit(uint32_t deficit) {
  g_stats.runs++;
  if (deficit) {
    g_stats.starved++;
    if (deficit > g_stats.max_deficit) g_stats.max_deficit = deficit;
    if (g_grow) g_last_run_deficit = deficit;         /* no slot is maintained with `--grow` off      */
  }
  return lean_box(0);                               /* Unit */
}

/* Called from LLVMFuzzerTestOneInput at the conclusion of the Lean function's property test
   run in the case that there was a deficit. This function makes a copy of the input, which
   a subsequent custom mutator call will check, to make sure that it is zero-extending
   the right buffer. `g_last_run_deficit` is already set; this pairs it with its bytes, or retires it
   if that cannot be done. */
static void basalt_fuzz_record_short(const uint8_t *Data, size_t Size) {
  if (Size > g_short.cap) {
    size_t cap = g_short.cap ? g_short.cap : 64;
    while (cap < Size) cap *= 2;
    uint8_t *p = (uint8_t *)realloc(g_short.buf, cap);
    if (!p) {
      g_last_run_deficit = 0;      /* no growth, so can't zero-extend the deficit buffer. */
      return;
    }
    g_short.buf = p;
    g_short.cap = cap;
  }
  if (Size) memcpy(g_short.buf, Data, Size);
  g_short.size = Size;
}

/* Whether `Data` is the input the slot's deficit was measured on. */
static int basalt_fuzz_slot_matches(const uint8_t *Data, size_t Size) {
  return Size == g_short.size && (Size == 0 || memcmp(Data, g_short.buf, Size) == 0);
}

/* The campaign's buffer statistics, on stderr. Called from two disjoint exits — `atexit` for the
   `-runs`-exhausted path, and the failure path below, which `abort()`s past `atexit` handlers.
   Printed from C rather than returned to Lean because a `String`-returning extern is the one shape
   of this bridge that gets the `BaseIO` ABI wrong silently (see `basalt_fuzz_note_deficit`). */
static void basalt_fuzz_report_stats(void) {
  if (!g_stats.runs) return;
  fprintf(stderr, "[basalt] runs %llu, starved %llu (max deficit %u B)",
          (unsigned long long)g_stats.runs, (unsigned long long)g_stats.starved,
          g_stats.max_deficit);
  if (g_grow)
    fprintf(stderr, ", grew %llu times, %llu at the -max_len cap\n",
            (unsigned long long)g_stats.grew, (unsigned long long)g_stats.cap_blocked);
  else
    fprintf(stderr, " [--grow off]\n");
}

/* This replaces libFuzzer's mutator. If we are in --grow mode, and the prior run
   experienced a deficit, and did so when using the provided `Data` buffer, then this code
   will grow buffer (not exceeding its `MaxSize`) and zero-extend its contents up to the
   deficit, prior to mutating. If there was no deficit or we were not in --grow
   mode, we go straight to mutation, which is just the default behavior.

   `Seed` is libFuzzer's own PRNG output and is unused: the tail is determined, not chosen.

   The visibility attribute is load-bearing: libFuzzer finds this by
   `dlsym(RTLD_DEFAULT, "LLVMFuzzerCustomMutator")`, so under the hidden-visibility default the
   symbol stays `private external`, the lookup fails silently, and the campaign runs the default
   mutators as if `--grow` had never been asked for. `fuzz-run/build.sh` checks the linked binary
   exports it. */
static size_t basalt_hybrid_mutate(uint8_t *Data, size_t Size, size_t MaxSize);

__attribute__((visibility("default")))
size_t LLVMFuzzerCustomMutator(uint8_t *Data, size_t Size, size_t MaxSize, unsigned Seed) {
  (void)Seed;
  size_t hybrid = basalt_hybrid_mutate(Data, Size, MaxSize);
  if (hybrid) return hybrid;
  size_t want = g_last_run_deficit;
  if (g_grow && want && basalt_fuzz_slot_matches(Data, Size)) {
    g_last_run_deficit = 0;                          /* one growth per observation                  */
    if (Size >= MaxSize) {
      g_stats.cap_blocked++;                      /* -max_len is the ceiling on structure size   */
    } else {
      if (want > MaxSize - Size) want = MaxSize - Size;
      memset(Data + Size, 0, want);
      g_stats.grew++;
      Size += want;
    }
  }
  return LLVMFuzzerMutate(Data, Size, MaxSize);
}

/* Cumulative edge coverage, for comparing backends (`fuzz-run/compare-coverage.sh`). libFuzzer resets
   the SanitizerCoverage counters before every run and reports only a campaign-wide edge count, which
   also counts Basalt's own plumbing, and that differs between backends. So when `BASALT_COV_OUT`
   names a file, each run's counters are scanned and `g_cov_first[i]` records the 1-based index of the
   first run that hit edge `i`; at exit every edge of the PC table is written as `<offset> <first>`
   (`0` = never hit), where offset is from the executable base so `nm` can attribute it to a function.
   The first-hit index is what gives coverage as a function of tests run; `<file>.time` gives it as a
   function of time, as the milliseconds elapsed at every 1000th run. The counters and the PC table are
   the linker-concatenated `__sancov_*` sections, in the same object order. */
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

/* Whether this binary has any counters (the ELF symbols are weak, so absent ones are null). */
static int basalt_have_counters(void) {
  uintptr_t start = (uintptr_t)__start___sancov_cntrs, stop = (uintptr_t)__stop___sancov_cntrs;
  return start != 0 && stop > start;
}
static uint32_t *g_cov_first;
static size_t g_cov_n;
static uint32_t g_cov_runs;
static FILE *g_cov_time;
static struct timespec g_cov_t0;

static void basalt_cov_accumulate(void) {
  g_cov_runs++;
  for (size_t i = 0; i < g_cov_n; i++)
    if (__start___sancov_cntrs[i] && !g_cov_first[i]) g_cov_first[i] = g_cov_runs;
  if (g_cov_time && g_cov_runs % 1000 == 0) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    long ms = (t.tv_sec - g_cov_t0.tv_sec) * 1000 + (t.tv_nsec - g_cov_t0.tv_nsec) / 1000000;
    fprintf(g_cov_time, "%u %ld\n", g_cov_runs, ms);
  }
}

static void basalt_cov_dump(void) {
  const char *path = getenv("BASALT_COV_OUT");
  if (!g_cov_first || !path) return;
  FILE *f = fopen(path, "w");
  if (!f) return;
  for (size_t i = 0; i < g_cov_n; i++)
    fprintf(f, "%lx %u\n", (unsigned long)(__start___sancov_pcs[2 * i] - basalt_image_base()),
            (unsigned)g_cov_first[i]);
  fclose(f);
  if (g_cov_time) fflush(g_cov_time);
}

static void basalt_cov_init(void) {
  if (!getenv("BASALT_COV_OUT") || !basalt_have_counters()) return;
  g_cov_n = (size_t)(__stop___sancov_cntrs - __start___sancov_cntrs);
  if ((size_t)(__stop___sancov_pcs - __start___sancov_pcs) != 2 * g_cov_n) return;
  g_cov_first = calloc(g_cov_n, sizeof *g_cov_first);
  if (!g_cov_first) return;
  atexit(basalt_cov_dump);
  char tpath[4096];
  snprintf(tpath, sizeof tpath, "%s.time", getenv("BASALT_COV_OUT"));
  g_cov_time = fopen(tpath, "w");
  clock_gettime(CLOCK_MONOTONIC, &g_cov_t0);
}


/* ---------------------------------------------------------------------------------------------
   Hybrid campaigns (`--warmup`, `--warmup-stall`, `--switch-back`)

   One libFuzzer loop, two modes. In *random* mode the callback ignores libFuzzer's buffer, runs the
   property at `RecordGen`, and returns -1, so libFuzzer neither keeps the input nor records its
   features; this file judges each run's coverage itself and keeps the recorded bytes of the new ones.
   In *fuzz* mode the callback runs libFuzzer's buffer at `FuzzGen` as usual. On a switch to fuzz mode a
   set cover of the random phase's finds is queued, and the custom mutator hands the queue to libFuzzer
   one seed at a time, so each enters the corpus by libFuzzer's own admission rule.

   When to switch is `basalt_phase_step`'s decision; fuzz-run/README.md gives the rule.
   --------------------------------------------------------------------------------------------- */

/* libFuzzer's `CounterToFeature`: an 8-bit counter's hit-count bucket, 0..7. */
static inline uint32_t basalt_bucket(uint8_t c) {
  return c >= 128 ? 7 : c >= 32 ? 6 : c >= 16 ? 5 : c >= 8 ? 4 : c >= 4 ? 3 : c - 1;
}

enum { BASALT_FUZZ = 0, BASALT_RANDOM = 1 };

typedef struct {
  uint8_t  *buf;
  size_t    size;
  uint32_t *feats;           /* counter index * 8 + bucket, one per counter the run hit           */
  size_t    nfeats;
} basalt_seed;

static struct {
  int          on;           /* a hybrid campaign at all                                          */
  int          adaptive;     /* the first random phase ends on the rule, not only at `first_max`  */
  int          switch_back;  /* fuzz phases end on the rule too                                   */
  uint64_t     first_max;    /* cap on the first random phase                                     */
  uint64_t     min_window;   /* K                                                                 */
  double       level, conf;  /* φ and c                                                           */
  uint64_t     budget;       /* -runs, or 0 if unbounded                                          */
  lean_object *run_random;   /* `ByteArray -> IO UInt8`, the `RecordGen` callback                 */
  lean_object *offered;      /* the bytes the last random run recorded                            */
  int          mode, started, trace;
  uint32_t     phases;       /* phases begun, the first random one included                       */
  uint64_t     total;        /* tests run, every phase                                            */
  uint64_t     n;            /* tests run in this phase                                           */
  uint64_t     block_start, block_len, block_new;  /* the current window: start, length, finds */
  double       left_rate[2]; /* per mode, its find rate over the window it was left on; 0 = never  */
  uint64_t     features;     /* distinct features reached, the whole campaign                     */
  uint64_t     finds;        /* F: tests that reached a feature no earlier test did               */
  size_t       ncntrs;
  uint8_t     *seen;         /* per counter, a bit per bucket some run reached                    */
  uint8_t     *fresh;        /* the same, for features first reached in this random phase         */
  uint32_t    *scratch;      /* the current run's features, `ncntrs` long                         */
  basalt_seed *seeds;        /* this random phase's new runs                                      */
  size_t       nseeds, cap;
  basalt_seed *queue;        /* the cover, waiting to be handed to libFuzzer                       */
  size_t       nqueue, qpos;
} g_hy;

/* Scan the counters after a run: record its features in `scratch` and count those never reached
   before. The counters are only read; libFuzzer resets them before each run. */
static size_t basalt_hybrid_scan(size_t *nf_out) {
  const uint8_t *c = __start___sancov_cntrs;
  size_t nf = 0, fresh = 0;
  for (size_t i = 0; i < g_hy.ncntrs; i++) {
    /* Most counters are zero; skip them a word at a time. */
    if ((i & 7) == 0 && i + 8 <= g_hy.ncntrs) {
      uint64_t w;
      memcpy(&w, c + i, 8);
      if (!w) { i += 7; continue; }
    }
    if (!c[i]) continue;
    uint32_t b = basalt_bucket(c[i]);
    g_hy.scratch[nf++] = (uint32_t)(i * 8 + b);
    if (!(g_hy.seen[i] & (1u << b))) {
      g_hy.seen[i] |= (uint8_t)(1u << b);
      if (g_hy.mode == BASALT_RANDOM) g_hy.fresh[i] |= (uint8_t)(1u << b);
      fresh++;
    }
  }
  *nf_out = nf;
  g_hy.features += fresh;
  if (fresh) g_hy.finds++;
  return fresh;
}

static void basalt_hybrid_keep(lean_object *bytes, size_t nf) {
  if (g_hy.nseeds == g_hy.cap) {
    size_t cap = g_hy.cap ? 2 * g_hy.cap : 256;
    basalt_seed *p = realloc(g_hy.seeds, cap * sizeof *p);
    if (!p) basalt_fuzz_die("out of memory keeping random-phase seeds");
    g_hy.seeds = p;
    g_hy.cap = cap;
  }
  basalt_seed *sd = &g_hy.seeds[g_hy.nseeds++];
  sd->size = lean_sarray_size(bytes);
  sd->buf = malloc(sd->size ? sd->size : 1);
  sd->feats = malloc((nf ? nf : 1) * sizeof *sd->feats);
  if (!sd->buf || !sd->feats) basalt_fuzz_die("out of memory keeping random-phase seeds");
  memcpy(sd->buf, lean_sarray_cptr(bytes), sd->size);
  memcpy(sd->feats, g_hy.scratch, nf * sizeof *sd->feats);
  sd->nfeats = nf;
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

static inline int basalt_bit(const uint8_t *map, uint32_t f) { return map[f >> 3] & (1u << (f & 7)); }

/* Queue a greedy set cover of this random phase's new features — not every feature its seeds hit,
   most of which an earlier phase already covers. Lazy greedy: a seed's gain only falls as others are
   chosen, so a popped seed whose recomputed gain still tops the heap is the greedy choice. Seeds left
   out are freed; chosen ones move to the queue. */
static void basalt_hybrid_cover(void) {
  size_t n = g_hy.nseeds;
  uint8_t *covered = calloc(g_hy.ncntrs ? g_hy.ncntrs : 1, 1);
  g_heap = malloc((n ? n : 1) * sizeof *g_heap);
  g_gain = malloc((n ? n : 1) * sizeof *g_gain);
  basalt_seed *q = malloc((n ? n : 1) * sizeof *q);
  if (!covered || !g_heap || !g_gain || !q) basalt_fuzz_die("out of memory compressing seeds");
  g_heap_n = 0;
  for (size_t i = 0; i < n; i++) {
    size_t gain = 0;
    for (size_t j = 0; j < g_hy.seeds[i].nfeats; j++)
      if (basalt_bit(g_hy.fresh, g_hy.seeds[i].feats[j])) gain++;
    g_gain[i] = gain;
    basalt_heap_push(i);
  }
  size_t nq = 0;
  while (g_heap_n) {
    size_t i = basalt_heap_pop();
    basalt_seed *sd = &g_hy.seeds[i];
    size_t gain = 0;
    for (size_t j = 0; j < sd->nfeats; j++)
      if (basalt_bit(g_hy.fresh, sd->feats[j]) && !basalt_bit(covered, sd->feats[j])) gain++;
    if (!gain) continue;
    g_gain[i] = gain;
    if (g_heap_n && basalt_heap_above(g_heap[0], i)) { basalt_heap_push(i); continue; }
    for (size_t j = 0; j < sd->nfeats; j++)
      covered[sd->feats[j] >> 3] |= (uint8_t)(1u << (sd->feats[j] & 7));
    q[nq] = *sd;
    q[nq++].feats = NULL;                               /* freed with the rest, below            */
    sd->buf = NULL;                                     /* moved to the queue                    */
  }
  for (size_t i = 0; i < n; i++) { free(g_hy.seeds[i].buf); free(g_hy.seeds[i].feats); }
  for (size_t i = g_hy.qpos; i < g_hy.nqueue; i++) free(g_hy.queue[i].buf);
  free(g_hy.queue);
  g_hy.queue = q; g_hy.nqueue = nq; g_hy.qpos = 0;
  g_hy.nseeds = 0;
  memset(g_hy.fresh, 0, g_hy.ncntrs);
  fprintf(stderr, "[basalt] random phase: %zu new runs, %zu seeds after set cover\n", n, nq);
  free(covered); free(g_heap); free(g_gain); g_heap = NULL; g_gain = NULL;
}

/* The window a block is judged over: long enough that a phase still making finds at the rate worth
   staying for would show `conf` of them in it. That rate is the lower of two: `level * F / H`, at which
   the rest of the budget would add a further `level` of the finds so far; and the other mode's rate
   when it was last left, since handing over to a mode that was doing worse is churn. A find is a test
   that reached new coverage, not a feature: one find brings tens of features at once, so a count of
   features is far too clumped to read as a rate. Recomputed after every test, since `F` and `H` move. */
static uint64_t basalt_phase_window(void) {
  uint64_t horizon = g_hy.budget ? (g_hy.budget > g_hy.total ? g_hy.budget - g_hy.total : 1)
                                 : (g_hy.n ? g_hy.n : 1);
  double f = g_hy.finds ? (double)g_hy.finds : 1.0;
  double rate = g_hy.level * f / (double)horizon;
  double other = g_hy.left_rate[g_hy.mode == BASALT_RANDOM ? BASALT_FUZZ : BASALT_RANDOM];
  if (other > 0 && other < rate) rate = other;
  double w = g_hy.conf / rate;
  uint64_t len = w > 1e18 ? (uint64_t)1e18 : (uint64_t)w + 1;
  return len > g_hy.min_window ? len : g_hy.min_window;
}

static void basalt_phase_block(void) {
  g_hy.block_start = g_hy.n;
  g_hy.block_new = 0;
}

static void basalt_phase_switch(void) {
  fprintf(stderr, "[basalt] switch to %s after test %llu (%llu in the phase; %llu finds, %llu features)\n",
          g_hy.mode == BASALT_RANDOM ? "fuzzing" : "random", (unsigned long long)g_hy.total,
          (unsigned long long)g_hy.n, (unsigned long long)g_hy.finds,
          (unsigned long long)g_hy.features);
  /* `+ 1`: a window that found nothing still bounds the rate only by about one per window. */
  uint64_t span = g_hy.n - g_hy.block_start;
  g_hy.left_rate[g_hy.mode] = ((double)g_hy.block_new + 1) / (double)(span ? span : 1);
  if (g_hy.mode == BASALT_RANDOM) basalt_hybrid_cover();
  g_hy.mode = g_hy.mode == BASALT_RANDOM ? BASALT_FUZZ : BASALT_RANDOM;
  g_hy.phases++;
  g_hy.n = 0;
  basalt_phase_block();
}

/* After every test once the loop has started: advance the phase, and switch if it has leveled off. */
static void basalt_phase_step(size_t fresh) {
  g_hy.n++;
  g_hy.block_new += fresh ? 1 : 0;
  int first = g_hy.phases == 1 && g_hy.mode == BASALT_RANDOM;
  if (first && g_hy.n >= g_hy.first_max) { basalt_phase_switch(); return; }
  g_hy.block_len = basalt_phase_window();
  if (g_hy.n - g_hy.block_start < g_hy.block_len) return;
  int quiet = (double)g_hy.block_new < g_hy.conf;
  if (g_hy.trace)
    fprintf(stderr, "[basalt] phase %u %s: test %llu, n %llu, F %llu, window %llu found %llu%s\n",
            g_hy.phases, g_hy.mode == BASALT_RANDOM ? "random" : "fuzz",
            (unsigned long long)g_hy.total, (unsigned long long)g_hy.n,
            (unsigned long long)g_hy.finds, (unsigned long long)g_hy.block_len,
            (unsigned long long)g_hy.block_new, quiet ? " (quiet)" : "");
  int decides = g_hy.mode == BASALT_RANDOM ? (first ? g_hy.adaptive : 1) : g_hy.switch_back;
  if (quiet && decides) basalt_phase_switch();
  else basalt_phase_block();
}

/* The custom mutator's share: before libFuzzer's first mutation the campaign enters its random
   phase; in a random phase the buffer is ignored, so it is returned as is; and a queued seed replaces
   the mutation, so libFuzzer runs it and admits it on its own terms. Returns 0 to leave the call to
   the ordinary mutator. */
static size_t basalt_hybrid_mutate(uint8_t *Data, size_t Size, size_t MaxSize) {
  if (!g_hy.on) return 0;
  if (!g_hy.started) {
    g_hy.started = 1;
    g_hy.mode = BASALT_RANDOM;
    g_hy.phases = 1;
    basalt_phase_block();
  }
  if (g_hy.mode == BASALT_RANDOM) {
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

/* Called from the `RecordGen` callback with the bytes the run recorded; held until the run's
   coverage has been judged. */
LEAN_EXPORT lean_object *basalt_hybrid_offer(lean_object *bytes) {
  if (g_hy.offered) lean_dec(g_hy.offered);
  g_hy.offered = bytes;
  return lean_box(0);
}

/* Arm a hybrid campaign; called before `basalt_fuzz_go`. */
LEAN_EXPORT lean_object *basalt_hybrid_config(lean_object *run_random, uint64_t first_max,
    uint64_t min_window, double level, double conf, uint64_t budget, uint8_t adaptive,
    uint8_t switch_back) {
  if (!basalt_have_counters()) basalt_fuzz_die("hybrid: no SanitizerCoverage counters in this binary");
  g_hy.on = 1;
  g_hy.run_random = run_random;
  g_hy.first_max = first_max ? first_max : UINT64_MAX;
  g_hy.min_window = min_window;
  g_hy.level = level > 0 ? level : 1;
  g_hy.conf = conf > 0 ? conf : 10;
  g_hy.budget = budget;
  g_hy.adaptive = adaptive;
  g_hy.switch_back = switch_back;
  g_hy.trace = getenv("BASALT_PHASE_TRACE") != NULL;
  g_hy.ncntrs = (size_t)(__stop___sancov_cntrs - __start___sancov_cntrs);
  g_hy.seen = calloc(g_hy.ncntrs, 1);
  g_hy.fresh = calloc(g_hy.ncntrs, 1);
  g_hy.scratch = malloc(g_hy.ncntrs * sizeof *g_hy.scratch);
  if (!g_hy.seen || !g_hy.fresh || !g_hy.scratch)
    basalt_fuzz_die("out of memory for the hybrid campaign's coverage map");
  return lean_io_result_mk_ok(lean_box(0));             /* `IO`, unlike the `BaseIO` externs here */
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

/* Libfuzzer harness -- called by libFuzzer loop during testing.
   Failure model follows bolero (lib/bolero-libfuzzer): the Lean closure prints the counterexample,
   returns code 1, and we abort(). libFuzzer's signal handler then saves the crashing input as an
   artifact (reproduce with `basalt-fuzz replay`) and exits with its error code. */
int LLVMFuzzerTestOneInput(const uint8_t *Data, size_t Size) {
  if (g_hy.on && g_hy.mode == BASALT_RANDOM && g_hy.started) {
    /* A random test: the buffer is not its input, so libFuzzer must neither keep it nor learn from
       its coverage (-1). */
    uint8_t code = basalt_apply(g_hy.run_random, Data, Size);
    if (g_cov_first) basalt_cov_accumulate();
    if (code == 1) {
      /* The Lean side reported it and saved the recorded bytes. Exit past libFuzzer: its exit hook
         would save the buffer in hand as the crash, and that buffer is not this test's input. */
      basalt_cov_dump();
      basalt_fuzz_report_stats();
      fflush(NULL);
      _exit(77);
    }
    g_hy.total++;
    size_t nf, fresh = basalt_hybrid_scan(&nf);
    if (fresh && g_hy.offered) basalt_hybrid_keep(g_hy.offered, nf);
    basalt_phase_step(fresh);
    return -1;
  }

  g_last_run_deficit = 0;                    /* `basalt_fuzz_note_deficit` sets it if this run runs short */
  uint8_t code = basalt_apply(g_run, Data, Size);

  /* If there was a deficit, save the offending buffer. Will be checked by the custom mutator. */
  if (g_last_run_deficit) basalt_fuzz_record_short(Data, Size);
  if (g_cov_first) basalt_cov_accumulate();
  if (g_hy.on) {
    g_hy.total++;
    size_t nf, fresh = basalt_hybrid_scan(&nf);
    if (g_hy.started) basalt_phase_step(fresh);
  }

  if (code == 1) {
    basalt_cov_dump();                                /* abort() skips this atexit handler too  */
    basalt_fuzz_report_stats();                       /* abort() skips the atexit handler      */
    fflush(NULL);                                     /* the Lean side flushed its own handles */
    abort();                                          /* property failed → libFuzzer saves it */
  }
  return (code == 2) ? -1 : 0;    /* discard → not added to the corpus (LLVM >= 12; the legacy
                                     driver ignores the code) */
}

/* Called from Lean's `main` via @[extern]. Stores the closure and hands control to libFuzzer.
   Returns only if the campaign completes without a failure (a failure aborts the process). */
LEAN_EXPORT lean_object *basalt_fuzz_go(lean_object *run, lean_object *argv, uint8_t grow) {
  g_run = run;
  g_grow = grow;
  atexit(basalt_fuzz_report_stats);   /* the `-runs`-exhausted path exits here, not through Lean */
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
