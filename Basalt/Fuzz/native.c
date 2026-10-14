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
static uint64_t g_last_run_seed = 0;   /* the run's fill seed, under `--fill=random`              */

static struct {
  uint8_t *buf;
  size_t   cap;               /* allocated, never shrunk; see `basalt_fuzz_record_short`        */
  size_t   size;
  uint64_t seed;              /* the fill seed the slot's run read past its end with            */
} g_short;

/* `--fill=random`: a read past the end is `basalt_fill_byte(seed, i)`, as `Basalt.Fuzz.fillByte`. */
static int g_fill_random = 0;

/* `Basalt.Fuzz.mix64`, which must agree with this: both pin `mix64 1` (`basalt_fuzz_go`). */
static inline uint64_t basalt_mix64(uint64_t z) {
  z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
  z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
  return z ^ (z >> 31);
}
static inline uint8_t basalt_fill_byte(uint64_t seed, size_t i) {
  return (uint8_t)basalt_mix64(seed + ((uint64_t)i + 1) * 0x9e3779b97f4a7c15ULL);
}

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
LEAN_EXPORT lean_object *basalt_fuzz_note_deficit(uint32_t deficit, uint64_t seed) {
  g_stats.runs++;
  g_last_run_seed = seed;
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
  g_short.seed = g_last_run_seed;
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

static void basalt_diag_parent(const uint8_t *Data, size_t Size, int seeded);

__attribute__((visibility("default")))
size_t LLVMFuzzerCustomMutator(uint8_t *Data, size_t Size, size_t MaxSize, unsigned Seed) {
  (void)Seed;
  size_t hybrid = basalt_hybrid_mutate(Data, Size, MaxSize);
  basalt_diag_parent(Data, Size, hybrid != 0);
  if (hybrid) return hybrid;
  size_t want = g_last_run_deficit;
  if (g_grow && want && basalt_fuzz_slot_matches(Data, Size)) {
    g_last_run_deficit = 0;                          /* one growth per observation                  */
    if (Size >= MaxSize) {
      g_stats.cap_blocked++;                      /* -max_len is the ceiling on structure size   */
    } else {
      if (want > MaxSize - Size) want = MaxSize - Size;
      if (g_fill_random)                         /* the bytes the run read, materialized          */
        for (size_t i = 0; i < want; i++) Data[Size + i] = basalt_fill_byte(g_short.seed, Size + i);
      else
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

/* ---------------------------------------------------------------------------------------------
   Recorded draws (`--trace-probe`, `--diag-mutations`, off by default)

   The Lean side records each run's draws (`Basalt.Fuzz.FuzzState.trace`: `lo`, `hi`, value, and the
   cursor before the draw) and hands them over once, after the run. The probe keeps the traces of
   runs that reached a new feature in a table keyed by the buffer, and does nothing else with them:
   it is the bookkeeping a choice-sequence mutator would need, measured on its own. The mutation log
   adds, for every mutated input, a `BASALT_M` line on stderr comparing the run with its parent's:

     BASALT_M <run> <parent run> <class> <first draw changed> <draw edit distance> <new feature>
              <draws> <bytes read> <first byte changed> <parent's bytes read>

   `<run>` counts every call of the callback, so it is also the index of the run's `BASALT_H` line.
   `<class>` is `a` (same draws, and the bytes the parent read unchanged), `b` (same draws, though
   bytes it read changed), `v` (different draws), `m` (the parent's trace is unknown), `s` (a queued
   hybrid seed, not a mutation) or `n` (no mutation, e.g. libFuzzer's initial inputs). Assumes zero
   fill: under random fill a parent's unread tail is not what `a` compares.
   --------------------------------------------------------------------------------------------- */

static int g_probe = 0, g_diag = 0;
static uint64_t g_run_idx;           /* every call of the callback, random phases included          */

static struct { uint64_t *w; size_t n, cap; uint64_t cursor; } g_tr;   /* the last run's trace      */

static void *basalt_grow_buf(void *p, size_t *cap, size_t need, size_t elt) {
  if (need <= *cap) return p;
  size_t c = *cap ? *cap : 64;
  while (c < need) c *= 2;
  void *q = realloc(p, c * elt);
  if (!q) basalt_fuzz_die("out of memory recording draws");
  *cap = c;
  return q;
}

LEAN_EXPORT lean_object *basalt_fuzz_note_trace(uint64_t cursor, b_lean_obj_arg arr) {
  size_t n = lean_array_size(arr);
  g_tr.w = basalt_grow_buf(g_tr.w, &g_tr.cap, n, sizeof *g_tr.w);
  for (size_t i = 0; i < n; i++) g_tr.w[i] = lean_unbox_uint64(lean_array_get_core(arr, i));
  g_tr.n = n;
  g_tr.cursor = cursor;
  return lean_box(0);
}

static uint64_t basalt_hash_buf(const uint8_t *d, size_t n) {
  uint64_t h = 0xcbf29ce484222325ULL;
  for (size_t i = 0; i < n; i++) h = (h ^ d[i]) * 0x100000001b3ULL;
  return basalt_mix64(h) | 1;          /* never 0, which marks an empty slot                         */
}

typedef struct {
  uint64_t key, run, cursor;
  uint64_t *w;
  size_t    n;
  uint8_t  *buf;
  size_t    size;
} basalt_tentry;

static struct {
  basalt_tentry *e;
  size_t cap, n, bytes;
  uint64_t lookups, misses, draws;
} g_tc;

static basalt_tentry *basalt_tc_find(uint64_t key, const uint8_t *d, size_t size) {
  if (!g_tc.cap) return NULL;
  for (size_t i = key & (g_tc.cap - 1);; i = (i + 1) & (g_tc.cap - 1)) {
    basalt_tentry *e = &g_tc.e[i];
    if (!e->key) return NULL;
    if (e->key == key && e->size == size && (!size || memcmp(e->buf, d, size) == 0)) return e;
  }
}

static void basalt_tc_put(const uint8_t *d, size_t size) {
  if (2 * (g_tc.n + 1) > g_tc.cap) {
    size_t cap = g_tc.cap ? 2 * g_tc.cap : 4096;
    basalt_tentry *old = g_tc.e;
    size_t oldcap = g_tc.cap;
    g_tc.e = calloc(cap, sizeof *g_tc.e);
    if (!g_tc.e) basalt_fuzz_die("out of memory caching traces");
    g_tc.cap = cap;
    for (size_t i = 0; i < oldcap; i++)
      if (old[i].key) {
        size_t j = old[i].key & (cap - 1);
        while (g_tc.e[j].key) j = (j + 1) & (cap - 1);
        g_tc.e[j] = old[i];
      }
    free(old);
  }
  uint64_t key = basalt_hash_buf(d, size);
  if (basalt_tc_find(key, d, size)) return;
  size_t j = key & (g_tc.cap - 1);
  while (g_tc.e[j].key) j = (j + 1) & (g_tc.cap - 1);
  basalt_tentry *e = &g_tc.e[j];
  e->w = malloc((g_tr.n ? g_tr.n : 1) * sizeof *e->w);
  e->buf = malloc(size ? size : 1);
  if (!e->w || !e->buf) basalt_fuzz_die("out of memory caching traces");
  memcpy(e->w, g_tr.w, g_tr.n * sizeof *e->w);
  memcpy(e->buf, d, size);
  e->key = key; e->n = g_tr.n; e->size = size; e->cursor = g_tr.cursor; e->run = g_run_idx;
  g_tc.n++;
  g_tc.bytes += g_tr.n * sizeof *e->w + size + sizeof *e;
}

enum { PAR_NONE = 0, PAR_OK, PAR_MISS, PAR_SEED };
static struct {
  int kind;
  uint64_t run, cursor;
  uint64_t *w; size_t n, wcap;
  uint8_t *buf; size_t size, bcap;
} g_par;
static struct { uint8_t *buf; size_t size, cap; uint64_t run; } g_last;   /* the last run's buffer */

/* From the custom mutator, before it mutates: find the parent's trace. */
static void basalt_diag_parent(const uint8_t *Data, size_t Size, int seeded) {
  if (!g_diag) return;
  g_par.kind = PAR_NONE;
  if (g_hy.on && g_hy.mode == BASALT_RANDOM) return;
  if (seeded) { g_par.kind = PAR_SEED; return; }
  const uint64_t *w; size_t n; uint64_t run, cursor;
  g_tc.lookups++;
  if (g_last.run && Size == g_last.size && (!Size || memcmp(Data, g_last.buf, Size) == 0)) {
    w = g_tr.w; n = g_tr.n; run = g_last.run; cursor = g_tr.cursor;
  } else {
    basalt_tentry *e = basalt_tc_find(basalt_hash_buf(Data, Size), Data, Size);
    if (!e) { g_tc.misses++; g_par.kind = PAR_MISS; return; }
    w = e->w; n = e->n; run = e->run; cursor = e->cursor;
  }
  g_par.w = basalt_grow_buf(g_par.w, &g_par.wcap, n, sizeof *g_par.w);
  memcpy(g_par.w, w, n * sizeof *w);
  g_par.n = n;
  g_par.buf = basalt_grow_buf(g_par.buf, &g_par.bcap, Size, 1);
  if (Size) memcpy(g_par.buf, Data, Size);
  g_par.size = Size;
  g_par.run = run; g_par.cursor = cursor;
  g_par.kind = PAR_OK;
}

/* Edit distance between the parent's and the child's sequences of drawn values (-1 if either is
   long enough to make it slow). */
static long basalt_draw_distance(const uint64_t *a, size_t na, const uint64_t *b, size_t nb) {
  if (na > 4000 || nb > 4000) return -1;
  static long *row; static size_t rowcap;
  row = basalt_grow_buf(row, &rowcap, nb + 1, sizeof *row);
  for (size_t j = 0; j <= nb; j++) row[j] = (long)j;
  for (size_t i = 1; i <= na; i++) {
    long diag = row[0];
    row[0] = (long)i;
    for (size_t j = 1; j <= nb; j++) {
      long up = row[j];
      long sub = diag + (a[4 * (i - 1) + 2] != b[4 * (j - 1) + 2]);
      long best = up + 1 < row[j - 1] + 1 ? up + 1 : row[j - 1] + 1;
      row[j] = sub < best ? sub : best;
      diag = up;
    }
  }
  return row[nb];
}

/* After a fuzz-mode run: log it against its parent, and keep its trace if it reached a new feature
   (or was a queued seed, whose features the random phase already counted). */
static void basalt_trace_after(const uint8_t *Data, size_t Size, size_t fresh) {
  g_tc.draws += g_tr.n / 4;
  int seeded = g_diag && g_par.kind == PAR_SEED;
  if (fresh || seeded) basalt_tc_put(Data, Size);
  if (!g_diag) return;
  size_t nc = g_tr.n / 4;
  switch (g_par.kind) {
  case PAR_OK: {
    size_t np = g_par.n / 4, k = 0;
    while (k < np && k < nc && g_par.w[4 * k] == g_tr.w[4 * k] && g_par.w[4 * k + 1] == g_tr.w[4 * k + 1]
           && g_par.w[4 * k + 2] == g_tr.w[4 * k + 2]) k++;
    size_t off = 0, lim = Size > g_par.size ? Size : g_par.size;
    while (off < lim && (off < Size ? Data[off] : 0) == (off < g_par.size ? g_par.buf[off] : 0)) off++;
    char cls = (k == np && k == nc) ? (off >= g_par.cursor ? 'a' : 'b') : 'v';
    long dist = cls == 'v' ? basalt_draw_distance(g_par.w, np, g_tr.w, nc) : 0;
    fprintf(stderr, "BASALT_M %llu %llu %c %zu %ld %d %zu %llu %zu %llu\n",
            (unsigned long long)g_run_idx, (unsigned long long)g_par.run, cls, k, dist, fresh ? 1 : 0,
            nc, (unsigned long long)g_tr.cursor, off, (unsigned long long)g_par.cursor);
    break;
  }
  case PAR_MISS: fprintf(stderr, "BASALT_M %llu - m 0 0 %d %zu %llu 0 0\n", (unsigned long long)g_run_idx,
                         fresh ? 1 : 0, nc, (unsigned long long)g_tr.cursor); break;
  case PAR_SEED: fprintf(stderr, "BASALT_M %llu - s 0 0 %d %zu %llu 0 0\n", (unsigned long long)g_run_idx,
                         fresh ? 1 : 0, nc, (unsigned long long)g_tr.cursor); break;
  default:       fprintf(stderr, "BASALT_M %llu - n 0 0 %d %zu %llu 0 0\n", (unsigned long long)g_run_idx,
                         fresh ? 1 : 0, nc, (unsigned long long)g_tr.cursor); break;
  }
  g_par.kind = PAR_NONE;
  g_last.buf = basalt_grow_buf(g_last.buf, &g_last.cap, Size, 1);
  if (Size) memcpy(g_last.buf, Data, Size);
  g_last.size = Size;
  g_last.run = g_run_idx;
}

static void basalt_trace_report(void) {
  if (!g_probe && !g_diag) return;
  fprintf(stderr, "[basalt] traces: %llu draws over %llu runs (%.1f per run); %zu cached, %.1f MB; "
          "%llu parent lookups, %llu missed\n",
          (unsigned long long)g_tc.draws, (unsigned long long)g_stats.runs,
          g_stats.runs ? (double)g_tc.draws / (double)g_stats.runs : 0.0, g_tc.n,
          (double)g_tc.bytes / 1e6, (unsigned long long)g_tc.lookups, (unsigned long long)g_tc.misses);
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
  g_run_idx++;
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
  size_t fresh = 0;
  if (g_hy.on || g_probe || g_diag) { size_t nf; fresh = basalt_hybrid_scan(&nf); }
  if (g_hy.on) {
    g_hy.total++;
    if (g_hy.started) basalt_phase_step(fresh);
  }
  if (g_probe || g_diag) basalt_trace_after(Data, Size, fresh);

  if (code == 1) {
    basalt_cov_dump();                                /* abort() skips this atexit handler too  */
    basalt_fuzz_report_stats();                       /* abort() skips the atexit handler      */
    basalt_trace_report();
    fflush(NULL);                                     /* the Lean side flushed its own handles */
    abort();                                          /* property failed → libFuzzer saves it */
  }
  return (code == 2) ? -1 : 0;    /* discard → not added to the corpus (LLVM >= 12; the legacy
                                     driver ignores the code) */
}

/* Called from Lean's `main` via @[extern]. Stores the closure and hands control to libFuzzer.
   Returns only if the campaign completes without a failure (a failure aborts the process). */
LEAN_EXPORT lean_object *basalt_fuzz_go(lean_object *run, lean_object *argv, uint8_t grow,
                                        uint32_t modes) {
  g_run = run;
  g_grow = grow;
  g_fill_random = (modes & 1) != 0;
  g_probe = (modes & 2) != 0;
  g_diag = (modes & 4) != 0;
  if (basalt_mix64(1) != 6238072747940578789ULL)
    basalt_fuzz_die("basalt_mix64 disagrees with Basalt.Fuzz.mix64");
  if ((g_probe || g_diag) && !g_hy.on) {
    /* The new-feature scan is the hybrid's; a plain campaign needs its maps too. */
    if (!basalt_have_counters()) basalt_fuzz_die("--trace-probe: no SanitizerCoverage counters");
    g_hy.ncntrs = (size_t)(__stop___sancov_cntrs - __start___sancov_cntrs);
    g_hy.seen = calloc(g_hy.ncntrs, 1);
    g_hy.fresh = calloc(g_hy.ncntrs, 1);
    g_hy.scratch = malloc(g_hy.ncntrs * sizeof *g_hy.scratch);
    if (!g_hy.seen || !g_hy.fresh || !g_hy.scratch) basalt_fuzz_die("out of memory for the coverage map");
  }
  atexit(basalt_trace_report);
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
