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
static uint64_t g_last_run_cursor;
LEAN_EXPORT lean_object *basalt_fuzz_note_deficit(uint32_t deficit, uint64_t seed, uint64_t cursor) {
  g_stats.runs++;
  g_last_run_seed = seed;
  g_last_run_cursor = cursor;
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
static size_t basalt_truncate(const uint8_t *Data, size_t Size);
static void *basalt_grow_buf(void *p, size_t *cap, size_t need, size_t elt);
static int g_choice;                   /* a choice-sequence campaign (`--backend=choice`)        */
static int g_ch_seeded;                /* the input now running is a queued hybrid seed          */
static int g_trunc;                    /* cut inputs to the bytes their run read (byte fuzzer)    */
static size_t basalt_choice_mutate(const uint8_t *Data, size_t Size, const uint8_t *Donor,
                                   size_t DSize, uint8_t *Out, size_t MaxSize, unsigned Seed);
static int g_cmp;                      /* `--cmp`: compared operands planted, as libFuzzer's CMP  */
static size_t basalt_cmp(uint8_t *Data, size_t Size, size_t MaxSize);
static inline int basalt_tracing(void) { return g_cmp; }
static void basalt_plant_find(const uint8_t *Data, size_t Size);
static void basalt_plant_report(void);
static void basalt_plant_check(void);

__attribute__((visibility("default")))
size_t LLVMFuzzerCustomMutator(uint8_t *Data, size_t Size, size_t MaxSize, unsigned Seed) {
  (void)Seed;
  size_t hybrid = basalt_hybrid_mutate(Data, Size, MaxSize);
  basalt_diag_parent(Data, Size, hybrid != 0);
  g_ch_seeded = hybrid != 0;
  if (hybrid) return hybrid;
  if (basalt_tracing()) basalt_plant_find(Data, Size);  /* before truncating: keyed by it */
  Size = basalt_truncate(Data, Size);
  if (g_choice) {
    static uint8_t *in; static size_t incap;
    in = basalt_grow_buf(in, &incap, Size ? Size : 1, 1);
    memcpy(in, Data, Size);
    return basalt_choice_mutate(in, Size, NULL, 0, Data, MaxSize, Seed);
  }
  if (g_cmp) {
    size_t planted = basalt_cmp(Data, Size, MaxSize);
    if (planted) return planted;
  }
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
  uint64_t  test;            /* its test in the phase (`g_hy.n` when it ran, from 1)              */
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
  int          dw;           /* the doubling-window exit (`--switch-rule=doubling`)               */
  uint64_t     dw_floor, dw_quiet, dw_base;  /* its first checkpoint, the finds that count as quiet, and
                                                the shortest phase of the no-`-runs` alternation */
  uint64_t     dw_next, dw_mark;  /* the next checkpoint, and the edges reached at the last one      */
  uint64_t     edges;        /* distinct edges reached (counters ever nonzero)                    */
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
    if (!g_hy.seen[i]) g_hy.edges++;
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
  sd->test = g_hy.n + 1;
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
  /* The doubling window: at tests floor/2, floor, 2·floor, …, a first random phase whose second half
     reached at most `dw_quiet` new edges has saturated. A path's first-time code (a lazily initialized
     constant, say) is a discovery when its path is first reached, as it should be, and then stops. */
  if (first && g_hy.dw && g_hy.n >= g_hy.dw_next) {
    uint64_t found = g_hy.edges - g_hy.dw_mark;
    if (g_hy.trace)
      fprintf(stderr, "[basalt] doubling: test %llu, %llu new edges since test %llu\n",
              (unsigned long long)g_hy.n, (unsigned long long)found,
              (unsigned long long)(g_hy.dw_next / 2));
    if (g_hy.n >= g_hy.dw_floor && found <= g_hy.dw_quiet) { basalt_phase_switch(); return; }
    g_hy.dw_mark = g_hy.edges;
    g_hy.dw_next *= 2;
  }
  /* Without `-runs` the window below has no horizon: it never closes when random makes fewer than
     `conf` finds, and closes at once when it makes more. The guarantee instead: no phase outlasts the
     campaign before it (at least `dw_base` tests), so the modes alternate in doubling phases and
     fuzzing gets about half of all tests. */
  if (g_hy.dw && !g_hy.budget) {
    uint64_t before = g_hy.total - g_hy.n, cap = before > g_hy.dw_base ? before : g_hy.dw_base;
    if (g_hy.n >= cap) basalt_phase_switch();
    return;
  }
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

/* Add the doubling-window exit to a hybrid campaign; called after `basalt_hybrid_config`. */
LEAN_EXPORT lean_object *basalt_hybrid_doubling(uint64_t floor, uint64_t quiet, uint64_t base) {
  g_hy.dw = 1;
  g_hy.dw_floor = floor ? floor : 1;
  g_hy.dw_quiet = quiet;
  g_hy.dw_base = base;
  g_hy.dw_next = g_hy.dw_floor > 1 ? g_hy.dw_floor / 2 : 1;
  return lean_io_result_mk_ok(lean_box(0));
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
  uint8_t  *rz, *bd;          /* a choice campaign's trace: realized records, and bounds          */
  size_t    rzn, bdn;
} basalt_tentry;

static struct { uint8_t *rz, *bd; size_t rzn, bdn, rzcap, bdcap; } g_ch;   /* the last run's        */

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
  size_t n = g_choice ? 0 : g_tr.n;
  e->w = malloc((n ? n : 1) * sizeof *e->w);
  e->buf = malloc(size ? size : 1);
  if (!e->w || !e->buf) basalt_fuzz_die("out of memory caching traces");
  memcpy(e->w, g_tr.w, n * sizeof *e->w);
  memcpy(e->buf, d, size);
  if (g_choice) {
    e->rz = malloc(g_ch.rzn ? g_ch.rzn : 1);
    e->bd = malloc(g_ch.bdn ? g_ch.bdn : 1);
    if (!e->rz || !e->bd) basalt_fuzz_die("out of memory caching traces");
    memcpy(e->rz, g_ch.rz, g_ch.rzn); memcpy(e->bd, g_ch.bd, g_ch.bdn);
    e->rzn = g_ch.rzn; e->bdn = g_ch.bdn;
  }
  e->key = key; e->n = n; e->size = size; e->cursor = g_tr.cursor; e->run = g_run_idx;
  g_tc.n++;
  g_tc.bytes += n * sizeof *e->w + size + sizeof *e + e->rzn + e->bdn;
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
/* Whether the run just finished may have become a corpus unit, so its trace is worth caching: it
   reached a new feature; or it was a queued hybrid seed, whose features the random phase already
   counted; or it is the smallest input yet for one of its features, which libFuzzer also admits. */
static uint32_t *g_smallest;           /* per feature, the size of the smallest input reaching it  */
static int basalt_may_be_unit(size_t Size, size_t fresh, size_t nf) {
  int smaller = 0;
  if (!g_smallest) {
    g_smallest = malloc(g_hy.ncntrs * 8 * sizeof *g_smallest);
    if (!g_smallest) basalt_fuzz_die("out of memory for the feature sizes");
    memset(g_smallest, 0xff, g_hy.ncntrs * 8 * sizeof *g_smallest);
  }
  for (size_t i = 0; i < nf; i++)
    if (Size < g_smallest[g_hy.scratch[i]]) { g_smallest[g_hy.scratch[i]] = (uint32_t)Size; smaller = 1; }
  return fresh || smaller || g_ch_seeded;
}

static void basalt_trace_after(const uint8_t *Data, size_t Size, size_t fresh, size_t nf) {
  g_tc.draws += g_tr.n / 4;
  int seeded = g_diag && g_par.kind == PAR_SEED;
  /* `--cmp` and truncation look up corpus units, so they keep every input libFuzzer may have saved;
     the probe and the mutation log keep new-feature runs only. */
  int lookup = basalt_tracing();
  if ((lookup || g_trunc) ? basalt_may_be_unit(Size, fresh, nf) : (fresh || seeded))
    basalt_tc_put(Data, Size);
  if (!g_diag) {
    if (!lookup && !g_trunc) return;
    g_ch_seeded = 0;
    g_last.buf = basalt_grow_buf(g_last.buf, &g_last.cap, Size ? Size : 1, 1);
    if (Size) memcpy(g_last.buf, Data, Size);
    g_last.size = Size;
    g_last.run = g_run_idx;
    return;
  }
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

/* Truncation, always on for the byte fuzzer: cut an input to the bytes its run read before mutating
   it, so no mutation is spent on bytes nothing reads. The run's cursor comes from the last run or,
   for a corpus unit, the cache (kept for every input that may be one). */
static uint64_t g_trunc_cut, g_trunc_bytes, g_trunc_miss;
static size_t basalt_truncate(const uint8_t *Data, size_t Size) {
  if (!g_trunc || (g_hy.on && g_hy.mode == BASALT_RANDOM)) return Size;
  uint64_t cursor;
  if (g_last.run && Size == g_last.size && (!Size || memcmp(Data, g_last.buf, Size) == 0))
    cursor = g_last_run_cursor;
  else {
    basalt_tentry *e = basalt_tc_find(basalt_hash_buf(Data, Size), Data, Size);
    if (!e) { g_trunc_miss++; return Size; }
    cursor = e->cursor;
  }
  if (cursor >= Size) return Size;
  if (cursor == 0) cursor = 1;
  g_trunc_cut++; g_trunc_bytes += Size - cursor;
  return (size_t)cursor;
}

static void basalt_trunc_after(const uint8_t *Data, size_t Size, size_t fresh, size_t nf) {
  g_tr.n = 0;
  g_tr.cursor = g_last_run_cursor;
  if (basalt_may_be_unit(Size, fresh, nf)) basalt_tc_put(Data, Size);
  g_ch_seeded = 0;
  g_last.buf = basalt_grow_buf(g_last.buf, &g_last.cap, Size ? Size : 1, 1);
  if (Size) memcpy(g_last.buf, Data, Size);
  g_last.size = Size;
  g_last.run = g_run_idx;
}

static void basalt_trace_report(void) {
  if (g_trunc)
    fprintf(stderr, "[basalt] truncate: %llu inputs cut, %.1f bytes each on average; %llu cursors "
            "unknown\n", (unsigned long long)g_trunc_cut,
            g_trunc_cut ? (double)g_trunc_bytes / (double)g_trunc_cut : 0.0,
            (unsigned long long)g_trunc_miss);
  basalt_plant_report();
  if (!g_probe && !g_diag && !basalt_tracing()) return;
  fprintf(stderr, "[basalt] traces: %llu draws over %llu runs (%.1f per run); %zu cached, %.1f MB; "
          "%llu parent lookups, %llu missed\n",
          (unsigned long long)g_tc.draws, (unsigned long long)g_stats.runs,
          g_stats.runs ? (double)g_tc.draws / (double)g_stats.runs : 0.0, g_tc.n,
          (double)g_tc.bytes / 1e6, (unsigned long long)g_tc.lookups, (unsigned long long)g_tc.misses);
}

/* ---------------------------------------------------------------------------------------------
   Choice-sequence campaigns (`--backend=choice`)

   The buffer is a sequence of records, a kind byte and an LEB128 value (`Basalt.Fuzz.ChoiceFuzz`).
   Each run hands back its realized records and its draws' bounds (`basalt_choice_note`); the mutator
   finds the trace of the input it is given — the last run's, or the cache's for a corpus unit — and
   edits the *realized* records, so the fill values a run drew become ordinary records the next edit
   keeps. Operators are chosen by a bandit rewarded by new features. DESIGN-choice-sequences.md §3
   gives the design; `BASALT_CHOICE_OPS` (a comma list of operator names) restricts the operators and
   `BASALT_CHOICE_BANDIT=0` makes the choice uniform.
   --------------------------------------------------------------------------------------------- */

LEAN_EXPORT lean_object *basalt_choice_note(b_lean_obj_arg rz, b_lean_obj_arg bd) {
  size_t rn = lean_sarray_size(rz), bn = lean_sarray_size(bd);
  g_ch.rz = basalt_grow_buf(g_ch.rz, &g_ch.rzcap, rn, 1);
  g_ch.bd = basalt_grow_buf(g_ch.bd, &g_ch.bdcap, bn, 1);
  memcpy(g_ch.rz, lean_sarray_cptr(rz), rn); g_ch.rzn = rn;
  memcpy(g_ch.bd, lean_sarray_cptr(bd), bn); g_ch.bdn = bn;
  return lean_box(0);
}

/* A record as the mutator sees it. A value or bound too wide for 64 bits is kept as its raw bytes
   and only ever copied. */
typedef struct {
  uint8_t kind, fill, wide, known;     /* `known`: the bounds came from a trace                    */
  uint64_t lo, hi, v;
  const uint8_t *raw; uint32_t rawlen; /* the record's bytes, kind included                       */
} crec;

typedef struct { crec *r; size_t n, cap; } crecs;

static int basalt_leb(const uint8_t *b, size_t n, size_t *i, uint64_t *out, int *wide) {
  uint64_t v = 0; int shift = 0; *wide = 0;
  while (*i < n) {
    uint8_t x = b[(*i)++];
    if (shift < 63 || (shift == 63 && (x & 0x7f) <= 1)) v |= (uint64_t)(x & 0x7f) << shift;
    else *wide = 1;
    shift += 7;
    if (x < 128) { *out = v; return 1; }
  }
  return 0;
}

static void crecs_push(crecs *a, crec r) {
  a->r = basalt_grow_buf(a->r, &a->cap, a->n + 1, sizeof *a->r);
  a->r[a->n++] = r;
}

/* Records of `rz`, with bounds from `bd` if given (`bd == NULL`: unknown). As `parseRecords`. */
static void basalt_parse(crecs *a, const uint8_t *rz, size_t rn, const uint8_t *bd, size_t bn) {
  a->n = 0;
  size_t i = 0, j = 0;
  while (i < rn) {
    size_t start = i;
    crec r = {0};
    r.kind = rz[i++];
    if (r.kind != 1) break;
    int wide;
    if (!basalt_leb(rz, rn, &i, &r.v, &wide)) break;
    r.wide = (uint8_t)wide;
    r.raw = rz + start; r.rawlen = (uint32_t)(i - start);
    r.lo = 0; r.hi = UINT64_MAX;
    if (bd && j < bn) {
      int w1 = 0, w2 = 0;
      r.fill = bd[j++] & 1;
      if (basalt_leb(bd, bn, &j, &r.lo, &w1) && basalt_leb(bd, bn, &j, &r.hi, &w2)) {
        r.known = 1;
        if (w1 || w2) r.wide = 1;
      }
    }
    crecs_push(a, r);
  }
}

static size_t basalt_put_leb(uint8_t *o, size_t cap, size_t at, uint64_t v) {
  do {
    if (at >= cap) return SIZE_MAX;
    uint8_t x = v & 0x7f; v >>= 7;
    o[at++] = v ? (uint8_t)(x | 0x80) : x;
  } while (v);
  return at;
}

/* Encode records into `o`, stopping at the last record that fits. */
static size_t basalt_encode(const crecs *a, uint8_t *o, size_t cap) {
  size_t at = 0;
  for (size_t k = 0; k < a->n; k++) {
    const crec *r = &a->r[k];
    size_t next;
    if (r->wide) {
      if (at + r->rawlen > cap) break;
      memcpy(o + at, r->raw, r->rawlen); next = at + r->rawlen;
    } else {
      if (at >= cap) break;
      o[at] = r->kind;
      next = basalt_put_leb(o, cap, at + 1, r->v);
      if (next == SIZE_MAX) break;
    }
    at = next;
  }
  return at;
}

static uint64_t g_crng = 0x853c49e6748fea9bULL;
static inline uint64_t crand(void) {
  g_crng += 0x9e3779b97f4a7c15ULL;
  return basalt_mix64(g_crng);
}
static inline uint64_t crand_below(uint64_t n) { return n ? crand() % n : 0; }
/* A uniform value in [lo, hi]. */
static inline uint64_t crand_in(uint64_t lo, uint64_t hi) {
  uint64_t span = hi - lo;
  return span == UINT64_MAX ? crand() : lo + crand_below(span + 1);
}
/* A length: 1 with probability 1/2, 2 with 1/4, … */
static inline size_t crand_geom(size_t max) {
  size_t k = 1;
  while (k < max && (crand() & 1)) k++;
  return k;
}

/* Comparison operands, from the instrumented code's `trace-cmp` hooks (linked with `--wrap`, so the
   runtime's own hooks still run). A Lean scalar arrives tagged (`2n+1`), so an odd operand is also
   offered untagged. A direct-mapped table: recent operands evict colliding older ones. */
#define BASALT_POOL 1024
static uint64_t g_pool[BASALT_POOL];
static uint8_t  g_pool_used[BASALT_POOL];
static size_t   g_pool_n;
static inline void basalt_pool_add(uint64_t x) {
  size_t i = basalt_mix64(x) & (BASALT_POOL - 1);
  if (!g_pool_used[i]) { g_pool_used[i] = 1; g_pool_n++; }
  g_pool[i] = x;
}
/* `--cmp`'s comparison pairs, as libFuzzer's tables of recent compares keep them: a slot per
   `a ^ b`, later pairs evicting earlier ones. Lean scalars arrive tagged, so a pair of odd operands
   is also kept untagged. */
#define BASALT_PAIRS 1024
static struct { uint64_t a[BASALT_PAIRS], b[BASALT_PAIRS]; uint8_t used[BASALT_PAIRS]; } g_pairs;
static struct { uint64_t planted, matched, lits, kept; size_t npairs; } g_cm;
static inline void basalt_pair_add(uint64_t a, uint64_t b) {
  if (a == b) return;
  size_t i = basalt_mix64(a ^ b) & (BASALT_PAIRS - 1);
  if (!g_pairs.used[i]) { g_pairs.used[i] = 1; g_cm.npairs++; }
  g_pairs.a[i] = a; g_pairs.b[i] = b;
}
static inline void basalt_pool_cmp(uint64_t a, uint64_t b, int konst) {
  if (g_cmp) {
    basalt_pair_add(a, b);
    if ((a & 1) && (b & 1)) basalt_pair_add(a >> 1, b >> 1);
  }
  if (!g_choice) return;
  if (a & 1) basalt_pool_add(a >> 1);
  if (!konst && (b & 1)) basalt_pool_add(b >> 1);
  basalt_pool_add(a);
  if (!konst) basalt_pool_add(b);
}
/* The targets' own literals (`harvested_literals%`), offered alongside the comparison operands. */
static uint64_t *g_lits;
static size_t g_lits_n, g_lits_cap;
LEAN_EXPORT lean_object *basalt_choice_literal(uint64_t n) {
  g_lits = basalt_grow_buf(g_lits, &g_lits_cap, g_lits_n + 1, sizeof *g_lits);
  g_lits[g_lits_n++] = n;
  return lean_box(0);
}

#ifdef BASALT_CMP_WRAP
extern void __real___sanitizer_cov_trace_cmp8(uint64_t, uint64_t);
extern void __real___sanitizer_cov_trace_const_cmp8(uint64_t, uint64_t);
extern void __real___sanitizer_cov_trace_cmp4(uint32_t, uint32_t);
extern void __real___sanitizer_cov_trace_const_cmp4(uint32_t, uint32_t);
void __wrap___sanitizer_cov_trace_cmp8(uint64_t a, uint64_t b) {
  basalt_pool_cmp(a, b, 0); __real___sanitizer_cov_trace_cmp8(a, b);
}
void __wrap___sanitizer_cov_trace_const_cmp8(uint64_t a, uint64_t b) {
  basalt_pool_cmp(a, b, 1); __real___sanitizer_cov_trace_const_cmp8(a, b);
}
void __wrap___sanitizer_cov_trace_cmp4(uint32_t a, uint32_t b) {
  basalt_pool_cmp(a, b, 0); __real___sanitizer_cov_trace_cmp4(a, b);
}
void __wrap___sanitizer_cov_trace_const_cmp4(uint32_t a, uint32_t b) {
  basalt_pool_cmp(a, b, 1); __real___sanitizer_cov_trace_const_cmp4(a, b);
}
#endif

/* ---------------------------------------------------------------------------------------------
   Recorded draws, for writing a value into one (`--cmp`)

   Under `--cmp` the Lean side records every fuzz-mode run's draws (`lo`, `hi`, value, and the cursor
   where the draw's bytes start), as the probe does, and the cache keeps the traces of inputs that may
   be corpus units. Writing `v` into a draw overwrites exactly its `bytesFor (hi - lo + 1)` bytes with
   `v - lo`, big-endian, which `drawStep` decodes back to `v`; the next run checks that it does.
   --------------------------------------------------------------------------------------------- */

static struct {
  uint64_t miss, ok, bad, gone;
  const uint64_t *w; size_t n;
  int pending; uint64_t at, v;           /* the plant the next run should decode             */
} g_pl;

static void basalt_plant_report(void) {
  if (!g_cmp) return;
  fprintf(stderr, "[basalt] cmp: %llu planted (%llu where the compared value was, %llu from "
          "literals, %llu kept); %zu pairs, %zu literals; %llu inputs with no trace; next run "
          "decoded %llu as planted, %llu otherwise, %llu never reached the draw\n",
          (unsigned long long)g_cm.planted, (unsigned long long)g_cm.matched,
          (unsigned long long)g_cm.lits, (unsigned long long)g_cm.kept, g_cm.npairs, g_lits_n,
          (unsigned long long)g_pl.miss, (unsigned long long)g_pl.ok, (unsigned long long)g_pl.bad,
          (unsigned long long)g_pl.gone);
}

/* After a run: did the draw a plant just wrote decode to the planted value? A changed earlier draw
   can move the control flow off it (`gone`), but a draw starting at the offset must hold the value. */
static void basalt_plant_check(void) {
  if (!g_pl.pending) return;
  g_pl.pending = 0;
  for (size_t d = 0; d < g_tr.n / 4; d++)
    if (g_tr.w[4 * d + 3] == g_pl.at) {
      if (g_tr.w[4 * d + 2] == g_pl.v) g_pl.ok++; else g_pl.bad++;
      return;
    }
  g_pl.gone++;
}

/* `Data`'s trace, into `g_pl`: the last run's, or the cache's (none: `g_pl.w == NULL`). */
static void basalt_plant_find(const uint8_t *Data, size_t Size) {
  g_pl.w = NULL; g_pl.n = 0;
  if (g_hy.on && g_hy.mode == BASALT_RANDOM) return;
  if (g_last.run && Size == g_last.size && (!Size || memcmp(Data, g_last.buf, Size) == 0)) {
    g_pl.w = g_tr.w; g_pl.n = g_tr.n;
    return;
  }
  basalt_tentry *e = basalt_tc_find(basalt_hash_buf(Data, Size), Data, Size);
  if (e) { g_pl.w = e->w; g_pl.n = e->n; }
}

/* `Basalt.Fuzz.bytesFor (hi - lo + 1)`. */
static size_t basalt_draw_width(uint64_t lo, uint64_t hi) {
  uint64_t span = hi - lo;               /* range - 1                                              */
  size_t bits = 0;
  while (bits < 64 && (span >> bits)) bits++;
  return (bits + 7) / 8;
}

/* ---------------------------------------------------------------------------------------------
   `--cmp`: libFuzzer's `Mutate_AddWordFromTORC` at the draw level

   One more mutator beside libFuzzer's thirteen (1/14 of the custom mutator's calls). It takes a
   comparison pair `(A, B)` and, in a random direction, finds a recorded draw whose *decoded* value is
   `A` and writes `B + d` there, `d` in {-1, 0, +1} as libFuzzer's `Arg + Rand(-1, 1)`; with no such
   draw, any draw whose range admits it, as libFuzzer falls back to a random position. A harvested
   literal is an unpaired constant (Lean's `Nat` compares never reach the hook) and goes the second
   way. A constant whose plant reached new coverage is kept, and a third of the picks reuse one, as
   libFuzzer's persistent auto-dictionary does.
   --------------------------------------------------------------------------------------------- */

#define BASALT_KEPT 256
static struct { uint64_t v[BASALT_KEPT]; size_t n, next; uint64_t pending; int has; } g_kept;

/* Write `v` into draw `d` of the trace in `g_pl`; the new size, or 0 if it does not fit. */
static size_t basalt_write_draw(uint8_t *Data, size_t Size, size_t MaxSize, size_t d, uint64_t v) {
  const uint64_t *w = g_pl.w;
  uint64_t lo = w[4 * d], hi = w[4 * d + 1], at = w[4 * d + 3];
  if (hi < lo || v < lo || v > hi || v == w[4 * d + 2]) return 0;
  size_t width = basalt_draw_width(lo, hi);
  if (at + width > MaxSize) return 0;
  if (at + width > Size) { memset(Data + Size, 0, at + width - Size); Size = at + width; }
  uint64_t raw = v - lo;
  for (size_t k = 0; k < width; k++) Data[at + width - 1 - k] = (uint8_t)(raw >> (8 * k));
  g_pl.pending = 1; g_pl.at = at; g_pl.v = v;
  g_kept.pending = v; g_kept.has = 1;
  g_cm.planted++;
  return Size;
}

static size_t basalt_cmp(uint8_t *Data, size_t Size, size_t MaxSize) {
  if (g_hy.on && g_hy.mode == BASALT_RANDOM) return 0;
  if (crand_below(14)) return 0;
  if (!g_pl.w) { g_pl.miss++; return 0; }
  size_t nd = g_pl.n / 4;
  if (!nd) return 0;
  int64_t dl = (int64_t)crand_below(3) - 1;
  uint64_t want, from = 0;
  int paired = 0;
  uint64_t r = crand_below(3);
  if (r == 0 && g_kept.n) want = g_kept.v[crand_below(g_kept.n)];
  else if ((r == 1 || !g_lits_n) && g_cm.npairs) {
    size_t i = crand_below(BASALT_PAIRS);
    while (!g_pairs.used[i]) i = (i + 1) & (BASALT_PAIRS - 1);
    int flip = crand() & 1;
    from = flip ? g_pairs.b[i] : g_pairs.a[i];
    want = flip ? g_pairs.a[i] : g_pairs.b[i];
    paired = 1;
  } else if (g_lits_n) { want = g_lits[crand_below(g_lits_n)]; g_cm.lits++; }
  else return 0;
  want += (uint64_t)dl;
  if (paired) {                           /* where the compared value was, up to 8 such draws     */
    size_t pos[8], np = 0;
    size_t start = crand_below(nd);
    for (size_t q = 0; q < nd && np < 8; q++) {
      size_t d = (start + q) % nd;
      if (g_pl.w[4 * d + 2] == from) pos[np++] = d;
    }
    if (np) {
      size_t got = basalt_write_draw(Data, Size, MaxSize, pos[crand_below(np)], want);
      if (got) { g_cm.matched++; return got; }
    }
  }
  for (int t = 0; t < 8; t++) {           /* else any draw whose range admits it                  */
    size_t got = basalt_write_draw(Data, Size, MaxSize, crand_below(nd), want);
    if (got) return got;
  }
  return 0;
}

/* After a run: a plant that reached new coverage is kept for reuse. */
static void basalt_cmp_after(size_t fresh) {
  if (!g_kept.has) return;
  g_kept.has = 0;
  if (!fresh) return;
  for (size_t i = 0; i < g_kept.n; i++) if (g_kept.v[i] == g_kept.pending) return;
  g_kept.v[g_kept.next] = g_kept.pending;
  g_kept.next = (g_kept.next + 1) % BASALT_KEPT;
  if (g_kept.n < BASALT_KEPT) g_kept.n++;
  g_cm.kept++;
}

enum { OP_RAND, OP_DELTA, OP_BOUND, OP_BITS, OP_CONST, OP_TRUNC, OP_RANDRUN, OP_DELETE, OP_DUP,
       OP_HAVOC, OP_SPLICE, OP_INSERT, OP_CROSS, OP_N };
static const char *g_op_name[OP_N] = {"rand", "delta", "bound", "bits", "const", "trunc", "randrun",
                                      "delete", "dup", "havoc", "splice", "insert", "cross"};
static struct {
  int on[OP_N], bandit, init;
  uint64_t n[OP_N], wins[OP_N], fails[OP_N];
  int pending;                       /* the operator that made the input now running, or -1       */
  uint64_t misses, lookups, mutations, noops;
} g_cops;

static void basalt_cops_init(void) {
  g_cops.init = 1;
  g_cops.pending = -1;
  const char *ops = getenv("BASALT_CHOICE_OPS");
  for (int i = 0; i < OP_N; i++) g_cops.on[i] = ops == NULL;
  if (ops) {
    char buf[512]; snprintf(buf, sizeof buf, "%s", ops);
    for (char *t = strtok(buf, ","); t; t = strtok(NULL, ","))
      for (int i = 0; i < OP_N; i++) if (!strcmp(t, g_op_name[i])) g_cops.on[i] = 1;
  }
  const char *b = getenv("BASALT_CHOICE_BANDIT");
  g_cops.bandit = !(b && !strcmp(b, "0"));
}

/* Pick an operator: in proportion to its smoothed success rate, with a tenth of the picks uniform so
   no operator starves. The prior is one win in 100, and two for the destructive operators: on Cedar
   the mutations that reached new coverage were the ones that moved furthest from their parent
   (DESIGN-choice-sequences.md, Phase 0.1). */
static int basalt_pick_op(int have_donor, int know_bounds) {
  double w[OP_N], tot = 0;
  for (int i = 0; i < OP_N; i++) {
    int ok = g_cops.on[i] && (have_donor || i < OP_SPLICE) &&
             (know_bounds || i == OP_TRUNC || i == OP_DELETE || i == OP_DUP || i >= OP_SPLICE);
    double prior = (i == OP_TRUNC || i == OP_RANDRUN || i == OP_DELETE || i == OP_DUP ||
                    i == OP_HAVOC) ? 2.0 : 1.0;
    w[i] = ok ? (g_cops.bandit ? (g_cops.wins[i] + prior) / (g_cops.n[i] + 100.0) : 1.0) : 0;
    tot += w[i];
  }
  if (tot == 0) return OP_TRUNC;
  int uniform = g_cops.bandit && crand_below(10) == 0;
  if (uniform) {
    int k = 0, cand[OP_N];
    for (int i = 0; i < OP_N; i++) if (w[i] > 0) cand[k++] = i;
    return cand[crand_below(k)];
  }
  double x = (double)(crand() >> 11) / 9007199254740992.0 * tot;
  for (int i = 0; i < OP_N; i++) { if (x < w[i]) return i; x -= w[i]; }
  return OP_TRUNC;
}

/* A record whose value an operator can change, or -1. */
static long basalt_pick_value(const crecs *a) {
  if (!a->n) return -1;
  for (int t = 0; t < 16; t++) {
    size_t k = crand_below(a->n);
    if (!a->r[k].wide && a->r[k].known && a->r[k].hi > a->r[k].lo) return (long)k;
  }
  for (size_t k = 0; k < a->n; k++)
    if (!a->r[k].wide && a->r[k].known && a->r[k].hi > a->r[k].lo) return (long)k;
  return -1;
}

static int basalt_set(crec *r, uint64_t v) {
  if (v == r->v) return 0;
  r->v = v; r->fill = 0;
  return 1;
}

static int basalt_value_op(crecs *a, int op);

/* One operator on `a`, using `d` as the donor where it needs one. Returns whether it changed `a`. */
static crecs g_tmp;
static int basalt_apply_op(crecs *a, const crecs *d, int op) {
  size_t n = a->n;
  switch (op) {
  case OP_RAND: case OP_DELTA: case OP_BOUND: case OP_BITS: case OP_CONST:
    return basalt_value_op(a, op);
  case OP_TRUNC: {                       /* keep a prefix; the rest is drawn afresh                */
    if (!n) return 0;
    a->n = crand_below(n);
    return 1;
  }
  case OP_RANDRUN: {                     /* redraw a run of values within their bounds             */
    if (!n) return 0;
    size_t k = crand_below(n), m = crand_geom(n - k), changed = 0;
    for (size_t i = k; i < k + m; i++) {
      crec *r = &a->r[i];
      if (r->wide || !r->known) continue;
      changed |= basalt_set(r, crand_in(r->lo, r->hi));
    }
    return changed != 0;
  }
  case OP_DELETE: {                      /* drop a run of records; what follows shifts up          */
    if (!n) return 0;
    size_t k = crand_below(n), m = crand_geom(n - k);
    memmove(a->r + k, a->r + k + m, (n - k - m) * sizeof *a->r);
    a->n -= m;
    return 1;
  }
  case OP_DUP: {                         /* repeat a run of records after itself                   */
    if (!n) return 0;
    size_t k = crand_below(n), m = crand_geom(n - k);
    g_tmp.n = 0;
    for (size_t i = 0; i < k + m; i++) crecs_push(&g_tmp, a->r[i]);
    for (size_t i = k; i < n; i++) crecs_push(&g_tmp, a->r[i]);
    a->n = 0;
    for (size_t i = 0; i < g_tmp.n; i++) crecs_push(a, g_tmp.r[i]);
    return 1;
  }
  case OP_HAVOC: {                       /* several of the above at once                           */
    int k = 2 + (int)crand_below(5), changed = 0;
    for (int i = 0; i < k; i++) {
      static const int sub[] = {OP_RAND, OP_DELTA, OP_BOUND, OP_RANDRUN, OP_DELETE, OP_DUP};
      changed |= basalt_apply_op(a, d, sub[crand_below(6)]);
    }
    return changed;
  }
  case OP_SPLICE: {                      /* overwrite a run with a donor's, value by value, where
                                            the donor's values are permitted by these bounds       */
    if (!n || !d->n) return 0;
    for (int t = 0; t < 8; t++) {
      size_t i = crand_below(n), j = crand_below(d->n);
      size_t m = crand_geom(n - i < d->n - j ? n - i : d->n - j);
      int fits = 1, diff = 0;
      for (size_t q = 0; q < m && fits; q++) {
        const crec *x = &a->r[i + q], *y = &d->r[j + q];
        if (y->wide || x->wide || (x->known && (y->v < x->lo || y->v > x->hi))) fits = 0;
        diff |= x->v != y->v;
      }
      if (!fits || !diff) continue;
      for (size_t q = 0; q < m; q++) { a->r[i + q].v = d->r[j + q].v; a->r[i + q].fill = 0; }
      return 1;
    }
    return 0;
  }
  case OP_INSERT: {                      /* insert a run of a donor's records                      */
    if (!d->n) return 0;
    size_t i = crand_below(n + 1), j = crand_below(d->n), m = crand_geom(d->n - j);
    g_tmp.n = 0;
    for (size_t q = 0; q < i; q++) crecs_push(&g_tmp, a->r[q]);
    for (size_t q = 0; q < m; q++) crecs_push(&g_tmp, d->r[j + q]);
    for (size_t q = i; q < n; q++) crecs_push(&g_tmp, a->r[q]);
    a->n = 0;
    for (size_t q = 0; q < g_tmp.n; q++) crecs_push(a, g_tmp.r[q]);
    return 1;
  }
  case OP_CROSS: {                       /* this input's prefix, then a donor's suffix             */
    if (!d->n) return 0;
    size_t i = crand_below(n + 1), j = crand_below(d->n);
    a->n = i;
    for (size_t q = j; q < d->n; q++) crecs_push(a, d->r[q]);
    return 1;
  }
  }
  return 0;
}

static int basalt_value_op(crecs *a, int op) {
  long k = basalt_pick_value(a);
  if (k < 0) return 0;
  crec *r = &a->r[k];
  uint64_t lo = r->lo, hi = r->hi, span = hi - lo;
  switch (op) {
  case OP_RAND:
    for (int t = 0; t < 4; t++) if (basalt_set(r, crand_in(lo, hi))) return 1;
    return 0;
  case OP_DELTA: {
    uint64_t d = 1;
    while (d < span && (crand() & 1)) d <<= 1;
    d = 1 + crand_below(d);
    uint64_t v = r->v;
    if (crand() & 1) v = (hi - v < d) ? hi : v + d;
    else v = (v - lo < d) ? lo : v - d;
    return basalt_set(r, v);
  }
  case OP_BOUND: {
    uint64_t c[5] = {lo, hi, lo + 1, hi - 1, 0};
    for (int t = 0; t < 4; t++) {
      uint64_t v = c[crand_below(5)];
      if (v >= lo && v <= hi && basalt_set(r, v)) return 1;
    }
    return 0;
  }
  case OP_BITS: {
    int bits = 0;
    while (bits < 64 && (span >> bits)) bits++;
    uint64_t off = (r->v - lo) ^ (1ULL << crand_below(bits ? bits : 1));
    if (off > span) off %= span + 1;
    return basalt_set(r, lo + off);
  }
  case OP_CONST: {
    if (g_lits_n && (!g_pool_n || (crand() & 1))) {   /* a literal, half the time            */
      size_t start = crand_below(g_lits_n);
      for (size_t q = 0; q < g_lits_n; q++) {
        uint64_t c = g_lits[(start + q) % g_lits_n];
        if (c >= lo && c <= hi && c != r->v) { r->v = c; r->fill = 0; return 1; }
      }
    }
    if (!g_pool_n) return 0;
    size_t start = crand_below(BASALT_POOL);
    for (size_t q = 0; q < BASALT_POOL; q++) {
      size_t i = (start + q) & (BASALT_POOL - 1);
      if (g_pool_used[i] && g_pool[i] >= lo && g_pool[i] <= hi && g_pool[i] != r->v) {
        r->v = g_pool[i]; r->fill = 0;
        return 1;
      }
    }
    return 0;
  }
  }
  return 0;
}

static crecs g_cw, g_cd;

/* The trace of `Data`: the last run's, or the cache's. 0 if unknown. */
static int basalt_choice_trace(const uint8_t *Data, size_t Size, const uint8_t **rz, size_t *rn,
                               const uint8_t **bd, size_t *bn) {
  if (g_last.run && Size == g_last.size && (!Size || memcmp(Data, g_last.buf, Size) == 0)) {
    *rz = g_ch.rz; *rn = g_ch.rzn; *bd = g_ch.bd; *bn = g_ch.bdn;
    return 1;
  }
  basalt_tentry *e = basalt_tc_find(basalt_hash_buf(Data, Size), Data, Size);
  if (!e) return 0;
  *rz = e->rz; *rn = e->rzn; *bd = e->bd; *bn = e->bdn;
  return 1;
}

/* Load a donor's records into `g_cd`: `Donor` if given, else a random cached input. */
static int basalt_load_donor(const uint8_t *Donor, size_t DSize) {
  const uint8_t *rz, *bd; size_t rn, bn;
  if (Donor) {
    if (basalt_choice_trace(Donor, DSize, &rz, &rn, &bd, &bn)) basalt_parse(&g_cd, rz, rn, bd, bn);
    else basalt_parse(&g_cd, Donor, DSize, NULL, 0);
    return g_cd.n > 0;
  }
  if (!g_tc.n) return 0;
  for (int t = 0; t < 8; t++) {
    basalt_tentry *e = &g_tc.e[crand_below(g_tc.cap)];
    if (e->key) { basalt_parse(&g_cd, e->rz, e->rzn, e->bd, e->bdn); return g_cd.n > 0; }
  }
  return 0;
}

/* The choice mutator: materialize `Data`'s realized records, apply one operator, write `Out`. */
static size_t basalt_choice_mutate(const uint8_t *Data, size_t Size, const uint8_t *Donor,
                                   size_t DSize, uint8_t *Out, size_t MaxSize, unsigned Seed) {
  if (!g_cops.init) basalt_cops_init();
  g_crng ^= (uint64_t)Seed << 32;
  const uint8_t *rz, *bd; size_t rn, bn;
  g_cops.lookups++;
  int known = basalt_choice_trace(Data, Size, &rz, &rn, &bd, &bn);
  if (known) basalt_parse(&g_cw, rz, rn, bd, bn);
  else { g_cops.misses++; basalt_parse(&g_cw, Data, Size, NULL, 0); }
  int have_donor = basalt_load_donor(Donor, DSize);
  for (int t = 0; t < 8; t++) {
    int op = basalt_pick_op(have_donor, known);
    crecs save = g_cw;                   /* a failed operator must leave `g_cw` as it was          */
    static crecs back;
    back.n = 0;
    for (size_t i = 0; i < save.n; i++) crecs_push(&back, save.r[i]);
    if (basalt_apply_op(&g_cw, &g_cd, op)) {
      size_t n = basalt_encode(&g_cw, Out, MaxSize);
      if (n == 0 && Size == 0) { g_cops.fails[op]++; continue; }
      g_cops.pending = op;
      g_cops.mutations++;
      if (n) return n;
      Out[0] = 0;                        /* an empty record list as a lone 0 byte, which parses to
                                            no records: libFuzzer discards a mutation of size 0   */
      return 1;
    }
    g_cops.fails[op]++;
    g_cw.n = 0;
    for (size_t i = 0; i < back.n; i++) crecs_push(&g_cw, back.r[i]);
  }
  g_cops.noops++;
  for (size_t i = 0; i < 8 && i < MaxSize; i++) Out[i] = (uint8_t)crand();
  g_cops.pending = -1;
  return MaxSize < 8 ? MaxSize : 8;
}

/* After a choice run: reward the operator that made it, keep the trace of a run that reached a new
   feature (or was a queued seed, whose features the random phase already counted), and remember the
   run as the last one. */
static uint32_t *g_smallest;           /* per feature, the size of the smallest input reaching it  */
static void basalt_choice_after(const uint8_t *Data, size_t Size, size_t fresh, size_t nf) {
  /* libFuzzer also admits an input that reaches an existing unit's features in fewer bytes, so a
     run that is the smallest yet for any of its features may be a corpus unit too. */
  int smaller = 0;
  if (!g_smallest) {
    g_smallest = malloc(g_hy.ncntrs * 8 * sizeof *g_smallest);
    if (!g_smallest) basalt_fuzz_die("out of memory for the choice campaign's feature sizes");
    memset(g_smallest, 0xff, g_hy.ncntrs * 8 * sizeof *g_smallest);
  }
  for (size_t i = 0; i < nf; i++)
    if (Size < g_smallest[g_hy.scratch[i]]) { g_smallest[g_hy.scratch[i]] = (uint32_t)Size; smaller = 1; }
  if (fresh || smaller || g_ch_seeded) basalt_tc_put(Data, Size);
  g_ch_seeded = 0;
  g_last.buf = basalt_grow_buf(g_last.buf, &g_last.cap, Size ? Size : 1, 1);
  if (Size) memcpy(g_last.buf, Data, Size);
  g_last.size = Size;
  g_last.run = g_run_idx;
  if (g_cops.pending >= 0) {
    g_cops.n[g_cops.pending]++;
    if (fresh) g_cops.wins[g_cops.pending]++;
  }
  g_cops.pending = -1;
}

static void basalt_choice_report(void) {
  if (!g_choice) return;
  fprintf(stderr, "[basalt] choice: %llu mutations, %llu trace lookups, %llu missed, %llu no-ops; "
          "%zu traces cached (%.1f MB); %zu pool constants, %zu literals\n",
          (unsigned long long)g_cops.mutations, (unsigned long long)g_cops.lookups,
          (unsigned long long)g_cops.misses, (unsigned long long)g_cops.noops, g_tc.n,
          (double)g_tc.bytes / 1e6, g_pool_n, g_lits_n);
  for (int i = 0; i < OP_N; i++)
    if (g_cops.n[i] || g_cops.fails[i])
      fprintf(stderr, "[basalt] op %-8s runs %10llu  new-feature %8llu (%.4f%%)  failed %llu\n",
              g_op_name[i], (unsigned long long)g_cops.n[i], (unsigned long long)g_cops.wins[i],
              g_cops.n[i] ? 100.0 * (double)g_cops.wins[i] / (double)g_cops.n[i] : 0.0,
              (unsigned long long)g_cops.fails[i]);
}

__attribute__((visibility("default")))
size_t LLVMFuzzerCustomCrossOver(const uint8_t *Data1, size_t Size1, const uint8_t *Data2,
                                 size_t Size2, uint8_t *Out, size_t MaxOutSize, unsigned Seed) {
  if (!g_choice) return 0;               /* not ours: libFuzzer picks its other mutator instead    */
  size_t n = Size1 < MaxOutSize ? Size1 : MaxOutSize;
  memcpy(Out, Data1, n);
  size_t hybrid = basalt_hybrid_mutate(Out, n, MaxOutSize);
  g_ch_seeded = hybrid != 0;
  if (hybrid) { g_cops.pending = -1; return hybrid; }
  return basalt_choice_mutate(Data1, Size1, Data2, Size2, Out, MaxOutSize, Seed);
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
  size_t fresh = 0, nf = 0;
  if (g_hy.on || g_probe || g_diag || g_choice || g_trunc || basalt_tracing()) fresh = basalt_hybrid_scan(&nf);
  if (g_hy.on) {
    g_hy.total++;
    if (g_hy.started) basalt_phase_step(fresh);
  }
  if (basalt_tracing()) basalt_plant_check();
  if (g_cmp) basalt_cmp_after(fresh);
  if (g_choice) basalt_choice_after(Data, Size, fresh, nf);
  else if (g_probe || g_diag || basalt_tracing()) basalt_trace_after(Data, Size, fresh, nf);
  else if (g_trunc) basalt_trunc_after(Data, Size, fresh, nf);

  if (code == 1) {
    basalt_cov_dump();                                /* abort() skips this atexit handler too  */
    basalt_fuzz_report_stats();                       /* abort() skips the atexit handler      */
    basalt_trace_report();
    basalt_choice_report();
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
  g_choice = (modes & 8) != 0;
  g_trunc = !g_choice;                /* the byte fuzzer always truncates; choice inputs are records */
  g_cmp = (modes & 128) != 0;
  if (basalt_mix64(1) != 6238072747940578789ULL)
    basalt_fuzz_die("basalt_mix64 disagrees with Basalt.Fuzz.mix64");
  if ((g_probe || g_diag || g_choice || g_trunc || basalt_tracing()) && !g_hy.on) {
    /* The new-feature scan is the hybrid's; a plain campaign needs its maps too. */
    if (!basalt_have_counters()) basalt_fuzz_die("--trace-probe: no SanitizerCoverage counters");
    g_hy.ncntrs = (size_t)(__stop___sancov_cntrs - __start___sancov_cntrs);
    g_hy.seen = calloc(g_hy.ncntrs, 1);
    g_hy.fresh = calloc(g_hy.ncntrs, 1);
    g_hy.scratch = malloc(g_hy.ncntrs * sizeof *g_hy.scratch);
    if (!g_hy.seen || !g_hy.fresh || !g_hy.scratch) basalt_fuzz_die("out of memory for the coverage map");
  }
  atexit(basalt_trace_report);
  atexit(basalt_choice_report);
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
