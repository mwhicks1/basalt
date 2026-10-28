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
   Truncation (`--truncate`)

   Before libFuzzer mutates the input it has just run, the input is cut to the bytes its run read,
   so that the mutation lands on bytes the run used. The cut input runs exactly as before, since
   `readByte` reads `0` past the end. Only the input just run is cut: an input libFuzzer picks from
   its corpus to start a mutation chain has no run at hand to say how much of it was read.
   --------------------------------------------------------------------------------------------- */

static int g_trunc;           /* `--truncate`                                                    */

static struct {
  uint64_t runs;
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

/* After a run, under `--truncate`: remember it as the last run. */
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

/* The campaign's buffer statistics, on stderr. Called from two disjoint exits — `atexit` for the
   `-runs`-exhausted path, and the failure path below, which `abort()`s past `atexit` handlers.
   Printed from C rather than returned to Lean because a `String`-returning extern is the one shape
   of this bridge that gets the `BaseIO` ABI wrong silently. */
static void basalt_fuzz_report_stats(void) {
  if (!g_stats.runs) return;
  fprintf(stderr, "[basalt] runs %llu, starved %llu (max deficit %llu B)",
          (unsigned long long)g_stats.runs, (unsigned long long)g_stats.starved,
          (unsigned long long)g_stats.max_deficit);
  if (g_trunc)
    fprintf(stderr, "; truncated %llu inputs, %.1f bytes each on average",
            (unsigned long long)g_stats.cut,
            g_stats.cut ? (double)g_stats.cut_bytes / (double)g_stats.cut : 0.0);
  fprintf(stderr, "\n");
}

/* This replaces libFuzzer's mutator: truncate under `--truncate`, then libFuzzer's default suite.

   `Seed` is libFuzzer's own PRNG output and is unused.

   The visibility attribute is load-bearing: libFuzzer finds this by
   `dlsym(RTLD_DEFAULT, "LLVMFuzzerCustomMutator")`, so under the hidden-visibility default the
   symbol stays `private external`, the lookup fails silently, and the campaign runs the default
   mutators untruncated. `fuzz-run/build.sh` checks the linked binary exports it. */
__attribute__((visibility("default")))
size_t LLVMFuzzerCustomMutator(uint8_t *Data, size_t Size, size_t MaxSize, unsigned Seed) {
  (void)Seed;
  if (g_trunc) Size = basalt_truncate(Data, Size);
  return LLVMFuzzerMutate(Data, Size, MaxSize);
}

/* Libfuzzer harness -- called by libFuzzer loop during testing.
   Failure model follows bolero (lib/bolero-libfuzzer): the Lean closure prints the counterexample,
   returns code 1, and we abort(). libFuzzer's signal handler then saves the crashing input as an
   artifact (reproduce with `basalt-fuzz replay`) and exits with its error code. */
int LLVMFuzzerTestOneInput(const uint8_t *Data, size_t Size) {
  g_cursor = 0;
  lean_object *arr = lean_alloc_sarray(1, Size, Size);
  memcpy(lean_sarray_cptr(arr), Data, Size);

  lean_inc(g_run);                                    /* apply consumes the function object   */
  /* res : IO UInt8; Lean function applied to the world token; consumes arr. */
  lean_object *res = lean_apply_2(g_run, arr, lean_io_mk_world());

  uint8_t code;
  if (lean_io_result_is_ok(res)) {
    code = (uint8_t)lean_unbox(lean_io_result_get_value(res));
    lean_dec(res);
  } else {
    /* An exception -- this signals a broken harness, so end the campaign. */
    lean_io_result_show_error(res);
    lean_dec(res);
    basalt_fuzz_die("the property raised an exception");
  }

  g_stats.runs++;
  if (g_cov.first) basalt_cov_accumulate();
  if (g_guided) {
    if (g_cursor > Size) {
      g_stats.starved++;
      if (g_cursor - Size > g_stats.max_deficit) g_stats.max_deficit = g_cursor - Size;
    }
    if (g_trunc) basalt_after_run(Data, Size);
  }

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
