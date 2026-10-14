# Hybrid random/coverage-guided generation for Basalt: a report

October 2026, branch `hybrid-fuzz` (off `cedar-experiments`). Measurements are on macOS arm64
(M-series, 12 cores) unless stated otherwise; §3.5 replicates the 5M round on Linux x86_64 (8 cores).
All are on Cedar's `gen-traced` property.

Charts: [`curves-5M-3trials.html`](curves-5M-3trials.html) (with time-based panels),
[`curves-1M-6trials.html`](curves-1M-6trials.html), and the Linux round's
[`curves-5M-5trials-linux.html`](curves-5M-5trials-linux.html) with its linear-axis twin
[`curves-5M-5trials-linux-linear.html`](curves-5M-5trials-linux-linear.html) (which adds the first
100 seconds); PNG snapshots of each sit beside them, and the Linux round's script output is
[`tables-5M-5trials-linux.txt`](tables-5M-5trials-linux.txt). The raw dumps (several GB per round)
are not checked in; §7 regenerates them.

## Summary

- **The question.** On Cedar, random generation (`IO`) covers more code early and coverage-guided
  fuzzing (`FuzzGen` under libFuzzer) overtakes it late, past ~10⁵–10⁶ tests. Can one campaign get
  both?
- **The short answer: the hybrid is the best of both worlds.** It climbs as fast as random — it *is*
  random until it switches — and then reaches fuzzing's higher plateau, sooner than fuzzing alone.
  Pure fuzzing starts far behind (at 10 s, ~800–950 edges short of the hybrid); pure random levels
  off ~65–100 edges short of the fuzzing arms. Replicated on Linux with 5 trials (§3.5).
- **Yes, for code coverage at mid-range budgets.** Random first, then fuzzing seeded with what random
  found. Until it switches the hybrid *is* random, so it matches random's early lead; after the switch
  it leads both pure arms. With a 5M budget that lead runs from the switch (~500k tests) to ~3M tests,
  or ~8 to ~50 minutes of wall-clock. With a 1M budget the switch comes at ~120k, and at 1M tests the
  margin over pure fuzzing is **+62 edges** (7,089 against 7,027, 6 trials; earlier rounds agree),
  more than coverage guidance itself buys over random at that budget (+36).
- **By 5M tests the advantage is gone, but the reliability is not.** All three fuzzing arms finish at
  ~7,197 edges, ~100 ahead of random; the hybrid's trials agree to **±1** edge, pure fuzzing's to ±34.
- **An adaptive switch matches the best hand-tuned one.** The rule below needs no per-property
  tuning and lands near the best fixed warm-up (≈117k tests at a 1M budget, against a hand-picked
  100k), and its switch point scales with the budget (≈480k at 5M).
- **Switching back to random buys nothing on Cedar.** Implemented, made non-churning (3–5 switches in
  5M tests), and ties the one-switch version.
- **For input diversity, random wins outright.** Random produces 3.5M distinct expressions in 55
  minutes; every fuzzing arm ~2.0M. If the goal is breadth of *inputs* rather than breadth of
  *code*, the fuzzing phase is a cost.

## 1. What was built

All of it is an option to the existing `fuzz` backend of `basalt-fuzz`; nothing else changes.

### `RecordGen`: a random run that is also a fuzzer input

`Basalt/Fuzz/Record.lean`. A random run can seed libFuzzer only if it *is* a `FuzzGen` byte buffer.
`RecordGen` makes each choice from SplitMix, uniformly as `IO` does, and records bytes `FuzzGen`
decodes to the same choice: for value `d` of a range of `r` outcomes it writes `raw = d + r·k` for a
random `k` that fits the `bytesFor r` bytes `FuzzGen` reads, since `FuzzGen` reduces modulo `r`.

Two simpler encodings fail. Random bytes decoded by `FuzzGen` have the wrong distribution (modulo
bias: from one byte, `0..55` are twice as likely as `56..199` in a range of 200) and the wrong length
(too short reads zeros past the end; too long leaves a tail no draw reads). A recorded buffer is
exactly as long as its run read.

`readNat_recordDraw` **proves** the per-draw decoding (no `sorry`). Whole-run agreement is a free
theorem of the generator's polymorphism, so it cannot be stated inside Lean; `BasaltTest/Fuzz.lean`
pins it on 500 runs over one-byte, multi-byte, power-of-256 and bignum ranges plus a recursive BST.

### One libFuzzer loop, two modes

`Basalt/Fuzz/native.c`. The whole campaign runs inside libFuzzer's loop with a mode flag:

- **Random mode.** The callback ignores libFuzzer's buffer, runs the property at `RecordGen`, and
  returns `-1`, so libFuzzer neither keeps the input nor records its coverage. The bridge judges each
  run itself, with libFuzzer's notion of a feature (an edge plus its counter's hit-count bucket: 1, 2,
  3, 4–7, 8–15, 16–31, 32–127, 128+), and keeps the recorded bytes of the runs that reach something new.
  libFuzzer's own check is internal C++ and could not be reused.
- **Fuzz mode.** Ordinary `FuzzGen` fuzzing.
- **Random → fuzz.** The kept runs are compressed by greedy set cover over the features *that phase*
  discovered (about half survive: ~880 of ~1,750 at a 1M budget), then the custom mutator hands them to
  libFuzzer one per call, so each enters the corpus by libFuzzer's own admission rule. Set cover
  matters because one-at-a-time admission cannot drop a seed that a later one subsumes (keep `A` for
  features 1–2 and `B` for 3–4, and `C` covering 1–4 is never new, so it is never kept).
- **Fuzz → random.** libFuzzer's corpus stays in memory, so the next fuzzing phase resumes from it plus
  whatever the random phase added; nothing the fuzzer did is lost.

A counterexample found in a random phase is saved as `crash-random-<n>`, a `FuzzGen` buffer that
`basalt-fuzz replay` reproduces.

### Flags

| flag | meaning |
|---|---|
| `--warmup=N` | random first, for at most `N` tests; alone, exactly `N` |
| `--warmup-stall=K` | end the first random phase when coverage levels off (rule below), with a minimum window of `K` tests |
| `--switch-back` | apply the rule in both directions, for the rest of the campaign |
| `--level=φ`, `--confidence=c` | the rule's parameters (defaults 1 and 10) |

All tests, in every phase, count against the one `-runs` budget.

## 2. When to switch: the rule

For the current phase, let

- `F` = *finds* so far in the whole campaign: tests that reached some feature no earlier test did;
- `H` = the remaining budget, `R − tests run` (or the phase's length `n` if `-runs` is unbounded);
- `r_other` = the other mode's find rate over the last window on which it was left (`(finds+1)/window`).

The rate worth staying for is

&nbsp;&nbsp;&nbsp;&nbsp;`λ* = min( φ·F/H , r_other )`

and the phase is judged over consecutive windows of

&nbsp;&nbsp;&nbsp;&nbsp;`w = max( K, ⌈c / λ*⌉ )`

tests. It hands over at the end of the first window with **fewer than `c` finds**.

Reading it:

- **`φ·F/H`** is the rate at which spending the rest of the budget in this phase would add a further
  `φ` of everything found so far. With `φ = 1`: switch when continuing at the current rate would at
  most double the finds. It makes the waiting time grow with the budget — a small rate is still worth
  a lot over a long horizon, so it takes longer to be convinced it is negligible.
- **`r_other`** says: hand over only to a mode that was doing better when it was left. Without it,
  once both modes fall below `φ·F/H`, each "levels off" in its first window and the campaign churns
  (measured: ~2,500 switches per 1M tests). With it, a mode that left because it was stuck sets a low
  bar for its successor, windows only lengthen, and churn dies out (3–5 switches per 5M tests).
- **Whole windows, not a sliding one**: a sliding window tested after every test fires on noise almost
  at once. `c` is the confidence: at the threshold rate a window expects `c` finds.
- **Closed form.** If finds grow like `b·ln n`, the first switch lands at `n* ≈ (b/F)·R/φ`: linear in
  the budget, scaled by how fast coverage is still growing relative to its size.

Two calibration findings shaped it:

- **Count finds, not features.** Features arrive in clumps — one novel run brings ~20 at once — so a
  window with "fewer than `c` features" usually just means "no novel run", which happens by chance:
  counting features switched at ~24k tests regardless of `φ`. Counting finds made the switch point
  stable across trials (±10%) and proportional to `1/φ`:

  | `φ` | switch at, `R = 1M` (2 trials) |
  |---|---|
  | 0.5 | 195k, 225k |
  | 1 | 126k, 135k |
  | 2 | 66k, 69k |
  | 4 | 39k, 44k |

- **Recompute the window as `F` grows.** A window sized at the start of a phase, when `F ≈ 1`, is
  ~10⁷ tests long and never closes.

`φ = 1` was chosen because it lands closest to the best fixed warm-up measured (100k at a 1M budget).
It is calibrated on one property family; see §5.

## 3. Results

Arms: `random` (SplitMix inside libFuzzer's loop, so coverage is counted identically), `fuzz-noramp`
(pure `FuzzGen`, `-max_len=65536 -len_control=0`, the best pure-fuzzing setting measured on Cedar),
`warm-N` (fixed `--warmup=N`), `auto-1` (`--warmup-stall=0 --level=1`), `back-1` (`--switch-back`).
"Edges" are SanitizerCoverage edges in Cedar's own code, excluding its printing code.

### 3.1 At 5M tests, 3 trials, one trial per core (so time is fair)

**By tests run** (mean ± SE):

| tests | random | fuzz-noramp | auto-1 | back-1 |
|---|---|---|---|---|
| 10k | 6,465 ±16 | 5,541 ±162 | 6,473 ±28 | 6,433 ±38 |
| 100k | 6,780 ±11 | 6,506 ±69 | 6,763 ±8 | 6,782 ±7 |
| 1M | 6,988 ±4 | 7,016 ±35 | **7,083 ±4** | **7,076 ±1** |
| 5M | 7,098 ±4 | 7,198 ±34 | 7,196 ±1 | 7,198 ±10 |

**By elapsed time.** Random is ~25% faster per test (5M tests in 56 minutes against ~70); the last row
is when the fastest trial finished:

| time | random | fuzz-noramp | auto-1 | back-1 |
|---|---|---|---|---|
| 10 s | 6,420 | 5,591 | **6,528** | 6,495 |
| 1 min | 6,740 | 6,353 | 6,747 | 6,756 |
| 5 min | 6,918 | 6,829 | 6,911 | 6,891 |
| 15 min | 7,015 | 7,018 | **7,089** | 7,080 |
| 30 min | 7,061 | 7,107 | **7,144** | 7,130 |
| 55 min | 7,098 | 7,186 ±31 | 7,182 ±6 | 7,176 ±15 |

**Distinct expressions:**

| | random | fuzz-noramp | auto-1 | back-1 |
|---|---|---|---|---|
| at 5M tests | 3,538,786 | 2,514,911 | 2,728,226 | 2,741,665 |
| at 55 min | 3,536,983 | 1,986,768 | 2,032,274 | 2,048,390 |

**Edge sets, pooled over trials** (`fuzz-run/edge-sets.py`):

| | mean per trial | union of 3 trials | only this arm | missed, reached by another |
|---|---|---|---|---|
| random | 7,098 | 7,133 | 1 | 204 |
| fuzz-noramp | 7,198 | **7,294** | 53 | 43 |
| auto-1 | 7,196 | 7,224 | 6 | 113 |
| back-1 | 7,198 | 7,273 | 7 | 64 |

**Switching.** `auto-1` switched at 489k, 430k, 529k. `back-1`: random → fuzz at ~450k–540k, back to
random at ~1.1M (after ~650k of fuzzing), a 20k–40k random burst, then fuzzing to the end; one trial
made one more burst at 3.9M.

### 3.2 At 1M tests, 6 trials (all trials concurrently on 12 cores, so time is not fair)

| tests | random | fuzz-noramp | warm-100000 | auto-1 | back-1 (old rule†) |
|---|---|---|---|---|---|
| 100k | 6,760 ±10 | 6,536 ±28 | 6,790 ±8 | 6,776 ±11 | 6,780 ±9 |
| 1M | 6,991 ±6 | 7,027 ±12 | 7,086 ±8 | **7,089 ±9** | 7,055 ±5 |
| distinct at 1M | 731,542 | 484,456 | 514,111 | 518,118 | 597,290 |

† Without the `r_other` term: it churned ~2,500 times per trial, which is what led to that term.

`auto-1` switched at 115k–128k in all six trials.

### 3.3 Earlier rounds (the first, pre-loop implementation of the fixed warm-up)

| property, trials × tests | random | fuzz-noramp | warm-10000 | warm-100000 |
|---|---|---|---|---|
| `gen-traced`, 6 × 1M | 6,998 ±10 | 7,029 ±7 | — | 7,079 ±8 |
| `gen-traced`, 3 × 1M | 6,999 | 7,026 | 7,084 | 7,110 |
| `wide-traced`, 3 × 1M | 6,465 | 6,516 | 6,550 | 6,560 |

The second Cedar generator (`wide-traced`) shows the same ordering.

### 3.5 Replication on Linux x86_64, 5M tests, 5 trials (time is not fair)

Amazon Linux 2023, 8 cores, the same four arms and binary build recipe as §3.1; 20 trials ran 8 at a
time, so the time columns compare trials under somewhat different loads. Mean ± SE:

| tests | random | fuzz-noramp | auto-1 | back-1 |
|---|---|---|---|---|
| 10k | 6,428 ±17 | 5,703 ±32 | 6,439 ±21 | 6,428 ±21 |
| 100k | 6,784 ±9 | 6,519 ±46 | 6,765 ±14 | 6,778 ±4 |
| 1M | 6,991 ±5 | 7,029 ±13 | **7,071 ±5** | 7,064 ±6 |
| 5M | 7,104 ±5 | 7,167 ±10 | 7,170 ±7 | **7,175 ±5** |

| time | random | fuzz-noramp | auto-1 | back-1 |
|---|---|---|---|---|
| 10 s | 6,356 | 5,696 | 6,493 | **6,503** |
| 100 s | 6,812 | 6,557 | 6,797 | **6,815** |
| 15 min | 7,019 | 7,034 | **7,076** | 7,069 |
| 58 min (random done) | 7,104 | **7,152** | 7,143 | 7,150 |

- **The picture of §3.1 holds**: the hybrids track random until their switch (427k–590k tests),
  lead both pure arms from there to past 1M, and finish level with pure fuzzing at 5M, ~65 edges
  ahead of random.
- **The first 100 seconds** (linear chart) show the gap the hybrid avoids: pure fuzzing needs about
  a minute to reach what random and the hybrids cover in ~10 s. Within it, the hybrids' random phase
  is slightly ahead of the `random` arm (~140 edges at 10 s, ~6% more distinct expressions at 100 s),
  as on macOS (§3.1, 10 s); the two run different random paths (`RecordGen` in the `fuzz` backend
  against `io-libfuzzer`), and the gap is gone by 5 minutes.
- **Edge-set diversity again favours pure fuzzing**: union over 5 trials 7,266 (58 edges no other arm
  reached) against 7,216 for `auto-1`, 7,222 for `back-1`, 7,152 for random.
- **Switching back** happened 1–3 times per trial (first back to random at 1.2M–1.6M) and ends within
  noise of `auto-1`, as in §3.1.
- **Distinct expressions at 5M tests**: random 3.54M, `back-1` 2.73M, `auto-1` 2.72M, `fuzz-noramp`
  2.44M.

### 3.4 Bug-finding on the depth benchmarks (300 trials each, fixed run budget)

| property, budget | off | fixed warm-up (10%) | `--warmup-stall=0` | `--switch-back` |
|---|---|---|---|---|
| `chain-3`, 1,000 runs | 43.7% | 59.0% | 82.7% | 62.0% |
| `long-16`, 3,000 runs | 18.0% | 29.3% | 18.7% | 13.3% |

These benchmarks put one bug behind nested guards, so they measure *depth*, not the breadth the hybrid
is for; they are here to show it does not hurt depth, not to choose its settings. Every `chain-3` find
under the hybrid came in the fuzzing phase. The likely reason: `chain-3`'s first guard is a uniform
1-in-256 byte, which random hits at exactly that rate, while libFuzzer starting from an empty input
must first insert a byte *and* get its value right — so random banks the first stage cheaply and
hands the fuzzer a seed already past it. At budgets this small the adaptive rule spends much of the
budget on random (two-thirds on `chain-3`), which is why it helps there and does nothing for
`long-16`.

## 4. Interpretation

- **Breadth of code versus breadth of inputs.** The fuzzing phase earns its place only for code
  coverage at mid-range budgets. For distinct inputs it is a pure cost: random produces ~75% more per
  unit of time. Which one matters depends on what "breadth" means for the property being tested.
- **The hybrid is the low-variance choice.** At 1M–5M tests its trials agree to within a few edges;
  pure fuzzing's spread is ±34 at 5M. A single campaign is more predictable with the hybrid.
- **Independent pure-fuzzing runs are more diverse.** Pure fuzzing's trials wander into different
  territory (union 7,294 against 7,224 for the hybrid over 3 trials). The hybrid's trials start from
  near-identical random corpora and end up in the same place. If one runs several campaigns, pure
  fuzzing reaches more in total — an argument for diversifying hybrid runs (different `φ`, or
  RandSet-style randomized seed subsets) rather than against the hybrid.
- **The lead starts at the switch, and the switch scales with the budget.** Before it, the hybrid is
  random within noise (at 100k–330k tests of a 5M budget, random is 10–20 edges ahead of both
  hybrids, inside the trial-to-trial spread). So the budget given to `-runs` decides when the hybrid
  starts paying, which is the intended behaviour of the rule but means a too-large `-runs` delays the
  benefit.
- **By 5M tests on Cedar, fuzzing alone has caught up.** The hybrid's advantage is in getting there
  sooner, not in getting further. Whether it gets further on a property with more reachable code is
  open: CEDAR.md notes that what bounds coverage here is the property, not the search.
- **Switching back does not pay here** because random, after the first fuzzing phase, finds almost
  nothing the corpus has not already reached. It may pay where random's distribution reaches regions
  the mutated corpus drifts away from; Cedar does not appear to be such a case.

## 5. Caveats

- **Two machines, one benchmark family.** Two Cedar generators; macOS arm64, with the 5M round
  replicated on Linux x86_64 (§3.5). `φ = 1` is calibrated on Cedar.
- **Few trials at 5M.** Three per arm: enough for the 100-edge gap to random and for the variance
  difference, not for distinguishing the three fuzzing arms at 5M.
- **Time at 1M is contended.** The 1M runs put 30 trials on 12 cores; only the 5M runs (12 trials on
  12 cores) are fair by time.
- **Novelty in a random phase is judged on the generator's `RecordGen` specialization**, not its
  `FuzzGen` one, so a seed can look new to the warm-up and not to libFuzzer. libFuzzer re-judges each
  seed on admission, so the cost is only a few wasted seeds.
- **The wall-clock baseline, `random`, runs inside libFuzzer's loop** (so that coverage is counted
  identically). Basalt's plain `io` backend is faster still (~820k runs/s against ~137k on `bst-gen`
  in the backend table); against it the time comparison would favour random more.

## 6. Open questions

1. Does the hybrid get *further*, not just sooner, on a property with more reachable code than
   Cedar's soundness property exercises?
2. Diversifying hybrid runs: randomized seed subsets (RandSet's Algorithm 1) per fuzzing phase, or
   per-run `φ`, to recover pure fuzzing's union while keeping the hybrid's per-run reliability.
3. Distinct inputs as the switching signal, for properties where breadth of inputs is the goal.
4. A time-based budget (`-max_total_time`) in the rule, since `H` is measured in tests and the modes
   cost different amounts per test.

## 7. Reproducing

```sh
fuzz-run/hybrid-experiment.sh            # §3.1: build, 4 arms × 3 trials × 5M tests, every table
TRIALS=5 fuzz-run/hybrid-experiment.sh   # §3.5
RUNS=1000000 TRIALS=6 ARMS="random fuzz-noramp warm-100000 auto-1 back-1" \
  fuzz-run/hybrid-experiment.sh          # §3.2
TRIALS=300 SETTINGS="off --warmup=100 --warmup-stall=0 --switch-back" \
  fuzz-run/compare-grow.sh chain-3       # §3.4
BASALT_PHASE_TRACE=1 fuzz-run/basalt-fuzz gen-traced --warmup-stall=0 -runs=1000000   # the rule, live
```

`hybrid-experiment.sh` writes `tables.txt`, `curves.html` and `curves-linear.html` into `$OUT` (default
`/tmp/hybrid-exp-gen-traced`). For the time tables to be fair it needs a core per trial — 12 for the
default — and warns when it has fewer. The raw data behind this report is not checked in.
