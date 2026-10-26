# A budget-free switching rule, and libFuzzer-style comparison planting

Two follow-ups to [`../2026-10-planting/REPORT.md`](../2026-10-planting/REPORT.md), on branch
`hybrid-gt-cmp` (off `choice-fuzz`), cherry-picked to `cedar-mutants` for the Cedar fault runs.

## Plan (agreed 2026-10-25)

### 1. Switching rule: Good-Turing (`auto-gt`)

The current rule (`auto-1`) ends the random phase after a window of `conf · H / (level · F)` tests
with fewer than `conf` finds, where `H` is the budget left. When random makes few finds the window
is a fixed fraction of `-runs` (71% of 1M on the needles), and with no `-runs` it never closes.

- **Rule.** The random phase is i.i.d. sampling, so Good-Turing applies: with `f₁` the number of
  features reached by exactly one test so far, the chance that the next random test reaches
  something new is about `f₁ / n`. Switch when `n / f₁` (the expected tests to the next find)
  exceeds the tests random has run, i.e. `f₁ ≤ 1`, after a floor of 256 tests. One per-feature
  counter (tests that reached it, capped at 2), updated in the existing scan.
- **Scope.** The first switch only. Switch-back (`back-1`) is unchanged; doubling hysteresis for it
  is a follow-up.
- **Arms** (new binary; status quo rerun on it): `auto-1+trunc` vs `auto-gt+trunc`, and
  `auto-1+trunc+plant+nudge` vs `auto-gt+trunc+plant+nudge`. Pure arms are not affected by the rule
  and are reused from the planting report as context.
- **Measurements:**
  - **Needles:** the planting pair, 10 trials × 1M. Expected: `auto-gt` switches within a few
    hundred tests.
  - **Cedar coverage:** `gen-traced` and `wide-traced`, the plain pair, 5 trials at 5M and at 1M.
    Edges by tests and time, rare edges, switch points. Expected: `auto-gt`'s switch point does
    not move with the budget. The open question is whether it costs coverage. Plus one stricter
    threshold at 5M, as a sensitivity check.
  - **Cedar faults:** the 19 pairs, the plain pair, 10 trials × 500k.

### 2. `--cmp`: comparison planting as libFuzzer does it

Replaces `--plant` and `--nudge` with one flag that mirrors libFuzzer's `Mutate_AddWordFromTORC`
(`fuzz-run/vendor/fuzzer-src`, llvmorg-22.1.8, the linked runtime), at the draw level:

1. Keep comparison operand pairs `(A, B)` from the 4- and 8-byte hooks (odd values also untagged).
2. Pick a pair; find a recorded draw whose decoded value is `A`; write `B + δ`, `δ ∈ {−1, 0, +1}`
   (and symmetrically). If no draw holds `A`, a random draw whose range admits the value.
3. Harvested Lean literals are unpaired constants with the same `± 1`.
4. Rate: one more mutator beside libFuzzer's 13, so about 1/14 of steps.
5. Constants whose plant reached new coverage are kept and preferred, as `PersAutoDict` does.
6. No filtering of noisy pairs, as libFuzzer does not filter. A remedy for the decoding code's own
   comparisons only if a measurement shows them crowding out the rest.

The pool holds integer pairs, unpaired constants and words, so that later sources (Lean `Nat`
comparisons, 1-/2-byte and `switch` hooks, `memcmp` words, Rust) plug in without rework.

**Measurements:** the needles (both must still be solved), Cedar coverage and throughput, and the
Cedar fault suite, each against the plain hybrid and against `+plant+nudge`, using the switching rule
from part 1 if it holds up.

### Amendments

- **2026-10-25, the rule's statistic.** A random-only trace showed `f₁` over *features* never
  falling to 1: in the thousands on Cedar, and stuck at 2 on the needle. Features count hit-count
  buckets, and the reported metric counts edges, so the rule now uses `f₁` over **edges**. Edges hit
  only once because of one-time process work are excluded, but only once shown to be such (below),
  never just for being hit early: an edge an early small test reaches is what random generation is
  for. The feature-based version is kept as a comparison arm.
- **2026-10-25, the rule replaced: a doubling window.** Excluding one-time edges needed a replay of
  each singleton's test at `RecordGen` from its saved random state. It was correct (on Cedar, 106 /
  115 edges excluded, none reached again in 300k tests), but the user judged it brittle: a statistic
  that needs first-time code removed does not fit. `f₁` counts a *state*; the replacement counts
  discovery *events*. At tests `N/2, N, 2N, …` (`N = 256`) a first random phase whose second half
  reached no new edge has saturated. First-time code is a discovery when its path is first reached,
  then stops. The window rule stays as the guaranteed switch, since a rule that never switches loses
  fuzzing's benefit entirely (the user's point: inefficient benefits beat none). Without `-runs` the
  modes alternate in doubling phases. Smoke checks: the needles switch at test 258; on Cedar each
  half-window still reaches 50–190 new edges, so the window rule switches as before (101k–132k of
  1M). Arms: `auto-dw`. The replay version's trials are kept only as its record.
- **`--cmp` built,** on the same binary (`cedar-mutants` `a9a7274`, binary `f86aee73a32c`): pairs from
  the 4/8-byte hooks, literals as unpaired constants, `± 1`, 1/14 of mutator calls, kept constants
  reused. Smoke: `needle` at ~1,100 tests and `needle-2` at 2.2k–8.6k, with no nudge flag; 0 decode
  mismatches.
- **Later, not in this round:** a probe-based switch, where short fuzzing bursts measure fuzzing's
  find rate against random's Good-Turing rate, with doubling spacing. Considered after this round's
  results.

## Results

One binary for everything (`f86aee73a32c`, Basalt `cedar-mutants` `a9a7274`), 7 trials at a time.
`auto-dw` is `auto-1` plus the doubling-window exit; `+cmp` is `--cmp`.

### Needles

10 trials per arm, 1M tests, median tests to the find ([`needles.txt`](needles.txt)):

| arm | `needle` | `needle-2` | switched at |
|---|---|---|---|
| `fuzz-noramp+trunc+plant+nudge` | 69 | 63,392 | – |
| `fuzz-noramp+trunc+cmp` | 6,292 | 7,508 | – |
| `auto-1+trunc+plant+nudge` | 714,356 | 767,266 | 714,287 (all 10) |
| `auto-dw+trunc+plant+nudge` | 328 | 92,828 | 258 (all 10) |
| `auto-dw+trunc+cmp` | 6,516 | 8,117 | 258 (all 10) |
| `choice` | 1,693 | 19,554 | – |

All arms find both needles in 10/10. The doubling window ends the random phase at its first
checkpoint, so the hybrid now costs ~258 tests over pure fuzzing instead of 714k. `--cmp` is
slower than `--plant --nudge` on `needle` (1/14 of steps against 1/4, and a third of its picks are
literals) and much faster on `needle-2`, where the `± 1` on literals and the reuse of a kept
`0xDEADBEEF` supply the second stage. With either, the byte fuzzer is as good as `choice`.

### Cedar: coverage at 1M tests

5 trials per arm ([`cedar-coverage.txt`](cedar-coverage.txt)); p against `auto-1+trunc`:

| arm | `gen-traced` | p | `wide-traced` | p (by time) | tests/s ratio |
|---|---|---|---|---|---|
| `fuzz-noramp+trunc` | 7,263 | – | 6,744 | – | 1.00 / 1.00 |
| `fuzz-noramp+trunc+cmp` | 7,253 | (0.52 vs pure) | 6,740 | (0.84 vs pure) | 0.87 / 0.92 |
| `auto-1+trunc` | 7,293 | – | 6,738 | – | 1.00 / 0.97 |
| `auto-dw+trunc` | 7,283 | 1.00 | 6,748 | 0.79 (0.65) | 0.97 / 1.00 |
| `auto-dw+trunc+cmp` | 7,293 | 0.89 | **6,772** | **0.008 (0.040)** | 0.88 / 0.92 |

The doubling window never fired on Cedar: switches came from the window rule at 94k–152k tests,
the same range as `auto-1` (107k–152k). `--cmp` ties without the hybrid and, in it, adds ~34 edges on
`wide-traced`. Rare edges tie throughout.

### Cedar: no `-runs`

5 trials × 30 min ([`cedar-nobudget.txt`](cedar-nobudget.txt)):

| arm | `gen-traced` | p | `wide-traced` | p |
|---|---|---|---|---|
| `auto-1+trunc` | 7,281 | – | 6,762 | – |
| `auto-dw+trunc` | **7,307** | **0.008** | 6,752 | 1.00 |

Without a budget the old rule switched at test 11 in every trial, so it was pure fuzzing. The new
rule alternated in doubling phases (10k random, 10k fuzzing, 20k, 40k, … 8 switches). It is better on
`gen-traced` and ties on `wide-traced`.

### Cedar: injected faults

The 19 pairs, 10 trials per arm, 500k tests ([`faults.txt`](faults.txt)). Pairs significantly faster /
slower (p < 0.05):

| | vs `auto-1+trunc` | vs `auto-dw+trunc` | vs `fuzz-noramp+trunc` |
|---|---|---|---|
| `auto-dw+trunc` | **0 / 0** | – | 7 / 7 |
| `auto-dw+trunc+cmp` | **0 / 0** | **0 / 0** | 6 / 5 |
| `fuzz-noramp+trunc+cmp` | 6 / 7 | 6 / 7 | **0 / 0** |

## Conclusions

- **The doubling window fixes the switch without hurting Cedar.** It ends the random phase at test
  258 on the needles (714k before), and on Cedar it never fires: coverage, rare edges and all 19
  fault pairs are unchanged. Without `-runs` it replaces a rule that switched at test 11 with a
  doubling alternation, which is better on one property and ties on the other.
- **`--cmp` is the single flag to keep.** It solves both needles on its own, as well as `choice` and
  `--plant --nudge`. Unlike those, it costs pure fuzzing nothing on Cedar's faults (0 / 0, against
  0 / 2 and 0 / 3), because it runs at libFuzzer's rate, 1/14 of steps. In the hybrid it ties on
  faults and adds edges on `wide-traced`. It costs 8–13% throughput, for the recording.
- **The configuration the evidence supports:** `auto-dw+trunc+cmp`, the hybrid with the doubling exit
  and `--cmp`. `--plant` and `--nudge` can be retired.
- **What is still open:** whether a probe-based switch (fuzzing's measured rate against random's)
  switches *earlier* on Cedar with benefit; this round only made sure no rule switches later or
  never. Pair-matched plants are rare here, since Lean's `Nat` comparisons never reach the hook.
  That is the next item on the `--cmp` plan (a `lean.h` override).
