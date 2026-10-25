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
- **Later, not in this round:** a probe-based switch, where short fuzzing bursts measure fuzzing's
  find rate against random's Good-Turing rate, with doubling spacing. Considered after this round's
  results.

## Results

TODO
