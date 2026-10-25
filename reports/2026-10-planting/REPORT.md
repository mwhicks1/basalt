# Planting compared-against constants in the byte fuzzer

Can the byte fuzzer (`FuzzGen`) gain the one advantage the choice backend showed, planting a
compared-against constant into a draw, without losing its coverage or speed? And how does planting
combine with the random-then-fuzz hybrid? Background:
[`../2026-10-choice-fuzzing/GATES.md`](../2026-10-choice-fuzzing/GATES.md) (choice representation:
no gain on Cedar; its wins are the needles, via planted literals) and
[`../2026-10-cedar-faults/REPORT.md`](../2026-10-cedar-faults/REPORT.md) (the hybrids are the best
arms on Cedar's injected faults).

## Plan (agreed 2026-10-24)

### Build (branch `choice-fuzz`; `FuzzGen` only, no choice backend, no change to `Gen`)

1. **Recording only when fuzzing.** Under `--plant`, `FuzzGen`'s `choose` (`drawStep`) records
   each draw's byte offset, `lo` and `hi`, but only in the fuzzing phase (all along for pure
   fuzzing, from the switch on for the hybrid). Without the flag nothing changes.
2. **Trace cache.** The mutator keeps the trace of the last run and of the inputs libFuzzer saves to
   its corpus. When an input's trace is missing, that mutation falls back to an ordinary one.
3. **One pool of constants:**
   - **Harvested Lean literals** (`harvested_literals%`), since Lean `Nat` comparisons compile to
     tagged-pointer compares that `trace-cmp` never sees.
   - **Runtime comparison operands** from the wrapped 4- and 8-byte `trace-cmp` hooks, with the
     choice-only gate removed. These cover instrumented C and Rust code and computed values.
4. **One planting mutation.** Pick a recorded draw whose `[lo, hi]` holds a pool constant `v`, and
   overwrite exactly its bytes with `v − lo`, big-endian, at its width. It is one more choice in
   `FuzzGen`'s custom mutator, so libFuzzer's ordinary mutations stack after it. No pre-nudged
   values: a target needing `v + 1` (`needle-2`) relies on havoc to supply the nudge.
5. **Checks before measuring.** A planted input decodes to the planted value; the pool fills under
   the byte fuzzer; `--plant` off behaves as before.

### Arms

`random`, `fuzz-noramp+trunc`, `fuzz-noramp+trunc+plant`, `auto-1+trunc`, `auto-1+trunc+plant`;
`choice` as the reference on the needles.

### Measurements

- **A. Needles (where planting should matter).** `needle` and `needle-2`, 10 trials per arm, large
  budget (about 1M tests), tests and seconds to the find. Expected: pure fuzzing with planting finds
  both quickly; the hybrid with planting finds them later, by about its random phase; neither finds
  them without planting. `needle-2` shows whether havoc supplies the `+1`.
- **B. Cedar (that it does not hurt).**
  - **Cost:** tests/s with and without `--plant`, and the cache's memory. This tests the ~10%
    estimate from Phase 0.4.
  - **Bugs:** the 19 non-trivial (fault, property) pairs × the 4 byte arms × 10 trials × 500k tests,
    all on the new binary.
  - **Coverage:** `gen-traced` and `wide-traced`, 5 trials × 1M tests, edge totals and rare edges
    (`fuzz-run/rare-edges.py`).
  - **Expected:** a tie on bugs and coverage, and a modest throughput cost.

### Not in this round

- A draw-aware nudge (a small signed delta to one recorded draw), only if `needle-2` stalls.
- Making Lean `Nat` comparisons visible to `trace-cmp` (a `lean.h` override that untags and calls
  the hook).
- 1- and 2-byte, `switch` and `memcmp`/`strcmp`/`bcmp` hooks. Rust string and slice equality needs
  the last.
- Planting a whole string, which needs to know which draws form one.
- A Rust differential-testing target.

## What was built

- **`--plant`**, on `choice-fuzz` (`332f399`) and `cedar-mutants` (`d4eb73e`). It records the draws
  of every fuzz-mode run and caches traces. A quarter of the custom mutator's calls plant a
  constant into a draw whose range holds it. The pool holds the harvested literals plus the 4- and
  8-byte `trace-cmp` operands, which are now collected under the byte fuzzer too.
  - **Decode check:** after every plant, the next run must decode the planted value at that draw's
    offset. It never failed: 0 mismatches in every run measured, tens of thousands of plants each.
  - **Cache policy:** the experiment binaries are built from `cedar-mutants`. Its cache, like
    `--truncate`'s there, also keeps inputs libFuzzer saves for being smaller, and the hybrid's
    seeds. `choice-fuzz`'s older cache keeps new-feature runs only, so it misses more parents.
- **`--nudge`** (`9684a48` / `922a63b`), added once `needle-2` stalled under `--plant` alone (the
  agreed trigger). It moves one recorded draw by a small signed delta within its range, the
  distribution of the choice mutator's `delta`, and rewrites exactly that draw's bytes. It runs on a
  quarter of the calls `--plant` does not take. It is not literal-specific.

## Results

### A. Needles

10 trials per arm, 1M tests; median tests to the find (`>1000k`: not found in most trials)
([`needles.txt`](needles.txt)).

| arm | `needle` | `needle-2` |
|---|---|---|
| `random` | 0/10 | 0/10 |
| `fuzz-noramp+trunc` | 0/10 | 0/10 |
| `fuzz-noramp+trunc+plant` | 10/10, 751 | 0/10 |
| `fuzz-noramp+trunc+plant+nudge` | 10/10, **70** | 10/10, 27,847 |
| `auto-1+trunc` | 0/10 | 0/10 |
| `auto-1+trunc+plant` | 10/10, 715,038 | 2/10 |
| `auto-1+trunc+plant+nudge` | 10/10, 714,356 | 10/10, 766,496 |
| `choice` | 10/10, 480 | 10/10, 10,269 |

- **Planting does what the choice backend did.** Without it no byte arm finds either needle. With
  planting and nudging the byte fuzzer finds both every time. On `needle-2` it ties `choice`
  (p = 0.31), and on `needle` it is faster (70 vs 480 tests).
- **Havoc does not supply the `+1`.** Planting alone finds `needle-2` in no trial of 10. libFuzzer's
  arithmetic mutation lands on a random byte offset with a random endianness, so it rarely moves the
  planted draw by exactly one. The draw-aware nudge does.
- **The hybrid's delay is set by the budget, not the target.** Its random phase ended at test
  714,287 in every trial. Random finds only 4 new-coverage inputs here, and the switching rule
  (`fuzz-run/README.md`, "Random warm-up") waits until a window of `conf · H / (level · F)` tests has
  passed, where `H` is the budget left and `F` the finds so far. With `F = 4` and a 1M budget, that
  is 71% of the budget. On a target where random finds fewer than `conf / level` = 10 things, the
  random phase lasts a fixed fraction of `-runs`. With no `-runs` the window has no horizon: it
  never closes when random makes fewer than 10 finds, and closes almost at once when it makes
  more (test 11 on `gen-traced`; found later, in
  [`../2026-10-gt-cmp/REPORT.md`](../2026-10-gt-cmp/REPORT.md)). Every run in this report had a
  `-runs` budget. The hybrid still finds both needles once it switches.

### B. Cedar: cost and coverage

5 trials per arm, 1M tests, the unfaulted build ([`cedar-coverage.txt`](cedar-coverage.txt)). p is
against `fuzz-noramp+trunc`, or for the planting hybrid against `auto-1+trunc`.

| arm | `gen-traced` edges | p | `wide-traced` edges | p (by time) | tests/s ratio |
|---|---|---|---|---|---|
| `fuzz-noramp+trunc` | 7,242 | – | 6,724 | – | 1.00 |
| `+plant` | 7,186 | 0.31 | 6,693 | 0.056 (0.016) | 0.91 / 0.91 |
| `+plant+nudge` | 7,223 | 0.31 | 6,681 | 0.040 (0.016) | 0.89 / 0.93 |
| `auto-1+trunc` | 7,277 | – | 6,739 | – | 1.02 / 1.00 |
| `auto-1+trunc+plant+nudge` | 7,285 | 0.60 | 6,754 | 0.84 | 0.88 / 0.91 |

- **Cost: 7–12% throughput,** as Phase 0.4 measured for the same recording. The cache is 72–77 MB
  at 1M tests, about 20,000 traces. That is larger than Phase 0's 17–21 MB at 5M, because it keeps
  every input libFuzzer may save, not just new-feature ones. About 15% of planting attempts find no
  trace for their input. The operand pool fills its 1,024 slots.
- **The hybrid is unharmed.** With planting and nudging it ties the plain hybrid on both properties,
  by tests and by time, and on rare edges.
- **Pure fuzzing loses a little on `wide-traced`,** 31–43 edges (0.5%). By time that is
  significant (p = 0.016), and it is about what the lost throughput costs. `gen-traced` ties.

### B. Cedar: injected faults

The 19 non-trivial (fault, property) pairs of
[`../2026-10-cedar-faults/REPORT.md`](../2026-10-cedar-faults/REPORT.md), 10 trials per arm, 500k
tests, all six byte arms on one binary ([`cedar-faults.txt`](cedar-faults.txt)). Pairs where an arm
is significantly faster / slower (p < 0.05), out of 19:

| arm | vs `fuzz-noramp+trunc` | vs `auto-1+trunc` |
|---|---|---|
| `fuzz-noramp+trunc+plant` | 0 / 2 | 6 / 9 |
| `fuzz-noramp+trunc+plant+nudge` | 0 / 3 | 7 / 10 |
| `auto-1+trunc+plant` | 7 / 6 | **0 / 0** |
| `auto-1+trunc+plant+nudge` | 8 / 6 | **0 / 0** |

- **The hybrid is unharmed.** With planting, with or without nudging, it differs significantly from
  the plain hybrid on none of the 19 pairs. Its record against pure fuzzing is the plain hybrid's
  (7–6 and 8–6, against 8–6).
- **Pure fuzzing is slightly slower with planting.** It is slower on 2–3 pairs and faster on none:
  `+plant` on 8 `wide` (2.1k vs 733 tests) and 16 `wide` (5.7k vs 1.7k); `+plant+nudge` on 3 `gen`,
  16 `wide` and 28 `gen`. These are mostly faults pure fuzzing finds in a few thousand tests, where a
  quarter of its mutations going elsewhere, and 7–12% less throughput, shows. Across 19 pairs about
  one significant difference per comparison is expected by chance.
- **No fault here needs a planted constant,** so no gain was expected. As planned, this is the check
  that planting costs little, not a test of what it is for.
- **The rerun agrees with the earlier one.** The plain hybrid against pure fuzzing is 8–6 here and
  was 6–6 in the earlier run (another binary), so it is even within noise either way.

## Conclusions

- **Planting brings the choice backend's one advantage to the byte fuzzer.** On the needles,
  planting plus nudging matches `choice`: 10/10 on both, a tie on `needle-2`, faster on `needle`.
  Planting alone solves `needle` but not `needle-2`, whose `+1` libFuzzer's unaligned arithmetic does
  not supply.
- **It costs the hybrid nothing measurable on Cedar:** coverage ties, rare edges tie, and 0–0 on the
  19 fault pairs. It costs 7–12% throughput and ~75 MB at 1M tests.
- **So the configuration the evidence supports** is the hybrid (`auto-1+trunc`) with `--plant`,
  and `--nudge` if a target has compared values near constants. Neither changes `Gen`. Pure fuzzing
  with planting is slightly worse on easy Cedar faults, so planting should switch on with the
  fuzzing phase, as it does in the hybrid.
- **The hybrid's switching rule needs attention.** On a target where random finds fewer than
  `conf / level` (10) things, the random phase lasts a fixed fraction of `-runs` (71% at 1M); with
  no `-runs` it never ends, or, when random finds more early on, ends almost at once. The needles show it, and a real target with a tiny random-reachable
  surface would hit it too.

## Next steps

Beyond the "Not in this round" list above:

- Fix the switching rule for targets with very few random finds.
- Bring trace misses down: about 15% of planting attempts find no trace, against the choice
  backend's 4%.
- Measure `--nudge` alone (no planting), to tell its general value as an aligned arithmetic
  mutation apart from its role on `needle-2`. The `needle` speed-up with nudging (70 vs 751 tests),
  where no `+1` is needed, is not explained yet.
