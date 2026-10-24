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

## Results

TODO
