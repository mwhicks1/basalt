# Lean `Nat` comparisons, visible to `--cmp`

Step 2 of the `--cmp` plan ([`../2026-10-gt-cmp/REPORT.md`](../2026-10-gt-cmp/REPORT.md)), on
`hybrid-fuzzing`. `--cmp` plants compared operands into draws, but Lean's `Nat` comparisons never
reach the comparison hook: for small values `lean_nat_eq`/`lt`/`le` compare the tagged pointers
(`2n+1`), and SanitizerCoverage traces integer comparisons only. So `--cmp` learns Lean's constants
only from the source scan (`harvested_literals%`), and never sees a computed one.

## Plan (agreed 2026-10-27)

### Build

- **A force-included header** (`-include`, in the instrumented libraries' `moreLeancArgs`) that wraps
  `lean_nat_eq`, `lean_nat_ne`, `lean_nat_lt`, `lean_nat_le` and their `dec_` forms: when both operands
  are scalars it calls the 8-byte comparison hook with the *untagged* values, then compares as before.
  Lean's generated code is unchanged; the hook reaches `--cmp`'s pair table and libFuzzer's own
  table of recent compares through the existing `--wrap`.
- **`--nat-cmp`** turns the hook on at run time (a weak, default-off switch), so one binary measures
  with and without it. **`--no-literals`** turns off the harvested literals, for the needle test.
- **Scope:** Basalt, `BasaltFuzz` and the executable root first. Cedar's code needs the flag in Cedar's
  own `lakefile.lean` (`basalt-integration`); a second step if the first works.
- **No filtering** of noisy pairs (loop bounds, our own decoding's comparisons), as libFuzzer does not
  filter. A remedy only if a measurement shows crowding.

### Measurements

- **Needles, literals off:** `fuzz-noramp+cmp` with literals (the reference), and with `--no-literals`
  without and with `--nat-cmp`. Expected: without literals or hook neither needle is found; with the
  hook both are, `needle-2` without the `± 1`, since its second constant `0xDEADBEEF + 1` is now
  compared at run time. 10 trials × 1M.
- **Cost and noise:** throughput with and without the hook, the pair table's turnover, and the share
  of `--cmp` plants that match a compared value.
- **Cedar** (after the Cedar step): coverage at 1M and the fault suite, `auto-stale-corpus+cmp` with and
  without `--nat-cmp`.

## Results

TODO
