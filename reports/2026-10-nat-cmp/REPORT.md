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

Built on `hybrid-fuzzing` (`97aeac6`): `Basalt/Fuzz/nat_hook.h`, force-included into the three
instrumented targets. A smoke run decoded every plant as planted.

### Needles

10 trials per arm, 1M tests, median tests to the find; every arm finds both needles in 10/10
([`needles.txt`](needles.txt)).

| arm | `needle` | `needle-2` |
|---|---|---|
| `fuzz-noramp+cmp` (literals, no hook) | 6,323 | 8,562 |
| `fuzz-noramp+cmp+nolits` | 144,865 | 97,636 |
| `fuzz-noramp+cmp+nolits+natcmp` | **799** | **3,154** |
| `fuzz-noramp+cmp+natcmp` | **370** | **2,118** |
| `auto-stale-corpus+cmp` | 12,692 | 15,818 |
| `auto-stale-corpus+cmp+natcmp` | **786** | 10,044 |

- **The hook replaces the source scan, and does better.** With literals off and the hook on, `needle`
  falls 8× and `needle-2` 3× against literals without the hook. `needle-2`'s second constant,
  `0xDEADBEEF + 1`, now arrives as its run-time value, where before it needed a literal plus `± 1`.
- **Both together are fastest** (370 and 2,118), and the hybrid gains the same way (786 against
  12,692 on `needle`).
- **Without either, the needles are still found, but slowly** (145k and 98k tests: 11–23× slower than
  with literals, 31–180× slower than with the hook): some other captured operand reaches them.
  Literals remain a cheap fallback.

### Cedar

**Build.** Cedar's C is compiled under Cedar's own `lakefile.lean`, so the header reaches it through an
environment variable: `fuzz-run/build.sh` exports `BASALT_NAT_HOOK` (the header's path), and Cedar's
`lean_lib Cedar` adds `-include` it when set, nothing otherwise. Done on the faulty-Cedar branch first
(`basalt-mutants` `c91909e4`), which every Cedar experiment builds against; the mainline Cedar
(`basalt-integration`) gets it if the results justify. Confirmed in the objects: Cedar's
`Evaluator` and Basalt's `Staged` both reference the switch. Binary `dece68e2c7c9` (`cedar-mutants`
`d765e36`).

**Queued:** coverage at 1M (`fuzz-noramp+cmp` and `auto-stale-corpus+cmp`, each with and without
`+natcmp`, 5 trials) and the fault suite (`auto-stale-corpus+cmp` with and without `+natcmp`, the 19
pairs × 10 trials).

TODO: results
