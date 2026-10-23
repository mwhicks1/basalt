# Bug-finding on real Cedar: injected faults, five backends

The Cedar coverage gate ([`../2026-10-choice-fuzzing/GATES.md`](../2026-10-choice-fuzzing/GATES.md))
is saturated, and its bug-finding targets are toys. This experiment puts known faults into Cedar's
typechecker and evaluator and measures how fast each backend finds them, through the same proved
generators and the same properties. Linux x86_64, 8 cores, 7 trials at a time, 2026-10-23.

## Setup

- **Faults.** Cedar branch `basalt-mutants` (`c9adf7a7`, on `basalt-integration`) adds
  `Cedar.mutant k`, read from `CEDAR_MUTANT` by Basalt's C bridge (Basalt branch `cedar-mutants`,
  which builds against that Cedar). One binary carries every fault, and each process runs with at
  most one. Each fault is a one-line change that `type_of_is_sound` can detect. A fault that only
  changes a value without changing its type would be invisible to every property here, so none was
  included.
  - Typechecker (1–17): e.g. 2, `||` keeps the union of its operands' capabilities; 3, `if` does
    not intersect with the else branch's capabilities; 6, entity `in` ignores the hierarchy; 8, any
    capability justifies `hasTag`;
    13, a multi-attribute `has` whose tail is `tt` is `tt`; 15/16, `if`'s else branch / `||`'s
    right operand typed under the guard's capabilities.
  - Evaluator (20–28): e.g. 23, `in` is not reflexive; 24, `in` a set requires every member; 28, `contains` on an empty set is a type
    error.
  - The site of each fault is its `mutant k` in Cedar's diff.
- **Properties.** `gen-traced` (the proved-sound `CedarGen`) and `wide-traced` (`CedarWide`, whose
  candidates are filtered by the real, here faulty, `typeOf`). A kill is a failed
  `type_of_is_sound` check (`UNSOUND`), or for `gen-traced` the generator's judgment rejected by the
  faulty `typeOf` (`ill-typed`, rare: faults 15 and 16).
- **Arms.** `random`, `fuzz-noramp+trunc` (the rebaselined byte fuzzer), `auto-1+trunc` (its hybrid),
  `choice`, `choice-auto-1`.

## Screen

One trial per cell at 200k tests, on `random`, `fuzz-noramp+trunc` and `choice`
([`screen.txt`](screen.txt)):

- **Never killed (6):** 9, 11, 12, 14, 17, 26. Five of them make the typechecker accept more. A
  generator built for the correct typechecker produces only expressions that typechecker accepts,
  so these faults never matter. (`wide-traced` filters candidates with the faulty `typeOf`, but its
  candidates are themselves built to typecheck.) Fault 26 needs a record literal with a duplicated
  key, which neither generator builds.
- **Killed by every arm within ~2k tests (7):** 1, 4, 5, 20, 21, 22, 25.
- The remaining 19 (fault, property) pairs went to the main run.

## Results

Ten trials per arm, 500k tests per trial ([`kills.txt`](kills.txt)). Medians of tests to the kill,
where a trial that never kills counts as past the budget. p is a two-sided Mann-Whitney test by
permutation.

| fault, property | random | `fuzz-noramp+trunc` | `auto-1+trunc` | `choice` | `choice-auto-1` |
|---|---|---|---|---|---|
| 2 `wide` | 2/10, >500k | 10/10, **19.5k** | 10/10, 94.6k | 8/10, 351k | 7/10, 370k |
| 3 `gen` | 2/10, >500k | 10/10, **106k** | 10/10, 177k | 7/10, 292k | 10/10, **112k** |
| 3 `wide` | 4/10, >500k | 10/10, **39.4k** | 10/10, 117k | 8/10, 210k | 10/10, 141k |
| 15 `gen` | 0/10 | 10/10, **75.9k** | 10/10, 110k | 8/10, 254k | 10/10, 109k |
| 15 `wide` | 0/10 | 10/10, **5.0k** | 10/10, 84.3k | 9/10, 110k | 10/10, 86.9k |
| 16 `gen` | 1/10, >500k | 10/10, **23.4k** | 9/10, 224k | 9/10, 210k | 10/10, 91.0k |
| 16 `wide` | 4/10, >500k | 10/10, **3.5k** | 10/10, 75.9k | 10/10, 30.3k | 10/10, 68.2k |
| 8 `wide` | 162k | **664** | 67.3k | 97.8k | 70.5k |
| 8 `gen` | 161k | 94.0k | 82.2k | 246k | 83.2k |
| 13 `wide` | **69.2k** | 5/10, 453k | **69.3k** | 110k | **72.0k** |
| 13 `gen` | 197k | 199k | 148k | 134k | 99.8k |
| 7 `wide` | 90.0k | 198k | 76.3k | 146k | 69.8k |
| 24 `wide` | 176k | 111k | 101k | 128k | 78.9k |
| 6 `gen` | 1.9k | 21.1k | 4.6k | 17.2k | **1.9k** |
| 6 `wide` | 2.1k | 37.1k | 3.2k | 33.3k | **854** |
| 23 `gen` | 2.3k | 13.4k | 4.8k | 26.9k | **1.4k** |
| 23 `wide` | 2.9k | 21.0k | 4.2k | 16.5k | 2.5k |
| 28 `gen` | 9.1k | 24.2k | 10.4k | 22.6k | 7.4k |
| 28 `wide` | 3.2k | 50.0k | 9.0k | 25.8k | 9.9k |

Pairs where an arm is significantly faster / slower (p < 0.05), out of 19:

| | vs `random` | vs `fuzz-noramp+trunc` |
|---|---|---|
| `random` | – | 6 / 8 |
| `fuzz-noramp+trunc` | 8 / 6 | – |
| `auto-1+trunc` | 9 / 1 | 6 / 6 |
| `choice` | 6 / 6 | 1 / 7 |
| `choice-auto-1` | 7 / 0 | 7 / 5 |

The two hybrids against each other: `choice-auto-1` is faster on 2 pairs (6 `gen`, 16 `gen`) and
slower on 1 (2 `wide`), out of 19 ([`kills-hybrids.txt`](kills-hybrids.txt)). Wall-clock tracks
tests (median seconds are in `kills.txt`), since every arm runs at about the same rate.

## Findings

- **Coverage guidance finds bugs random generation misses.** Faults 2, 3, 15 and 16 are capability
  faults: they need a guard that grants a capability, then a read the faulty rule wrongly allows.
  Random finds them in 0–4 of 10 trials at 500k tests. The byte fuzzer finds them in every trial,
  at a median of 3.5k–106k tests. Real Cedar code plus a proved generator is a target where coverage
  guidance clearly pays, which the saturated edge totals of the gate could not show.
- **On shallow faults it costs 3–18×.** Faults 6, 23 and 28 (a few thousand random tests) take the
  byte fuzzer 13k–50k, because its early inputs are small and repetitive.
- **The hybrids get both.** `auto-1+trunc` is never significantly slower than random except on one
  pair, and `choice-auto-1` never is. Both kill the capability faults in nearly every trial: `auto-1+trunc` misses once (16 `gen`),
  `choice-auto-1` three times (2 `wide`).
  Against the byte fuzzer each loses on the deep faults, which pure fuzzing finds sooner, and wins
  on the shallow ones.
- **The choice representation does not help alone.** Pure `choice` is slower than the byte fuzzer
  on 7 pairs and faster on 1. Under the hybrid rule it is even with `auto-1+trunc` (2–1). This agrees
  with the coverage gate: no evidence for the choice-sequence representation on Cedar.
- **What the faults cannot reach.** Six faults are never killed. Most of them only matter on input
  the correct typechecker rejects, and a generator derived from that typechecker never produces such
  input. Faults like these need generators that deliberately produce ill-typed terms, the case
  `BASALT_MUTATION_FUZZING_DESIGN.md` argues about.

## Policy-level faults

`policy-traced` (Basalt `cedar-mutants` @ `e9d5dc0`) generates policy sets and checks Cedar's
validation, level-slicing and authorization theorems. Faults 30–40 (Cedar `3971469b`, `913f124d`)
are in code only it reaches: the level checker (30, 31, 37, 39, 40), the entity slicer (32), the
authorizer (33, 34), the policy slicer (35) and the validator (36). Screens:
[`pscreen.txt`](pscreen.txt), [`pscreen2.txt`](pscreen2.txt). Every arm kills 30–35 and 39 within
3.4k tests. 36 is never killed, since a condition built for one environment types alike in the
other. 37 and 40 are deep (60k–146k; 40 only by the byte fuzzer), and a multi-trial run on them is
in progress.
