<!--
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-->

# Cedar: generators for its typing judgment, and a coverage experiment

Basalt generators for the *real* [Cedar](https://github.com/cedar-policy/cedar-spec) policy language
(its Lean `Cedar.Spec.Expr`, typechecked by its `Cedar.Validation.typeOf`), and an experiment asking
whether coverage-guided fuzzing (`FuzzGen`) explores Cedar better than random generation (`IO`) when
both drive the same generator.

## The generators (`BasaltFuzz/Cedar/`)

Each generates Cedar expressions together with the type and output capabilities `typeOf` assigns
them, so a guard's capabilities flow wherever `typeOf` sends them (`&&`'s right operand, `if`'s
*then* branch), `true`/`false` guards short-circuit, and dead branches may hold anything, ill-typed or
not.

| module | fragment | how the judgment is obtained | proofs |
|---|---|---|---|
| `Typed.lean` (`CedarTyped`) | literals, variables, `if`/`&&`/`||`, `!`/`-`/`is`, `==`/`<`/`<=`/`+`/`-`/`*`, `has`/`.`, over a small schema | each candidate finished by the real `typeOf` | **sound and complete** (`BasaltExamples/Cedar/Typed.lean`) |
| `Wide.lean` (`CedarWide`) | adds entity/action literals, `in` over hierarchies, tags, sets and set operators, record literals, `like`, multi-attribute `has`, extension functions, over a richer schema | each candidate finished by the real `typeOf`; a failed sub-judgment falls back to a leaf | none |
| `Gen.lean` (`CedarGen`) | `CedarWide`'s fragment and schema | **correct by construction**: no `typeOf` call; each rule combines its sub-results with the typechecker's own per-rule helper (`typeOfAnd`, `typeOfIf`, `typeOfBinaryApp`, `typeOfHasAttr`, `typeOfExtHasAttr`, …), and is offered only where it applies | **sound** (`BasaltExamples/Cedar/Gen.lean`) and **complete** over a scoped fragment (`BasaltExamples/Cedar/GenComplete.lean`) |

`CedarTyped`'s completeness is stated over the fragment `Frag`, for every capability set in scope:
every fragment expression `typeOf` accepts is generated at some fuel, with exactly its judgment.
Literals are complete (every `Int64`, every `String`); completeness is relative to the schema.

`CedarGen`'s soundness (`genS_sound`) says every judgment it returns, at any fuel, is exactly
`typeOf`'s. Its completeness (`genS_complete`) is stated per fuel over the fragment `Scope` (whose
docstring lists the restrictions): at fuel `n`, every boolean fragment expression of fuel `n` that
`typeOf` accepts is generated with exactly its judgment. Dead branches range over all of `Expr`
(`AnyE`), and literals are complete. That the generator never returns `none` is not proved; `gen-cbc`
checks it on every test, together with the judgment's agreement with `typeOf`.

## The Cedar dependency

Cedar is an ordinary git dependency (`lakefile.toml`), built inside this workspace's `.lake`. It pins
Cedar plus two commits, `basalt-integration`, for two things that cannot be done from this side:

- **Six `List` lemmas moved into `Cedar.List`.** Cedar copied them from Mathlib under the same names,
  so without this no file could import both Cedar and Basalt's proof machinery. Cedar's own call sites
  are unchanged, since inside the `Cedar` namespace `List.<name>` resolves to `Cedar.List.<name>`.
- **SanitizerCoverage flags on the `Cedar` library.** Lake gives the root package no way to set a
  dependency's compiler flags; without them libFuzzer sees none of Cedar's code (measured: 3.7× fewer
  Cedar edges).

Cedar's sources otherwise compile unchanged under Basalt's toolchain.

## Running the experiment

```sh
fuzz-run/cedar-experiment.sh                                  # gen-traced, 2 trials × 1M tests
PROP=wide-traced RUNS=200000 TRIALS=3 fuzz-run/cedar-experiment.sh
ARMS="random fuzz-noramp fuzz-grow" fuzz-run/cedar-experiment.sh
```

It builds `basalt-fuzz`, runs every trial of every arm in parallel from one copy of the binary, and
writes `$OUT/curves.html` (coverage and distinct expressions against tests run) plus a table. The arms
share the binary and its instrumentation and differ only in the source of choices:

| arm | choices from |
|---|---|
| `random` | SplitMix, inside libFuzzer's loop (`--backend=io-libfuzzer`), so libFuzzer still counts coverage |
| `fuzz` | libFuzzer's mutated bytes (`FuzzGen`), default settings |
| `fuzz-noramp` | the same, with `-max_len=65536 -len_control=0` |
| `fuzz-grow` | the same, with Basalt's `--grow` |
| `warm-<N>` | a random warm-up of `N` tests, then mutation from its seeds (`--warmup=N`, `fuzz-run/README.md`), otherwise `fuzz-noramp`'s settings |
| `auto-<φ>` | the same, but switching when random's coverage levels off (`--warmup-stall=0 --level=φ`) |
| `back-<φ>` | the same rule in both directions (`--switch-back --level=φ`) |

Coverage is counted per edge by `Basalt/Fuzz/native.c` (`BASALT_COV_OUT`: the first test to hit each
SanitizerCoverage edge), restricted to Cedar's own code by symbol (`lp_Cedar_*`), and excluding
Cedar's printing code, which the traced properties' input hashing runs. Distinct inputs come from the
`BASALT_H` hash each traced property prints per test. `fuzz-run/edge-sets.py` compares the arms' edge
*sets* from the same dumps, which is how a hybrid arm is checked against the union of the others.

### Properties (`BasaltFuzzMain.lean`)

| property | checks |
|---|---|
| `typed-soundness`, `wide-soundness` | Cedar's `type_of_is_sound`: a well-typed expression evaluates to a value of its type, or fails only with `entityDoesNotExist`/`extensionError`/`arithBoundsError` |
| `wide-traced`, `gen-traced` | the same, printing the `BASALT_H` hashes (the experiment's properties) |
| `typed-S-exact`, `typed-C-exact`, `gen-cbc` | the generator's judgment equals `typeOf`'s |
| `wide-env`, `wide-inputs` | the schema is well formed; generated requests and entities conform to it |

`type_of_is_sound` is a proved theorem, so these properties cannot fail; they are vehicles for
exercising the evaluator and typechecker. Measuring bug-finding would need injected faults.

## Findings

Coverage is Cedar SanitizerCoverage edges, mean of 2 trials, at a budget of tests run. Wall-clock per
test is comparable across arms (both run in the same libFuzzer loop).

`gen-traced` (the `CedarGen` generator), 2 trials × 1M tests per arm, Amazon Linux 2023 x86_64:

| tests | random: edges / distinct exprs | fuzz: edges / distinct exprs | fuzz-noramp: edges / distinct exprs |
|---|---|---|---|
| 10 | **2,962** / 9 | 1,530 / 6 | 1,583 / 5 |
| 100 | **4,822** / 104 | 2,884 / 44 | 2,443 / 34 |
| 1,000 | **5,888** / 923 | 3,955 / 315 | 4,085 / 271 |
| 10,000 | **6,464** / 8,095 | 4,871 / 2,180 | 5,554 / 3,549 |
| 100,000 | **6,780** / 85,672 | 6,465 / 43,813 | 6,553 / 46,579 |
| 1,000,000 | 7,006 / 731,314 | **7,069** / 460,937 | 7,013 / 472,838 |

Random covers more until past 100k tests; fuzz passes it by 1M, from 37% fewer distinct expressions:
each input it keeps was chosen for new coverage. The margin is ~60 edges (<1%). Reproduce with
`fuzz-run/cedar-experiment.sh`.

### Random first, then mutation (`--warmup-stall`, `--switch-back`)

The crossover above is the argument for running both in one campaign: random until its coverage levels
off, then mutation from what it found (`fuzz-run/README.md`, "Random warm-up", which owns the switching
rule). `auto-1` is `--warmup-stall=0 --level=1`; `back-1` adds `--switch-back`. `gen-traced`, macOS
arm64 (M-series), 3 trials × 5M tests per arm, one trial per core so that time is comparable:

| tests | random | `fuzz-noramp` | `auto-1` | `back-1` |
|---|---|---|---|---|
| 100,000 | **6,780** ±11 | 6,506 ±69 | 6,763 ±8 | **6,782** ±7 |
| 1,000,000 | 6,988 ±4 | 7,016 ±35 | **7,083** ±4 | **7,076** ±1 |
| 5,000,000 | 7,098 ±4 | **7,198** ±34 | **7,196** ±1 | **7,198** ±10 |

| time | random | `fuzz-noramp` | `auto-1` | `back-1` |
|---|---|---|---|---|
| 1 min | **6,740** | 6,353 | **6,747** | **6,756** |
| 15 min | 7,015 | 7,018 | **7,089** | 7,080 |
| 30 min | 7,061 | 7,107 | **7,144** | 7,130 |
| 55 min (random done) | 7,098 | **7,186** ±31 | **7,182** ±6 | **7,176** ±15 |

- **Until it switches the hybrid *is* random, and after it leads both.** The rule switched at 430k–530k
  tests of the 5M budget (at 115k–128k of a 1M one, in all of 6 trials), and the hybrid led both pure
  arms from there to ~3M tests, ~8 to ~50 minutes. At 1M tests, 6 trials: `auto-1` 7,089 ±9 against
  `fuzz-noramp` 7,027 ±12 and random 6,991 ±6 — the same as the best fixed warm-up (`warm-100000`,
  7,086 ±8), with no budget picked by hand.
- **By 5M tests pure fuzzing has caught up**; the hybrid gets there sooner, and far more consistently
  (±1 against ±34).
- **Pure fuzzing's trials are the more diverse.** Pooled, its 3 trials cover 7,294 edges against the
  hybrid's 7,224 (`fuzz-run/edge-sets.py`): each fuzzing trial wanders somewhere different, while the
  hybrid's start from near-identical random corpora and end up in the same place.
- **Switching back buys nothing here.** It switched 3–5 times in 5M tests — back to random at ~1.1M
  for 20k–40k tests, then fuzzing to the end — and ties `auto-1`. After the first fuzzing phase random
  finds almost nothing the corpus has not already reached.
- **For distinct inputs random wins outright**: 3.5M distinct expressions in 55 minutes, against ~2.0M
  for every fuzzing arm. The fuzzing phase pays only for code coverage, and only at mid-range budgets.
- **`wide-traced` agrees** on the fixed warm-up, at 3 trials × 1M: random 6,465, `fuzz-noramp` 6,516,
  `warm-10000` 6,550, `warm-100000` 6,560.

`fuzz-run/hybrid-experiment.sh` reruns all of this — build, the four arms, and every table above
plus where each trial switched — into one directory; it takes ~75 minutes on 12 cores. Time is from
`BASALT_COV_OUT`'s `.time` file (milliseconds at every 1000th test);
`fuzz-run/budget-table.py` gives both tables, with standard errors, and `fuzz-run/coverage-curves.py`
draws both, with zoomed panels for the tail.

- **Draw order matters to `FuzzGen`.** Its draw order is byte order, so a property must generate the
  thing under test first. With the request and entity store drawn before the expression, their bytes
  (8 per `Int64`) pushed the expression past the end of libFuzzer's short early inputs, where every
  choice reads `0`. Fuzz then produced one distinct expression in its first ~10k tests. Every property
  here now generates the expression first.
- **`--grow` hurts here.** It appends zeros, and in these generators a zero choice is the first branch
  or minimal fuel, so grown inputs decode to repeats (half as many distinct expressions). What does
  help is the other half of what `--grow` switches on: dropping libFuzzer's input-length ramp
  (`fuzz-noramp`).
- **Cedar's typechecker is not monotone in capabilities.** Adding a capability can make a well-typed
  expression ill-typed, so a guard can break a policy that typechecks on its own:

  ```
  e       = (if context.cReq then (principal has opt && !(context has cOpt)) else principal has opt)
              && principal.opt == ""                          -- typechecks
  guarded = context has cOpt && e                             -- rejected: attrNotFound "opt"
  ```

  Under the capability `(context, cOpt)` the *then* branch is statically `false` and outputs no
  capabilities, so the `if`'s output capabilities, `(c₁ ∪ c₂) ∩ c₃`, lose `principal has opt`.
  `guarded` is safe at runtime; the typechecker is only more conservative. It is why `CedarGen` offers
  a capability-justified read only through a path, checked under the capabilities at the read.
- **Fuzz repeats inputs.** Only about a quarter to a half of its tests produce a new expression; most
  byte mutations do not change the decoded term. Random repeats less.
- **What bounds coverage is the property, not the search.** Most of Cedar's code is outside what an
  expression-level soundness property calls: printing, policy-level validation, the authorizer, and
  compiler-generated `match` splitters used only by proofs.
