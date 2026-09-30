<!--
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-->

# CedarLite: comparing the `FuzzGen` and random backends on a large, well-formed generator

This experiment answers the question "does coverage-guided fuzzing (`FuzzGen`) beat blind random
sampling (`io`/`plausible`) on a *big, well-formed* generator, where reaching a failure means the
generator has to build up real structure?" It does so on a modelled fragment of the
[Cedar policy language](https://github.com/cedar-policy/cedar) — the flagship real-world target the
`BuggyBST` demo cannot stand in for.

The short answer, consistent with `fuzz-run/README.md`'s existing thesis: **which backend wins is a
property of the failure, not the tool.** A well-typed Cedar-expression generator plus a natural
correctness property (a partial-evaluation-vs-evaluation law) yields a *shallow* bug that random
finds faster; only when the failure hides behind several layers of structure the generator produces
rarely does coverage guidance win — and there it wins by ~2 orders of magnitude.

## What is here

- **`BasaltFuzz/Cedar.lean`** (Mathlib-free, so it links into `basalt-fuzz`): the `CedarLite`
  fragment — `Expr`, `Value`, `Prim`, `Error`, `Result`, the evaluator `eval`, a type-directed
  generator `genExpr Γ τ`, a partial evaluator `tpe` modelling `Cedar.TPE`, a buggy variant
  `tpeBuggy`, and the properties.
- **`BasaltExamples/Cedar.lean`** (imports the `Basalt` umbrella + the module above): the inductive
  typing judgment `Typed` and the proof `genExpr.sound_complete : IsSoundAndComplete (genExpr Γ τ)
  (Typed Γ · τ)`. The generator is the single source of truth — defined once, in the fuzz library,
  and proved about here (no second copy, unlike `BasaltFuzz/BuggyBST.lean`).
- Six registered properties in `BasaltFuzzMain.lean` (`cedar-*`).

## Why a modelled subset, not real `cedar-lean`

A self-contained fragment keeps every line of the code under test in the instrumented `BasaltFuzz`
library, so libFuzzer sees its coverage, and makes the generator's `IsSoundAndComplete` proof a
modest exercise against a small inductive judgment. Moving to real `cedar-lean` is future work (see
below).

So `CedarLite` reconstructs a fragment *faithfully*: it keeps Cedar's real constructor names
(`lit`/`var`/`ite`/`and`/`or`/`unaryApp`/`binaryApp`), its `Value`/`Prim`/`Error`/`Result` shapes,
and its **exact short-circuiting `ite`/`and`/`or` and `apply₂` operator semantics** (transcribed from
`Cedar/Spec/Evaluator.lean`). The one deliberate divergence: integer primitives are unbounded `Int`
rather than Cedar's `Int64`, so arithmetic is total (no `arithBoundsError`) — which makes "well-typed
⇒ no evaluation error" a clean, always-true property and lets the generator be *complete* over the
infinite set of integer literals.

Fragment scope: types `bool`/`int`; operators `not`, `neg`, `eq`, `less`, `lessEq`, `add`, `sub`,
`mul`, plus `ite`/`and`/`or`. Omitted vs. Cedar: strings, entities, sets, records, extension
functions, and the attribute/tag operators. Variables are De Bruijn indices into a context, standing
in for Cedar's schema-typed `principal`/`action`/`resource`/`context`.

## What is proved

`genExpr.sound_complete : IsSoundAndComplete (genExpr Γ τ) (Typed Γ · τ)` — the generator's support
is *exactly* the well-typed expressions of type `τ` in `Γ`: nothing ill-typed, nothing missed
(including every integer literal, via a complete-over-ℤ literal generator). This is deliverable #1,
proved with the same `walk`/`SPMF.mem_support_iff_may` recipe as `BasaltExamples/STLC/GenTerm.lean`.

## The properties (all polymorphic in the backend)

| property | expectation |
|---|---|
| `cedar-eval` | a well-typed boolean expression evaluates without a type error (type soundness) — never fails |
| `cedar-tpe` | `eval env (tpe pe e) = eval env e` — the analogue of Cedar's `partial_evaluate_is_sound` — never fails |
| `cedar-buggy-tpe` | the same law for `tpeBuggy`, which folds a statically-`false` `ite` guard to the *then*-branch (swapped branches) — a counterexample exists |
| `cedar-chain-3/4/5` | a staged benchmark (à la `Staged.propChain`): draw `n` expressions, stop unless each is a *nested* `ite` (`≈1/360` each); fails only when all `n` are — the failure hides behind structural depth |

## Results

Single-trial, cold start, on Amazon Linux 2023 (x86_64), `basalt-fuzz -runs=…`. Runs = tested inputs
to first counterexample; lower is better. (Single trials are indicative, not medians — the geometric
spread is wide; see `fuzz-run/compare-backends.sh` for the median methodology.)

**Sanity (never fail):** `cedar-eval` and `cedar-tpe` both pass 200,000 runs under `fuzz` with no
counterexample — the generator only makes well-typed expressions, and the correct partial evaluator
agrees with `eval`.

**Bug-finding — a shallow bug (`cedar-buggy-tpe`):**

| backend | runs to counterexample |
|---|---|
| `fuzz` | 7,294 |
| `io` | 138 |
| `plausible` | 84 |

Random wins by ~50–90×. The swapped-branch optimizer bug fires whenever a foldable-false `ite` guard
sits over two differing branches — structure `genExpr` produces readily, so coverage guidance is pure
overhead. This is the same story as every `bst-buggy-*` bug.

**Bug-finding — a deep, staged failure (`cedar-chain-3`, per-stage gate `≈1/360`):**

| backend | runs to counterexample |
|---|---|
| `fuzz` | 100,514 |
| `io` | 8,735,385 (~87× fuzz) |
| `plausible` | 16,595,039 (~165× fuzz) |

Here **coverage-guided fuzzing wins decisively.** A blind sampler must draw `n` independent
low-probability structures at once (`≈360⁻ⁿ`); the fuzzer banks each newly-reached stage as coverage
and mutates onward, paying roughly `n·360`. This is the regime the question was really about: a
*well-formed* generator whose failures require built-up structure benefits from coverage feedback.

An intermediate note: at a per-stage gate of `≈1/19` (`cedar-chain-4` with a bare-`ite` predicate,
before the nesting change) random still won — Cedar's *natural* structural events are not rare enough
to reach the coverage-dominant regime on their own. The crossover needs the failure to sit behind
gates rarer than a single constructor choice.

## How to reproduce

```sh
fuzz-run/build.sh                                            # build the executable (Mathlib-free link)
fuzz-run/basalt-fuzz cedar-eval       -runs=200000           # passes
fuzz-run/basalt-fuzz cedar-tpe        -runs=200000           # passes
fuzz-run/basalt-fuzz cedar-buggy-tpe  -runs=5000000          # fuzz finds it; random finds it faster
fuzz-run/basalt-fuzz --backend=io       cedar-buggy-tpe
fuzz-run/basalt-fuzz --backend=plausible cedar-buggy-tpe
fuzz-run/basalt-fuzz cedar-chain-3                           # fuzz ~1e5 runs
fuzz-run/basalt-fuzz --backend=io       cedar-chain-3 -runs=100000000   # ~9e6 runs
fuzz-run/basalt-fuzz --backend=plausible cedar-chain-3 -runs=100000000  # ~2e7 runs
```

The `IsSoundAndComplete` proof is checked by `lake build BasaltExamples.Cedar`.

## Limitations and next steps

- **Numbers are single trials.** For a publishable comparison, run each cell as a median-of-N (or a
  fixed-budget success rate) as `fuzz-run/compare-backends.sh` / `compare-grow.sh` do.
- **The chain benchmark is synthetic.** Its per-stage gate is a structural predicate, not a semantic
  bug. A more compelling result would be a *semantic* CedarLite bug (in `eval` or `tpe`) that is only
  reachable behind several distinct operator branches — but note `fuzz-run/README.md`'s caveat that
  coverage is edge-based, so re-entering the same recursive branch does not create new coverage;
  distinct source locations (as `propChain`'s loop provides) are what the fuzzer banks.
- **Real Cedar.** Target the actual `cedar-lean` evaluator and typechecker — including
  capabilities (`e has f && e.f …`) and the `tt`/`ff` types that short-circuit typing, both rare
  under a correct-by-construction generator. Cedar's own code must then be built with the fuzzer's
  coverage flags for the comparison to mean anything.
- The `cedar-buggy-tpe` bug is shallow; a value-level shrinker (Basalt has none) would make its
  counterexamples smaller.
