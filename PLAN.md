# Plan: Mathlib/CSLib Compliance for Basalt

## Context

Basalt needs to meet the coding and documentation standards used by Mathlib4 and CSLib. Both libraries share the same core requirements: copyright headers on every file, module-level docstrings, doc comments on every definition and theorem, no `sorry`s, and consistent naming conventions. CSLib adds one extra requirement: readable proofs (no performance-destroying golf).

The user will write all prose documentation manually. This plan handles everything automatable and produces a `TODO.md` tracking what remains for the user.

---

## Key standards summary

| Requirement | Mathlib/CSLib rule |
|-------------|-------------------|
| Copyright header | Every file: copyright line, license line, authors line |
| Module docstring | `/-! # Title\n\nSummary.\n\n## Main Definitions\n\n## Main Theorems\n-/` |
| Def/theorem docs | `/-- ... -/` on every `def`, `abbrev`, `class`, `instance` (named), `theorem`, `lemma` |
| Naming: theorems | `snake_case` |
| Naming: types/props | `UpperCamelCase` |
| Naming: functions | `lowerCamelCase` |
| `sorry`-free | Master branch must have zero `sorry`s |
| `#eval`/`#check` | Only in example files, wrapped in `#guard_msgs` |
| Line length | Max 100 characters |

---

## Files inventory

All 19 `.lean` files need copyright headers. Below is the current doc status per file:

| File | Module doc | Notes |
|------|-----------|-------|
| `Basalt.lean` | None (has a `--` comment) | Root aggregator |
| `Basalt/Basic.lean` | Yes | Already has narrative background text |
| `Basalt/RandomChoice.lean` | Yes | Well-documented |
| `Basalt/Gen.lean` | None | 0 doc comments at all |
| `Basalt/IO.lean` | None | Tiny file, needs header + doc on instance |
| `Basalt/Classes.lean` | None | 0 doc comments; 4 classes |
| `Basalt/SPMF.lean` | None | Re-export aggregator |
| `Basalt/SPMF/Core.lean` | Yes | ~50% def/theorem coverage |
| `Basalt/SPMF/Support.lean` | Unknown | Needs audit |
| `Basalt/SPMF/Termination.lean` | Unknown | Needs audit |
| `Basalt/SPMF/Cost.lean` | Unknown | Partial coverage confirmed |
| `Basalt/Examples/Basic.lean` | Unknown | Needs audit |
| `Basalt/Examples/ArbNat.lean` | None confirmed | Has `#guard_msgs` + `#eval` (OK) |
| `Basalt/Examples/ArbList.lean` | Unknown | Needs audit |
| `Basalt/Examples/BST.lean` | Unknown | Partial doc confirmed |
| `Basalt/Examples/SortedList.lean` | None | Has 2 `sorry`s |
| `Basalt/Experiments/Mutation.lean` | None confirmed | Needs audit |
| `Basalt/Experiments/Reflective.lean` | Partial | Has 2 `sorry`s |
| `Main.lean` | None | Empty executable entry point |

---

## Steps

### Step 1 — Copyright headers (all files)

Add to the top of every `.lean` file:
```
/-
Copyright (c) 2025 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
```
(User should verify the copyright year against when each file was first written.)

Also create a `LICENSE` file if one doesn't exist (MIT).

### Step 2 — Module docstring skeletons

For each file missing a module docstring, add a skeleton `/-! ... -/` block with the Mathlib-required structure. The user will fill in the content:
```
/-!
# <Title>

<Summary paragraph — fill in>

## Main Definitions

- `Foo` — <fill in>

## Main Theorems

- `foo_bar` — <fill in>
-/
```

Files needing new module docs: `Basalt.lean`, `Gen.lean`, `IO.lean`, `Classes.lean`, `SPMF.lean`,
`Examples/ArbNat.lean`, `Examples/ArbList.lean`, `Examples/BST.lean`, `Examples/SortedList.lean`,
`Experiments/Mutation.lean`, plus any in `SPMF/` submodules found to be missing them.

### Step 3 — Doc comment stubs

For every `def`, `abbrev`, `class`, named `instance`, `theorem`, and `lemma` that currently has
no `/-- -/` doc comment, add a stub:
```lean
/-- TODO: document -/
```
The user fills these in. (Stubs make missing docs explicit and searchable.)

### Step 4 — Mark in-progress `sorry`s

The `sorry`s in `SortedList.lean` and `Reflective.lean` are acknowledged works in progress. Leave
the proofs as-is but ensure they are clearly marked with `-- TODO` comments and wrapped in
`#guard_msgs` so the `sorry` warnings are visible and contained.

### Step 5 — Naming convention audit

Do a pass to catch clear violations:
- Structure/class *field* names: Lean 4 Mathlib convention uses `camelCase` for fields
  (e.g., `isCorrect` not `is_correct`). `Classes.lean` has `is_correct`, `is_ast`,
  `is_cost_bounded` — rename to `isCorrect`, `isAst`, `isCostBounded`.
- Theorem names: verify all are `snake_case` (currently appear correct overall).
- Confirm no `#check` or bare `#eval` outside example files.

---

## What the user will do (after this plan runs)

1. Fill in all `/-- TODO: document -/` stubs in-place (search for `TODO: document`)
2. Fill in all module docstring skeletons (search for `TODO: summarize`)
3. Write `README.md` content (the file exists but is essentially empty)
4. Verify copyright year on each file header
5. Complete the in-progress sorry proofs in `SortedList.lean` and `Reflective.lean`

---

## Critical files

- `Basalt/Classes.lean` — field rename needed
- `Basalt/Examples/SortedList.lean` — sorry completion (user)
- `Basalt/Experiments/Reflective.lean` — sorry completion (user)
- `Basalt/Gen.lean` — fully undocumented
- `Basalt/IO.lean` — fully undocumented

---

## Verification

After implementation:
1. `lake build` — must compile with zero errors and zero warnings about `sorry`.
2. `lean_diagnostic_messages` on each modified file — no new errors.
3. Grep for `sorry` — must only appear inside `#guard_msgs` wrappers.
4. Grep for `TODO: document` and `TODO: summarize` — gives the remaining doc list for the user.
