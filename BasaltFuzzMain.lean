/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Basalt.Combinators
import Basalt.Fuzz.Runner
import BasaltFuzz.BuggyBST
import BasaltFuzz.Cedar.Gen
import BasaltFuzz.Staged

/-!
# `basalt-fuzz` executable entry point

Lean owns `main`: `PBT.dispatch` selects a named property and a backend and runs the campaign. This
module and everything it imports must stay Mathlib-free, since the executable links whatever it
imports; it is built by `fuzz-run/build.sh`, never by the default `lake build`.
-/

open Basalt.Fuzz Basalt.PBT RandomChoice

/-- Infrastructure self-test: a deliberately false property. Its failure lives on a distinct branch
(`fail` vs `pass`), so it is reachable by coverage-guided search — libFuzzer hits a byte `≥ 200`
quickly, the counterexample is reported, and the process crashes for libFuzzer to record. -/
def propThreshold [Gen G] : PropM G Unit :=
  forAll (chooseNat 0 255) (· < 200)

/-- The Cedar experiments' properties (`BasaltFuzz/Cedar/`, `CEDAR.md`). Every one draws its Cedar
expression first. A separate list because a list literal this long elaborates without its expected
type and then fails on the `Property` binder. -/
def cedarProperties : List (String × Property) :=
  [ -- the narrow fragment, generator proved sound and complete (`Cedar/Typed.lean`)
    ("typed-S-exact",        fun _ => CedarTyped.prop_genS_exact),
    ("typed-C-exact",        fun _ => CedarTyped.prop_genC_exact),
    ("typed-soundness",      fun _ => CedarTyped.prop_soundness),
    -- the wide fragment, candidates finished by `typeOf` (`Cedar/Wide.lean`)
    ("wide-env",             fun _ => CedarWide.prop_env_wf),
    ("wide-inputs",          fun _ => CedarWide.prop_inputs_ok),
    ("wide-soundness",       fun _ => CedarWide.prop_soundness),
    ("wide-traced",          fun _ => CedarWide.prop_soundness_traced),
    -- the wide fragment, correct by construction (`Cedar/Gen.lean`)
    ("gen-cbc",              fun _ => CedarGen.prop_correct_by_construction),
    ("gen-traced",           fun _ => CedarGen.prop_soundness_traced) ]

/-- The property registry, selected by the first non-flag CLI argument. `bst-*` are the worked BST
demo (`BasaltFuzz/BuggyBST.lean`): the `-buggy-*` ones have real bugs every backend can find,
and the others must never fail. `chain-*` and `long-*` are the staged microbenchmarks
(`BasaltFuzz/Staged.lean`), the one place the backends differ by orders of magnitude;
`long-*` is the one whose difficulty is buffer length, so it is where `--grow` is measured.

Each entry is a `Property`, so one registry serves every backend; `fun _ =>` is the explicit `G`
binder it asks for. -/
def properties : List (String × Property) :=
  ([ ("threshold",            fun _ => propThreshold),
    ("bst-gen",              fun _ => BuggyBST.prop_genBST_isBST),
    ("bst-insert",           fun _ => BuggyBST.prop_insert_preserves_BST),
    ("bst-buggy-insert",     fun _ => BuggyBST.prop_insertBuggy_preserves_BST),
    ("bst-insert2",          fun _ => BuggyBST.prop_insert_two_distinct),
    ("bst-buggy-insert2",    fun _ => BuggyBST.prop_insertBuggy_two_distinct),
    ("bst-delete",           fun _ => BuggyBST.prop_delete_model),
    ("bst-buggy-delete",     fun _ => BuggyBST.prop_deleteBuggy_model),
    ("chain-2",              fun _ => Staged.propChain 2),
    ("chain-3",              fun _ => Staged.propChain 3),
    ("chain-4",              fun _ => Staged.propChain 4),
    ("long-16",              fun _ => Staged.propLong 16),
    ("long-32",              fun _ => Staged.propLong 32),
    ("long-64",              fun _ => Staged.propLong 64) ] : List (String × Property))
    ++ cedarProperties

/-- `dispatch`'s default backend is the first one registered, which is `io` — Basalt's own backends
are registered by the import. This executable is a fuzzer, so it moves `fuzzBackend` to the front
rather than listing the backends: anything else tagged `@[basalt_backend]` is still offered. -/
def main (args : List String) : IO Unit :=
  let (fuzz, others) := (registered_backends% : List Backend).partition (·.name == fuzzBackend.name)
  dispatch "basalt-fuzz" properties args (fuzz ++ others)
