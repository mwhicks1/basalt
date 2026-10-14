/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Lean.Elab.ElabRules

/-!
# Harvesting a fuzz target's literals

`harvested_literals% A B …` elaborates to the `Array Nat` of the natural-number literals in every
definition in namespaces `A`, `B`, …: the constants the choice backend's mutator may plant in a draw.
A `Nat` comparison compiles to a comparison of tagged pointers, which SanitizerCoverage's `trace-cmp`
does not instrument, so the program's own literals are the only source of these constants.
-/

open Lean Elab Term

namespace Basalt.Fuzz

/-- The `Nat` literals below `2^64` in `e`, added to `acc`. -/
partial def natLits (e : Expr) (acc : Std.HashSet Nat) : Std.HashSet Nat :=
  match e with
  | .lit (.natVal n) => if n < 2 ^ 64 then acc.insert n else acc
  | .app f a => natLits a (natLits f acc)
  | .lam _ t b _ | .forallE _ t b _ => natLits b (natLits t acc)
  | .letE _ t v b _ => natLits b (natLits v (natLits t acc))
  | .mdata _ b | .proj _ _ b => natLits b acc
  | _ => acc

/-- Elaborates to the distinct `Nat` literals, below `2^64`, in the definitions under the given
namespaces. -/
elab "harvested_literals% " nss:ident* : term => do
  let env ← getEnv
  let prefixes := nss.map (·.getId)
  let mut seen : Std.HashSet Nat := {}
  for (name, info) in env.constants.toList do
    unless prefixes.any (·.isPrefixOf name) do continue
    let some v := info.value? | continue
    seen := natLits v seen
  let sorted := seen.toArray.qsort (· < ·)
  return mkApp2 (mkConst ``List.toArray [Level.zero]) (mkConst ``Nat)
    (sorted.foldr (fun n acc => mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``Nat)
      (mkRawNatLit n) acc) (mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Nat)))

end Basalt.Fuzz
