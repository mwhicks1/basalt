import Basalt
import Basalt.Examples.ArbNat

open RandomChoice ArbNat

namespace SortedList

def List.genSortedGt [Gen G] (m : Nat) : G (List Nat) := do
  pick
    (fun () => pure [])
    (fun () => do
      let delta ← Nat.arbitrary
      let x := m + delta
      let xs ← List.genSortedGt x
      return x :: xs)
partial_fixpoint

def List.genSorted [Gen G] : G (List Nat) := do
  let m ← Nat.arbitrary
  List.genSortedGt m

def List.genSorted.costBound (xs : List Nat) : Nat :=
  xs.length + 1 + -- Cost of choosing `xs.length` cons-cells and one nil.
  xs.sum + xs.length + -- Cost of choosing `xs.length` natural numbers `n`, each of which costs `n + 1`.
  xs.head?.elim 0 (· + 1) -- Cost of choosing the head of the list `m` (if it exists), which again costs `m + 1`.

def List.sorted (xs : List Nat) : Prop :=
  match xs with
  | [] => True
  | [_] => True
  | x :: y :: xs => x <= y ∧ List.sorted (y :: xs)

-- TODO: Complete these sorrys
/-- warning: declaration uses `sorry` -/
#guard_msgs in
instance : LawfulGenerator List.genSorted List.sorted List.genSorted.costBound where
  is_correct := sorry
  is_ast := sorry
  is_cost_bounded := sorry

end SortedList
