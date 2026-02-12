import Basalt.Gen
import Basalt.SPMF

open Lean.Order RandomChoice

def CorrectGen (P : Set α) := {g : Gen α // SPMF.support g = P}

namespace Example

inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α

def Tree.isBST (lo hi : Nat) : Tree Nat → Prop
  | leaf => True
  | node l x r =>
    lo ≤ x ∧ x ≤ hi ∧
    l.isBST lo (x - 1) ∧
    r.isBST (x + 1) hi
coinductive_fixpoint

def Tree.isAllTwo : Tree Nat → Prop
  | leaf => True
  | node l x r => x = 2 ∧ l.isAllTwo ∧ r.isAllTwo
coinductive_fixpoint

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
example : CorrectGen Tree.isAllTwo := by
  sorry

end Example
