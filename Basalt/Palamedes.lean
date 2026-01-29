import Basalt.Gen
import Basalt.SPMF

open Lean.Order

def CorrectGen (P : Set α) := {g : (m : Type → Type) → (∀ α, CCPO (m α)) → m α // (g SPMF inferInstance).support = P}

variable [∀ α, CCPO ((m : Type → Type) → ((α : Type) → CCPO (m α)) → m α)]

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
noncomputable def synth_fix
    [Lean.Order.CompleteLattice (Set α)]
    (f : Set α → Set α)
    (g : ((m : Type → Type) → (∀ α, CCPO (m α)) → m α) → (m : Type → Type) → (∀ α, CCPO (m α)) → m α)
    (h : ∀ (gen : (m : Type → Type) → (∀ α, CCPO (m α)) → m α) (pred : α → Prop),
      (gen SPMF inferInstance).support = pred →
      SPMF.support (g gen SPMF inferInstance) = f pred)
    (h_monotone_f : monotone f)
    (h_monotone_g : monotone g) :
    CorrectGen (lfp f) := by
  refine ⟨fix g h_monotone_g, ?_⟩
  rw [lfp_fix h_monotone_f]
  rw [fix_eq]
  apply h
  sorry

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

variable [∀ α, Lean.Order.CompleteLattice (Set α)]

/--
error: Tactic `apply` failed: failed to assign synthesized instance

inst✝¹ : (α : Type) → CCPO ((m : Type → Type) → ((α : Type) → CCPO (m α)) → m α)
inst✝ : (α : Type) → Lean.Order.CompleteLattice (Set α)
⊢ CorrectGen
    (lfp fun f x =>
      match x with
      | Tree.leaf => True
      | l.node x r => x = 2 ∧ f l ∧ f r)
-/
#guard_msgs in
example : CorrectGen Tree.isAllTwo := by
  delta Tree.isAllTwo
  simp [lfp_monotone]
  apply synth_fix

end Example
