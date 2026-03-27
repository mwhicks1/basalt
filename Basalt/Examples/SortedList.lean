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

lemma List.sorted_cons_forall_le : List.sorted (x :: xs) → List.Forall (x ≤ ·) xs := by
  intro h
  induction xs
  case _ => simp
  case _ x xs ih => grind [= sorted.eq_def, sorted, List.forall_cons]

theorem List.genSortedGt_support (xs : List Nat) (m : Nat) :
    xs ∈ SPMF.support (List.genSortedGt m) ↔ (List.sorted xs ∧ List.Forall (m ≤ ·) xs) := by
  fun_induction List.sorted generalizing m
  case _ =>
    unfold genSortedGt
    simp
  case _ x =>
    unfold genSortedGt
    simp
    constructor
    . grind
    . intro h
      exists x - m
      apply And.intro Nat.arbitrary_support
      constructor
      . unfold genSortedGt
        simp
      . grind
  case _ x y xs ih =>
    unfold genSortedGt
    simp only [bind_pure_comp, SPMF.support_pick, SPMF.support_pure, SPMF.support_bind,
      SPMF.support_map, Set.mem_setOf_eq, Set.singleton_union, Set.mem_insert_iff, reduceCtorEq,
      List.cons.injEq, exists_eq_right_right', false_or, List.Forall, List.forall_cons]
    constructor
    . intro h
      replace ⟨a, _, h, heq⟩ := h
      subst heq
      grind only [List.forall_iff_forall_mem, List.forall_cons]
    . intro h
      replace ⟨h, hx, hy, hxs⟩ := h
      exists x - m
      grind only [
        List.forall_iff_forall_mem, List.Forall.eq_def, List.Forall.imp, List.sorted_cons_forall_le,
        sorted.eq_def, Nat.arbitrary_support]

theorem List.genSorted_support (xs : List Nat) :
    xs ∈ SPMF.support List.genSorted ↔ List.sorted xs := by
  unfold genSorted
  simp [genSortedGt_support]
  constructor
  . grind
  . intro h
    exists 0
    constructor
    . simp [Nat.arbitrary_support]
    . apply And.intro h
      simp [List.forall_iff_forall_mem]

-- TODO: Complete these sorrys
/-- warning: declaration uses `sorry` -/
#guard_msgs in
instance : LawfulGenerator List.genSorted List.sorted List.genSorted.costBound where
  support_iff := by simp [List.genSorted_support]
  is_pmf := sorry
  is_bounded := sorry

end SortedList
