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

def List.genSorted [Gen G] : G (List Nat) := List.genSortedGt 0

def List.genSorted.costBound (xs : List Nat) : Nat :=
  xs.length + 1 + -- Cost of choosing `xs.length` cons-cells and one nil.
  xs.sum + xs.length -- Cost of choosing `xs.length` natural numbers `n`, each of which costs `n + 1`.

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
  simp [genSortedGt_support, List.forall_iff_forall_mem]

theorem List.genSortedGt_terminates (m : Nat) : SPMF.IsPMF (List.genSortedGt m) := by
  refine (SPMF.IsPMF_of_mass_fixpoint
    (g := fun (m : Nat) => (List.genSortedGt m : SPMF (List Nat)))
    (F := fun c => 1 / 2 + 1 / 2 * c)
    ?bounds ?mass) m
  case bounds =>
    intro c hle hge
    simp_all
    apply ENNReal.eq_one_of_fixed_ineq' hle hge
    intro hmono
    rw [ENNReal.toReal_add (by norm_num) (by aesop), ENNReal.toReal_mul] at hmono
    norm_num at hmono; linarith
  case mass =>
    intro m h
    conv_lhs => unfold List.genSortedGt
    simp [SPMF.mass_pick, SPMF.mass_pure]
    gcongr
    apply SPMF.mass_bind_of_mass_one Nat.arbitrary_terminates
    intro x
    simp [SPMF.mass_map]
    exact iInf_le (fun i => SPMF.mass (genSortedGt i)) (m + x)

theorem List.genSorted_terminates : SPMF.IsPMF List.genSorted :=
  List.genSortedGt_terminates 0

theorem List.genSortedGt_cost :
    IsBounded (List.genSortedGt m) (fun xs => xs.length + xs.sum + xs.length + 1) := by
  open Lean.Order in
  delta genSortedGt
  apply (fix_induct (motive := fun (g : Nat → SPMF.Cost (List Nat)) => 
    ∀ m, IsBounded (g m) (fun xs => xs.length + xs.sum + xs.length + 1)) _ ?admissible ?step) m
  case admissible =>
    exact admissible_pi_apply _ fun _ => admissible_IsBounded _
  case step =>
    intro genSortedGt_rec ih m
    simp [IsBounded_iff] at *
    have hnat : ∀ p ∈ (Nat.arbitrary : SPMF.Cost Nat).support,
        p.2 ≤ p.1 + 1 := IsBounded_iff.mp Nat.arbitrary_cost
    intro xs c hxs
    unfold pick at hxs
    simp only [SPMF.Cost.mem_support_bind_iff, SPMF.Cost.mem_support_choose_iff] at hxs
    obtain ⟨k, c1, c2, ⟨_, hk1, rfl⟩, hrest, rfl⟩ := hxs
    split_ifs at hrest with hk
    · simp_all [SPMF.Cost.mem_support_pure_iff]
    · simp only [SPMF.Cost.mem_support_bind_iff, SPMF.Cost.mem_support_pure_iff] at hrest
      grind

theorem List.genSorted_cost :
    IsBounded List.genSorted List.genSorted.costBound :=
  IsBounded_mono List.genSortedGt_cost (by unfold genSorted.costBound; intro xs; omega)

instance : LawfulGenerator List.genSorted List.sorted List.genSorted.costBound where
  support_iff := by simp [List.genSorted_support]
  is_pmf := List.genSorted_terminates
  is_bounded := List.genSorted_cost

end SortedList
