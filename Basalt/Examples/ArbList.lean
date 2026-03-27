import Basalt
import Basalt.Examples.ArbNat

open RandomChoice ArbNat

namespace ArbList

def List.arbitrary [Gen G] : G (List Nat) := do
  pick
    (fun () => pure [])
    (fun () => do
      let x ← Nat.arbitrary
      let xs ← List.arbitrary
      return x :: xs)
partial_fixpoint

theorem List.arbitrary_support : xs ∈ SPMF.support List.arbitrary := by
  induction xs <;> rw [List.arbitrary]
  case _ => simp
  case _ x xs ih => simp [ih, Nat.arbitrary_support]

theorem List.arbitrary_terminates : SPMF.IsPMF List.arbitrary := by
  refine (SPMF.IsPMF_of_mass_fixpoint
    (g := fun () => (List.arbitrary : SPMF (List Nat)))
    (F := fun c => 1 / 2 + 1 / 2 * c)
    ?bounds ?mass) ()
  case bounds =>
    intro c hle hge
    simp_all
    apply ENNReal.eq_one_of_fixed_ineq hle _ hge
    . intro hmono hle'
      rw [ENNReal.toReal_add (by norm_num) (by aesop), ENNReal.toReal_mul] at hmono
      norm_num at hmono; linarith
    . aesop
  case mass =>
    intro () h
    conv_lhs => rw [List.arbitrary]
    have := Nat.arbitrary_terminates
    simp [SPMF.mass_pick, SPMF.mass_pure]
    gcongr
    apply le_trans _ (SPMF.mass_bind_ge_mul Nat.arbitrary_terminates.symm.le (fun x => SPMF.mass_map.symm.le))
    simp

theorem List.arbitrary_cost :
    IsBounded List.arbitrary (fun xs => 2 * xs.length + xs.sum + 1) := by
  open Lean.Order in
  delta arbitrary
  apply fix_induct (motive := fun (g : SPMF.Cost (List Nat)) =>
    IsBounded g (fun xs => 2 * xs.length + xs.sum + 1)) _ ?admissible ?step
  case admissible =>
    apply admissible_IsBounded
  case step =>
    intro arbitrary_rec ih
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

instance : LawfulGenerator List.arbitrary ⊤ (fun xs => 2 * xs.length + xs.sum + 1) where
  support_iff := by simp [List.arbitrary_support]
  is_pmf := List.arbitrary_terminates
  is_bounded := List.arbitrary_cost

#guard_msgs(drop info) in
#eval (for _ in [0:20] do
  IO.println <| repr (← List.arbitrary) : IO Unit)

end ArbList
