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

theorem List.arbitrary_support : SPMF.support List.arbitrary = Set.univ := by
  refine (Set.ext ?_)
  intro xs
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

-- TODO: Cost

#guard_msgs(drop info) in
#eval (for _ in [0:20] do
  IO.println <| repr (← List.arbitrary) : IO Unit)

end ArbList
