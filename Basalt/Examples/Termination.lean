import Basalt
import Basalt.Examples.NatList
import Basalt.Examples.BST

open RandomChoice

namespace NatListExample

theorem Nat.SPMF.IsPMF_arbitrary : SPMF.IsPMF Nat.arbitrary := by
  apply SPMF.IsPMF_pick_pure_of_mass_eq
  . rw [Nat.arbitrary]
  . exact SPMF.mass_bind_pure

theorem List.SPMF.IsPMF_arbitrary : SPMF.IsPMF List.arbitrary := by
  apply SPMF.IsPMF_pick_pure_of_mass_eq
  . rw [List.arbitrary]
  . apply SPMF.mass_bind_of_const_mass
    . exact Nat.SPMF.IsPMF_arbitrary
    . exact fun _ => SPMF.mass_bind_pure

theorem List.not_SPMF.IsPMF_diverge : ¬SPMF.IsPMF List.diverge := by
  have : (List.diverge : SPMF (List Nat)).mass = 0 := by
    apply SPMF.mass_eq_zero_of_support_empty
    ext xs
    induction xs <;> rw [List.diverge] <;> simp
    grind
  rw [SPMF.IsPMF, this]
  simp

theorem List.not_SPMF.IsPMF_pick_pure_nil_diverge :
    ¬SPMF.IsPMF (pick (fun () => pure []) (fun () => List.diverge)) := by
  have : (List.diverge : SPMF (List Nat)).mass = 0 := by
    apply SPMF.mass_eq_zero_of_support_empty
    ext xs
    induction xs <;> rw [List.diverge] <;> simp
    grind
  rw [SPMF.IsPMF, SPMF.mass_pick, this, SPMF.mass_pure]
  simp

theorem List.IsPMF_genSorted (m : Nat) : SPMF.IsPMF (List.genSorted m) := by
  apply SPMF.IsPMF_of_half_plus_half_weighted_avg
    (g := fun n => (List.genSorted n : SPMF (List Nat)))
    (body_mass := fun n => (Nat.arbitrary >>= fun d =>
        List.genSorted (n + d) >>= fun xs =>
          pure ((n + d) :: xs) : SPMF (List Nat)).mass)
  . intro n
    have h_inner_mass : ∀ d, (List.genSorted (n + d) >>= fun xs =>
        pure ((n + d) :: xs) : SPMF (List Nat)).mass = (List.genSorted (n + d) : SPMF (List Nat)).mass :=
      fun d => SPMF.mass_bind_pure
    apply SPMF.mass_bind_ge_of_ge Nat.SPMF.IsPMF_arbitrary
    intro d
    rw [h_inner_mass]
    exact iInf_le _ (n + d)
  . intro i
    conv_lhs => rw [List.genSorted]
    rw [SPMF.mass_pick, SPMF.mass_pure]
    ring

end NatListExample

namespace TreeExample

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem Tree.IsPMF_isBST (lo hi : Nat) : SPMF.IsPMF (Tree.genBST lo hi) := by
  sorry

end TreeExample
