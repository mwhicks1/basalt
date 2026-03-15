import Basalt
import Basalt.Examples.NatList
import Basalt.Examples.BST

open RandomChoice

namespace NatListExample

theorem Nat.SPMF.IsPMF_arbitrary : SPMF.IsPMF Nat.arbitrary :=
  SPMF.IsPMF_of_positive_termination_prob
      (g := fun () => (Nat.arbitrary : SPMF Nat))
      (p := 1/2) (term_prob := fun () => 1/2)
      (body_mass := fun () => (Nat.arbitrary : SPMF Nat).mass)
      (by norm_num) (by norm_num)
      (fun () => le_refl _)
      (fun () => iInf_le _ ())
      (fun () => by
        conv_lhs => rw [Nat.arbitrary]
        rw [SPMF.mass_pick, SPMF.mass_pure, SPMF.mass_bind_pure, mul_one]
        dsimp only
        have h : (1 : ENNReal) - 1/2 = 1/2 := by norm_num
        rw [h]) ()

theorem List.SPMF.IsPMF_arbitrary : SPMF.IsPMF List.arbitrary :=
  SPMF.IsPMF_of_positive_termination_prob
      (g := fun () => (List.arbitrary : SPMF (List Nat)))
      (p := 1/2) (term_prob := fun () => 1/2)
      (body_mass := fun () => (Nat.arbitrary >>= fun x =>
          (List.arbitrary : SPMF (List Nat)) >>= fun xs => pure (x :: xs)).mass)
      (by norm_num) (by norm_num)
      (fun () => le_refl _)
      (fun () => by
        rw [SPMF.mass_bind_of_const_mass Nat.SPMF.IsPMF_arbitrary
            (fun _ => SPMF.mass_bind_pure)]
        exact iInf_le _ ())
      (fun () => by
        conv_lhs => rw [List.arbitrary]
        rw [SPMF.mass_pick, SPMF.mass_pure, mul_one]
        dsimp only
        have h : (1 : ENNReal) - 1/2 = 1/2 := by norm_num
        rw [h]) ()

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
  apply SPMF.IsPMF_of_positive_termination_prob
    (g := fun n => (List.genSorted n : SPMF (List Nat)))
    (p := 1/2) (term_prob := fun _ => 1/2)
    (body_mass := fun n => (Nat.arbitrary >>= fun d =>
        List.genSorted (n + d) >>= fun xs =>
          pure ((n + d) :: xs) : SPMF (List Nat)).mass)
  · norm_num
  · norm_num
  · intro _; exact le_refl _
  · intro n
    have h_inner_mass : ∀ d, (List.genSorted (n + d) >>= fun xs =>
        pure ((n + d) :: xs) : SPMF (List Nat)).mass =
        (List.genSorted (n + d) : SPMF (List Nat)).mass :=
      fun d => SPMF.mass_bind_pure
    calc (Nat.arbitrary >>= fun d =>
          List.genSorted (n + d) >>= fun xs =>
            pure ((n + d) :: xs) : SPMF (List Nat)).mass
        ≥ 1 * ⨅ j, (List.genSorted j : SPMF (List Nat)).mass :=
          SPMF.mass_bind_ge_mul Nat.SPMF.IsPMF_arbitrary.symm.le
            (fun d => by rw [h_inner_mass]; exact iInf_le _ (n + d))
      _ = ⨅ j, (List.genSorted j : SPMF (List Nat)).mass := one_mul _
  · intro i
    conv_lhs => rw [List.genSorted]
    rw [SPMF.mass_pick, SPMF.mass_pure, mul_one]
    dsimp only
    have h : (1 : ENNReal) - 1/2 = 1/2 := by norm_num
    rw [h]

end NatListExample
