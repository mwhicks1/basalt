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

noncomputable def List.unfoldBodySPMF (coalg : β → SPMF (ListF α β)) (rec : β → SPMF (List α)) (b : β) : SPMF (List α) := do
  match ← coalg b with
  | .nilStep => return []
  | .consStep x b' => return x :: (← rec b')

lemma ListF.tsum_split {α β : Type} (f : ListF α β → ENNReal) :
    ∑' (step : ListF α β), f step = f ListF.nilStep + ∑' (xb : α × β), f (ListF.consStep xb.1 xb.2) := by
  let e : Option (α × β) ≃ ListF α β := {
    toFun := fun o => match o with
      | none => .nilStep
      | some xb => .consStep xb.1 xb.2
    invFun := fun step => match step with
      | .nilStep => none
      | .consStep x b => some (x, b)
    left_inv := fun o => by cases o <;> rfl
    right_inv := fun step => by cases step <;> rfl
  }
  rw [← e.tsum_eq]
  let e2 : (α × β) ⊕ PUnit.{1} ≃ Option (α × β) := (Equiv.optionEquivSumPUnit (α × β)).symm
  rw [← e2.tsum_eq]
  rw [Summable.tsum_sum ENNReal.summable ENNReal.summable, add_comm]
  congr 1
  · rw [tsum_eq_single PUnit.unit]
    · rfl
    · intro b hb; exact (hb (Subsingleton.elim _ _)).elim

lemma List.unfoldBodySPMF_mass_ge {α β : Type}
    (coalg : β → SPMF (ListF α β)) (rec : β → SPMF (List α)) (b : β)
    (h_coalg_pmf : SPMF.IsPMF (coalg b)) (c : ENNReal) (h_rec_ge : ∀ b', (rec b').mass ≥ c) :
    (List.unfoldBodySPMF coalg rec b).mass ≥
    (coalg b) ListF.nilStep + (1 - (coalg b) ListF.nilStep) * c := by

  let cont : ListF α β → SPMF (List α) := fun step =>
    match step with
    | .nilStep => SPMF.pure []
    | .consStep x b' => rec b' >>= fun xs => SPMF.pure (x :: xs)

  have hbody_eq : List.unfoldBodySPMF coalg rec b = (coalg b).bind cont := by
    unfold List.unfoldBodySPMF SPMF.bind
    congr 1
    ext step
    cases step <;> rfl

  have hmass_nil : (cont ListF.nilStep).mass = 1 := by
    simp only [cont]
    have h : SPMF.pure ([] : List α) = Pure.pure [] := rfl
    rw [h]
    exact SPMF.mass_pure []

  have hmass_cons : ∀ x b', (cont (ListF.consStep x b')).mass = (rec b').mass := fun x b' => by
    simp only [cont]
    exact SPMF.mass_bind_pure

  have hpmf : (coalg b).mass = 1 := h_coalg_pmf

  let lb : ListF α β → ENNReal := fun step =>
    match step with
    | .nilStep => 1
    | .consStep _ _ => c

  have hlb_le : ∀ step, (cont step).mass ≥ lb step := fun step => by
    cases step with
    | nilStep =>
        simp only [lb]
        rw [hmass_nil]
    | consStep x b' =>
        simp only [lb]
        calc (cont (ListF.consStep x b')).mass
          _ = (rec b').mass := hmass_cons x b'
          _ ≥ c := h_rec_ge b'

  rw [hbody_eq]

  calc ((coalg b).bind cont).mass
    _ = ∑' step, (coalg b) step * (cont step).mass := by
        unfold SPMF.mass SPMF.bind
        simp only [DFunLike.coe]
        rw [ENNReal.tsum_comm]
        congr 1
        ext step
        rw [ENNReal.tsum_mul_left]
    _ ≥ ∑' step, (coalg b) step * lb step := by
        apply ENNReal.tsum_le_tsum
        intro step
        exact mul_le_mul_right (hlb_le step) _
    _ = (coalg b) ListF.nilStep * 1 + ∑' (xb : α × β), (coalg b) (ListF.consStep xb.1 xb.2) * c := by
        rw [ListF.tsum_split]
    _ = (coalg b) ListF.nilStep + (∑' (xb : α × β), (coalg b) (ListF.consStep xb.1 xb.2)) * c := by
        rw [mul_one, ENNReal.tsum_mul_right]
    _ = (coalg b) ListF.nilStep + (1 - (coalg b) ListF.nilStep) * c := by
        have htotal : (coalg b) ListF.nilStep + ∑' (xb : α × β), (coalg b) (ListF.consStep xb.1 xb.2) = 1 := by
          rw [← ListF.tsum_split]
          exact hpmf
        have hnil_le_one : (coalg b) ListF.nilStep ≤ 1 := by
          calc (coalg b) ListF.nilStep ≤ (coalg b) ListF.nilStep + ∑' (xb : α × β), (coalg b) (ListF.consStep xb.1 xb.2) := le_self_add
            _ = 1 := htotal
        have hnil_ne_top : (coalg b) ListF.nilStep ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hnil_le_one
        have hcons_eq : ∑' (xb : α × β), (coalg b) (ListF.consStep xb.1 xb.2) = 1 - (coalg b) ListF.nilStep := by
          have := htotal
          rw [← this]
          exact (ENNReal.add_sub_cancel_left hnil_ne_top).symm
        rw [hcons_eq]

theorem List.unfold_IsPMF_of_termination_prob {α β : Type} {p : ENNReal}
    (hp : p > 0) (hp_le_one : p ≤ 1)
    (coalg : β → Gen (ListF α β)) (b : β)
    (h_coalg_pmf : ∀ b, SPMF.IsPMF (coalg b))
    (h_term_prob : ∀ b, (coalg b : SPMF (ListF α β)) ListF.nilStep ≥ p) :
    SPMF.IsPMF (List.unfold coalg b) := by
  haveI : Nonempty β := ⟨b⟩
  apply SPMF.IsPMF_of_positive_termination_prob
    (ι := β)
    (g := fun b' => (List.unfold coalg b' : SPMF (List α)))
    (p := p)
    (term_prob := fun b' => (coalg b' : SPMF (ListF α β)) ListF.nilStep)
    (body_mass := fun b' => ⨅ b'', (List.unfold coalg b'' : SPMF (List α)).mass)
  · exact hp
  · exact hp_le_one
  · exact h_term_prob
  · intro i
    rfl
  · intro i
    have heq : (List.unfold coalg i : SPMF (List α)).mass =
        (List.unfoldBodySPMF (fun b' => (coalg b' : SPMF _)) (fun b' => (List.unfold coalg b' : SPMF _)) i).mass := by
      rw [List.unfold, List.unfoldBodySPMF]
      rfl
    rw [heq]
    apply List.unfoldBodySPMF_mass_ge
    · exact h_coalg_pmf i
    · intro b'
      exact iInf_le _ b'

/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem List.IsPMF_genSorted' (m : Nat) : SPMF.IsPMF (List.genSorted' m) := by
  sorry

end NatListExample
