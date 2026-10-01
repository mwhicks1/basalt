/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import BasaltExamples.Cedar.GenCases

/-!
# `CedarGen` is complete over a scoped fragment
-/

open Cedar Cedar.Data Cedar.Spec Cedar.Validation
open CedarWide (env)
open CedarTyped (genBool genInt64 genString genChar)

namespace CedarGen

/-- **Completeness**, for every capability set: every fragment expression `typeOf` accepts is
generated, with exactly `typeOf`'s judgment, at its fuel. -/
theorem reach (hs : Scope c e n) :
    ∀ {tx out}, typeOf e c env = .ok (tx, out) → ReachF (fam n) c ⟨e, tx, out⟩ := by
  induction hs with
  | lit p n => exact reach_lit
  | var v n => exact reach_var
  | @and c a n b _ hab _ iha ihb =>
    intro tx out h
    obtain ⟨t₁, b₁, c₁, h₁, hb₁, hrest⟩ := Cedar.Thm.type_of_and_inversion h
    have hm₁ := (iha h₁).bool (b := b₁) hb₁
    have h' := h; rw [typeOf_and' h₁] at h'
    split at hrest
    · obtain ⟨rfl, rfl⟩ := hrest
      rename_i hff; subst hff
      refine reach_bool hb₁ ?_
      rw [fam_succ_bool]; apply stepBool_and
      have hd : typeOfAnd (tx, c₁) dead = .ok (tx, ∅) := by simp [typeOfAnd, hb₁, ok]
      rw [← ofR_ok hd]
      exact ruleAnd_ff (fam n) hm₁ hb₁ (fam_any ▸ genAny_complete hab)
    · rename_i hff
      obtain ⟨bty, t₂, b₂, c₂, rfl, h₂, hb₂, -⟩ := hrest
      have hm₂ := (ihb t₁ c₁ h₁ (by rw [hb₁]; simpa using hff) h₂).bool hb₂
      refine reach_bool (b := bty) rfl ?_
      rw [fam_succ_bool]; apply stepBool_and
      rw [h₂] at h'
      rw [← ofR_ok h']
      exact ruleAnd_both (fam n) hm₁ (by simpa [J.ty, hb₁] using hff) hm₂
  | @or c a n b _ hab _ iha ihb =>
    intro tx out h
    obtain ⟨t₁, b₁, c₁, h₁, hb₁, hrest⟩ := Cedar.Thm.type_of_or_inversion h
    have hm₁ := (iha h₁).bool (b := b₁) hb₁
    have h' := h; rw [typeOf_or' h₁] at h'
    split at hrest
    · obtain ⟨rfl, rfl⟩ := hrest
      rename_i htt; subst htt
      refine reach_bool hb₁ ?_
      rw [fam_succ_bool]; apply stepBool_or
      have hd : typeOfOr (tx, c₁) dead = .ok (tx, ∅) := by simp [typeOfOr, hb₁, ok]
      rw [← ofR_ok hd]
      exact ruleOr_tt (fam n) hm₁ hb₁ (fam_any ▸ genAny_complete hab)
    · rename_i htt
      obtain ⟨bty, t₂, b₂, c₂, rfl, h₂, hb₂, -⟩ := hrest
      have hm₂ := (ihb t₁ c₁ h₁ (by rw [hb₁]; simpa using htt) h₂).bool hb₂
      refine reach_bool (b := bty) rfl ?_
      rw [fam_succ_bool]; apply stepBool_or
      rw [h₂] at h'
      rw [← ofR_ok h']
      exact ruleOr_both (fam n) hm₁ (by simpa [J.ty, hb₁] using htt) hm₂
  | @ite c x₁ n x₂ x₃ _ hat hae _ _ hok ihg iht ihe =>
    intro tx out h
    obtain ⟨t₁, b₁, c₁, t₂, c₂, t₃, c₃, -, h₁, hb₁, hrest⟩ := Cedar.Thm.type_of_ite_inversion h
    have hm₁ := (ihg h₁).bool hb₁
    have h' := h; rw [typeOf_ite' h₁] at h'
    have hu := hok tx out h
    cases b₁ with
    | tt =>
      obtain ⟨h₂, hty, rfl⟩ := hrest
      have r₂ := iht t₁ c₁ h₁ (by rw [hb₁]; simp) h₂
      rw [h₂] at h'
      have hk : typeOfIf (t₁, c₁) (J.res ⟨x₂, t₂, c₂⟩) dead = .ok (tx, c₁ ∪ c₂) := by
        rw [← h']; simp [typeOfIf, hb₁, J.res]
      rcases hu with ⟨bt, hbt⟩ | ⟨hv, hi⟩
      · refine reach_bool hbt ?_; rw [fam_succ_bool]; apply stepBool_ite
        rw [← ofR_ok hk]
        exact ruleIte_tt (fam n) hm₁ hb₁ (r₂.bool (hty ▸ hbt)) (fam_any ▸ genAny_complete hae)
      · refine reach_val hv hi ?_; rw [fam_succ_atTy]; apply stepAt_ite
        rw [← ofR_ok hk]
        have := r₂.value (by simpa [J.ty, ← hty] using hv)
        simp only [J.ty, ← hty] at this
        exact ruleIte_tt (fam n) (branch := fun c' => (fam n).atTy c' tx.typeOf) hm₁ hb₁ this
          (fam_any ▸ genAny_complete hae)
    | ff =>
      obtain ⟨h₃, hty, rfl⟩ := hrest
      have r₃ := ihe t₁ c₁ h₁ (by rw [hb₁]; simp) h₃
      rw [h₃] at h'
      have hk : typeOfIf (t₁, c₁) dead (J.res ⟨x₃, t₃, out⟩) = .ok (tx, out) := by
        rw [← h']; simp [typeOfIf, hb₁, J.res]
      rcases hu with ⟨bt, hbt⟩ | ⟨hv, hi⟩
      · refine reach_bool hbt ?_; rw [fam_succ_bool]; apply stepBool_ite
        rw [← ofR_ok hk]
        exact ruleIte_ff (fam n) hm₁ hb₁ (r₃.bool (hty ▸ hbt)) (fam_any ▸ genAny_complete hat)
      · refine reach_val hv hi ?_; rw [fam_succ_atTy]; apply stepAt_ite
        rw [← ofR_ok hk]
        have := r₃.value (by simpa [J.ty, ← hty] using hv)
        simp only [J.ty, ← hty] at this
        exact ruleIte_ff (fam n) (branch := fun c' => (fam n).atTy c' tx.typeOf) hm₁ hb₁ this
          (fam_any ▸ genAny_complete hat)
    | anyBool =>
      obtain ⟨h₂, h₃, hlub, rfl⟩ := hrest
      have r₂ := iht t₁ c₁ h₁ (by rw [hb₁]; simp) h₂
      have r₃ := ihe t₁ c₁ h₁ (by rw [hb₁]; simp) h₃
      rw [h₂, h₃] at h'
      have hk : typeOfIf (t₁, c₁) (J.res ⟨x₂, t₂, c₂⟩) (J.res ⟨x₃, t₃, c₃⟩) =
          .ok (tx, (c₁ ∪ c₂) ∩ c₃) := h'
      rcases lub_U r₂.tyU r₃.tyU hlub with ⟨⟨b₂, hb₂⟩, ⟨b₃, hb₃⟩, ⟨bt, hbt⟩⟩ | ⟨hv, hty₂, hty₃⟩
      · refine reach_bool hbt ?_; rw [fam_succ_bool]; apply stepBool_ite
        rw [← ofR_ok hk]
        exact ruleIte_any (fam n) hm₁ (by simp [J.ty, hb₁]) (by simp [J.ty, hb₁]) (r₂.bool hb₂)
          (r₃.bool hb₃)
      · have hi : inhabited c tx.typeOf = true := by
          rcases hu with ⟨b, hb⟩ | ⟨_, hi⟩
          · rw [hb] at hv; exact absurd hv bool_not_value
          · exact hi
        refine reach_val hv hi ?_; rw [fam_succ_atTy]; apply stepAt_ite
        rw [← ofR_ok hk]
        have m₂ := r₂.value (by rw [hty₂]; exact hv)
        have m₃ := r₃.value (by rw [hty₃]; exact hv)
        rw [hty₂] at m₂; rw [hty₃] at m₃
        exact ruleIte_any (fam n) (branch := fun c' => (fam n).atTy c' tx.typeOf) hm₁
          (by simp [J.ty, hb₁]) (by simp [J.ty, hb₁]) m₂ m₃
  | _ => sorry

end CedarGen
