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

/-! ### Record literals, from typing -/

theorem mapM_fields_inv : (fs : List (Attr × Spec.Expr)) → (atys : List (Attr × TypedExpr)) →
    (fs.mapM fun p => (typeOf p.2 c env).map fun r => (p.1, r.1)) = .ok atys →
    ∃ js : List (Attr × J), js.map (fun p => (p.1, p.2.e)) = fs ∧
      js.map (fun p => (p.1, p.2.tx)) = atys ∧ ∀ p ∈ js, Judg c p.2
  | [], atys, h => by
    simp [pure, Except.pure] at h; subst h; exact ⟨[], rfl, rfl, by simp⟩
  | (a, x) :: fs, atys, h => by
    simp only [List.mapM_cons] at h
    cases hx : typeOf x c env with
    | error e => simp [hx, Except.map, bind, Except.bind] at h
    | ok p =>
      obtain ⟨tx, cx⟩ := p
      cases hr : fs.mapM (fun p => (typeOf p.2 c env).map fun r => (p.1, r.1)) with
      | error e => rw [hr] at h; simp [hx, Except.map, bind, Except.bind] at h
      | ok tys =>
        rw [hr] at h; simp [hx, Except.map, bind, Except.bind, pure, Except.pure] at h
        subst h
        obtain ⟨js, h₁, h₂, h₃⟩ := mapM_fields_inv fs tys hr
        refine ⟨(a, ⟨x, tx, cx⟩) :: js, by simp [h₁], by simp [h₂], ?_⟩
        rintro p (_ | ⟨_, hp⟩)
        exacts [hx, h₃ p hp]

theorem record_inv (h : typeOf (.record fs) c env = .ok (tr, cr)) :
    ∃ js : List (Attr × J), js.map (fun p => (p.1, p.2.e)) = fs ∧ (∀ p ∈ js, Judg c p.2) ∧
      recordOf js = (.record fs, tr) := by
  simp only [typeOf] at h
  have key := List.mapM₂_eq_mapM (m := Except TypeError)
    (fun p : Attr × Spec.Expr => (typeOf p.2 c env).map fun r => (p.1, r.1)) fs
  have h2 : (do
      let atys ← fs.mapM (fun p => (typeOf p.2 c env).map fun r => (p.1, r.1))
      ok (TypedExpr.record atys
        (.record (Map.make (atys.map fun x => (x.1, Qualified.required x.2.typeOf)))))) =
      (Except.ok (tr, cr) : ResultType) := by
    rw [← key]; exact h
  cases hm : fs.mapM (fun p => (typeOf p.2 c env).map fun r => (p.1, r.1)) with
  | error e => rw [hm] at h2; simp [bind, Except.bind] at h2
  | ok atys =>
    rw [hm] at h2; simp [bind, Except.bind, ok] at h2
    obtain ⟨rfl, -⟩ := h2
    obtain ⟨js, h₁, h₂, h₃⟩ := mapM_fields_inv fs atys hm
    refine ⟨js, h₁, h₃, ?_⟩
    subst h₁ h₂
    simp [recordOf, List.map_map, Function.comp_def]

theorem fields_reach {js : List (Attr × J)} (hjs : js.map (fun p => (p.1, p.2.e)) = fs)
    (hj : ∀ p ∈ js, Judg c p.2)
    (ih : ∀ p ∈ fs, ∀ {tx out}, typeOf p.2 c env = .ok (tx, out) →
      ReachF (fam (G := SPMF) n) c ⟨p.2, tx, out⟩) :
    ∀ p ∈ js, ReachF (fam (G := SPMF) n) c p.2 := fun p hp =>
  ih (p.1, p.2.e) (hjs ▸ List.mem_map_of_mem hp) (hj p hp)

theorem names_eq {js : List (Attr × J)} (hjs : js.map (fun p => (p.1, p.2.e)) = fs) :
    js.map Prod.fst = fs.map Prod.fst := by
  subst hjs; simp [Function.comp_def]

theorem reach_hasRec (hl : fs.length ≤ n) (hnd : (fs.map Prod.fst).Nodup)
    (ih : ∀ p ∈ fs, ∀ {tx out}, typeOf p.2 c env = .ok (tx, out) →
      ReachF (fam (G := SPMF) n) c ⟨p.2, tx, out⟩) :
    typeOf (.hasAttr (.record fs) a) c env = .ok (tx, out) →
    ReachF (fam (G := SPMF) (n + 1)) c ⟨.hasAttr (.record fs) a, tx, out⟩ := by
  intro h
  obtain ⟨-, tr, cr, h₁, -, -⟩ := Cedar.Thm.type_of_hasAttr_inversion h
  obtain ⟨js, hjs, hj, hrec⟩ := record_inv h₁
  have h' := h; rw [typeOf_hasAttr h₁] at h'
  obtain ⟨b, hb⟩ := typeOfHasAttr_bool h'
  have hm := ruleRecordHas_complete (fam n) (fs := js) (a := a)
    (by rw [fam_fuel]; have := congrArg List.length hjs; simp at this; omega)
    (names_eq hjs ▸ hnd) (fields_reach hjs hj ih)
  rw [hrec] at hm
  rw [ofR_ok (e := .hasAttr (.record fs) a) h'] at hm
  refine reach_bool hb ?_
  rw [fam_succ_bool]; step_bool
  all_goals (nth_or 7; exact hm)

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
