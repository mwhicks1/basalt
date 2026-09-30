/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Cedar.Thm.Data.List.Lemmas
import Basalt
import BasaltFuzz.Cedar.Gen

/-!
# `CedarGen` is sound: every judgment it generates is exactly `typeOf`'s
-/

open Cedar Cedar.Data Cedar.Spec Cedar.Validation
open CedarWide (env)

namespace CedarGen

/-- The judgment is exactly the one `typeOf` derives. -/
def Judg (c : Capabilities) (j : J) : Prop := typeOf j.e c env = .ok (j.tx, j.out)

/-- A result claims its judgment; `none` claims nothing. -/
def SoundO (c : Capabilities) : Option J → Prop
  | none => True
  | some j => Judg c j

/-- Every judgment a fuel level of the family returns is `typeOf`'s. -/
structure FamSound (f : Fam SPMF) : Prop where
  bool : ∀ c, IsSoundFor (f.bool c) (SoundO c)
  atTy : ∀ c ty, IsSoundFor (f.atTy c ty) (SoundO c)

theorem ofR_sound (h : typeOf e c env = r) : SoundO c (ofR e r) := by
  cases r with
  | error _ => trivial
  | ok p => exact h

theorem any_sound (f : Fam SPMF) : IsSoundFor f.any (fun _ => True) := fun _ _ => trivial

/-! ### `typeOf`, one constructor at a time -/

theorem typeOf_and (ha : typeOf a c env = .ok (ta, ca)) :
    typeOf (.and a b) c env = typeOfAnd (ta, ca) (typeOf b (c ∪ ca) env) := by
  simp [typeOf, ha]

theorem typeOf_or (ha : typeOf a c env = .ok (ta, ca)) :
    typeOf (.or a b) c env = typeOfOr (ta, ca) (typeOf b c env) := by
  simp [typeOf, ha]

theorem typeOf_ite (hg : typeOf g c env = .ok (tg, cg)) :
    typeOf (.ite g t e) c env = typeOfIf (tg, cg) (typeOf t (c ∪ cg) env) (typeOf e c env) := by
  simp [typeOf, hg]

theorem typeOf_unaryApp (hx : typeOf x c env = .ok (tx, cx)) :
    typeOf (.unaryApp op x) c env = typeOfUnaryApp op tx := by
  simp [typeOf, hx]

theorem typeOf_binaryApp (ha : typeOf a c env = .ok (ta, ca)) (hb : typeOf b c env = .ok (tb, cb)) :
    typeOf (.binaryApp op a b) c env = typeOfBinaryApp op ta tb a b c env := by
  simp [typeOf, ha, hb]

theorem typeOf_hasAttr (hx : typeOf x c env = .ok (tx, cx)) :
    typeOf (.hasAttr x a) c env = typeOfHasAttr tx x a c env := by
  simp [typeOf, hx]

theorem typeOf_getAttr (hx : typeOf x c env = .ok (tx, cx)) :
    typeOf (.getAttr x a) c env = typeOfGetAttr tx x a c env := by
  simp [typeOf, hx]

theorem typeOf_extHasAttr (hx : typeOf x c env = .ok (tx, cx)) :
    typeOf (.extHasAttr x a as) c env =
      (do let r ← typeOfExtHasAttr tx x (a :: as) c env
          ok (TypedExpr.extHasAttr tx a as (.bool r.1)) r.2) := by
  simp [typeOf, hx]

theorem mapM_justType {js : List J} (h : ∀ j ∈ js, Judg c j) :
    (js.map J.e).mapM (fun x => justType (typeOf x c env)) = .ok (js.map J.tx) := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    have hj : typeOf j.e c env = .ok (j.tx, j.out) := h j (by simp)
    simp only [List.map_cons, List.mapM_cons, ih (fun j' hj' => h j' (by simp [hj']))]
    simp [hj, justType, Except.map, bind, Except.bind, pure, Except.pure]

theorem typeOf_set {js : List J} (h : ∀ j ∈ js, Judg c j) :
    typeOf (.set (js.map J.e)) c env = typeOfSet (js.map J.tx) := by
  rw [typeOf, List.mapM₁_eq_mapM (fun x => justType (typeOf x c env)), mapM_justType h]; rfl

theorem typeOf_call {js : List J} (h : ∀ j ∈ js, Judg c j) :
    typeOf (.call fn (js.map J.e)) c env = typeOfCall fn (js.map J.tx) (js.map J.e) := by
  rw [typeOf, List.mapM₁_eq_mapM (fun x => justType (typeOf x c env)), mapM_justType h]; rfl

theorem mapM_fields {fs : List (Attr × J)} (h : ∀ p ∈ fs, Judg c p.2) :
    (fs.map fun p => (p.1, p.2.e)).mapM
        (fun p => (typeOf p.2 c env).map fun r => (p.1, r.1)) =
      .ok (fs.map fun p => (p.1, p.2.tx)) := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
    have hp : typeOf p.2.e c env = .ok (p.2.tx, p.2.out) := h p (by simp)
    simp only [List.map_cons, List.mapM_cons, ih (fun p' hp' => h p' (by simp [hp']))]
    simp [hp, Except.map, bind, Except.bind, pure, Except.pure]

theorem typeOf_record {fs : List (Attr × J)} (h : ∀ p ∈ fs, Judg c p.2) :
    typeOf (.record (fs.map fun p => (p.1, p.2.e))) c env =
      .ok (.record (fs.map fun p => (p.1, p.2.tx))
             (.record (Map.make (fs.map fun p => (p.1, Qualified.required p.2.tx.typeOf)))), ∅) := by
  rw [typeOf]
  refine (congrArg (· >>= _) (List.mapM₂_eq_mapM
    (fun p : Attr × Spec.Expr => (typeOf p.2 c env).map fun r => (p.1, r.1)) _)).trans ?_
  rw [mapM_fields h]
  simp [ok, List.map_map, Function.comp_def]

/-! ### Paths -/

theorem pathTx_sound : pathTx c x = some tx → ∃ cx, typeOf x c env = .ok (tx, cx) := by
  fun_induction pathTx c x generalizing tx <;> intro h
  all_goals try (simp at h; done)
  case case1 hv => cases h; exact ⟨_, by rw [typeOf, hv]⟩
  case case3 hv => cases h; exact ⟨_, by rw [typeOf, hv]⟩
  case case5 p a ih =>
    cases hp : pathTx c p with
    | none => simp [hp] at h
    | some tp =>
      obtain ⟨cp, hcp⟩ := ih hp
      simp only [hp, Option.bind_eq_bind, Option.bind_some] at h
      split at h
      · rename_i t cx hg; cases h; exact ⟨cx, by rw [typeOf_getAttr hcp, hg]⟩
      · simp at h

theorem mem_capReads (h : q ∈ capReads c ty) : pathTx c q.1 = some q.2.1 := by
  simp only [capReads, List.mem_filterMap] at h
  obtain ⟨⟨x, k⟩, -, hk⟩ := h
  cases k with
  | tag t => simp at hk
  | attr a =>
    simp only at hk
    split at hk
    · rename_i tx hx
      split at hk
      · split at hk
        · simp at hk; subst hk; exact hx
        · simp at hk
      · simp at hk
    · simp at hk

theorem mem_tagReads (h : q ∈ tagReads c) : pathTx c q.1 = some q.2.1 ∧ pathTx c q.2.2.1 = some q.2.2.2 := by
  simp only [tagReads, List.mem_filterMap] at h
  obtain ⟨⟨x, k⟩, -, hk⟩ := h
  cases k with
  | attr a => simp at hk
  | tag t =>
    simp only at hk
    split at hk
    · rename_i tx tt hx ht
      split at hk
      · split at hk
        · simp at hk; subst hk; exact ⟨hx, ht⟩
        · simp at hk
      · simp at hk
    · simp at hk

/-! ### A singleton guard never looks at the dead side -/

theorem typeOfAnd_ff (h : tx.typeOf = .bool .ff) : typeOfAnd (tx, c₁) r = typeOfAnd (tx, c₁) r' := by
  simp [typeOfAnd, h]

theorem typeOfOr_tt (h : tx.typeOf = .bool .tt) : typeOfOr (tx, c₁) r = typeOfOr (tx, c₁) r' := by
  simp [typeOfOr, h]

theorem typeOfIf_tt (h : tx.typeOf = .bool .tt) : typeOfIf (tx, c₁) r₂ r₃ = typeOfIf (tx, c₁) r₂ r₃' := by
  simp [typeOfIf, h]

theorem typeOfIf_ff (h : tx.typeOf = .bool .ff) : typeOfIf (tx, c₁) r₂ r₃ = typeOfIf (tx, c₁) r₂' r₃ := by
  simp [typeOfIf, h]

theorem ty_eq_of_beq {j : J} (h : (j.ty == t) = true) : j.tx.typeOf = t := by
  simpa [J.ty] using h

theorem ruleAnd_sound (f : Fam SPMF) (hf : FamSound f) : IsSoundFor (ruleAnd f c) (SoundO c) := by
  rw [IsSoundFor.iff_obs, ruleAnd]
  walk [(any_sound f).obs, fun c' => (hf.bool c').obs]
  all_goals first
    | trivial
    | (rename_i a ha hff _ _
       apply ofR_sound
       rw [typeOf_and ha]; exact typeOfAnd_ff (ty_eq_of_beq hff))
    | (rename_i a ha _ b hb
       apply ofR_sound
       rw [typeOf_and ha, hb]; rfl)

end CedarGen
