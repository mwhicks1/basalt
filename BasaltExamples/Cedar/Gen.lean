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

By induction on fuel, one lemma per rule: each rule's result is the helper `typeOf` applies to the
expression it built, given that every sub-result is `typeOf`'s for its subterm.
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

theorem typeOf_binaryApp (ha : typeOf a c env = .ok (ta, ca)) (hb : typeOf b c env = .ok (tb, cb)) :
    typeOf (.binaryApp op a b) c env = typeOfBinaryApp op ta tb a b c env := by
  simp [typeOf, ha, hb]

theorem typeOf_hasAttr (hx : typeOf x c env = .ok (tx, cx)) :
    typeOf (.hasAttr x a) c env = typeOfHasAttr tx x a c env := by
  simp [typeOf, hx]

theorem typeOf_getAttr (hx : typeOf x c env = .ok (tx, cx)) :
    typeOf (.getAttr x a) c env = typeOfGetAttr tx x a c env := by
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

/-! ### Reads, lists, and record literals -/

theorem capRead_eq (h : capReads c t = r :: rs) (hq : q ∈ r :: rs) :
    typeOf (.getAttr q.1 q.2.2) c env = typeOfGetAttr q.2.1 q.1 q.2.2 c env := by
  obtain ⟨cx, hx⟩ := pathTx_sound (mem_capReads (h ▸ hq))
  exact typeOf_getAttr hx

theorem typeOf_set1 (h : SoundO c (some x)) : typeOf (.set [x.e]) c env = typeOfSet [x.tx] :=
  typeOf_set (js := [x]) (fun j hj => by simp at hj; subst hj; exact h)

theorem typeOf_call_str :
    typeOf (.call fn [.lit (.string s)]) c env =
      typeOfCall fn [.lit (.string s) .string] [.lit (.string s)] :=
  typeOf_call (js := [⟨.lit (.string s), .lit (.string s) .string, ∅⟩])
    (fun j hj => by simp at hj; subst hj; simp [Judg, typeOf, typeOfLit, ok])

theorem tagRead_eq (h : tagReads c = r :: rs) (hq : q ∈ r :: rs) :
    typeOf (.binaryApp .getTag q.1 q.2.2.1) c env =
      typeOfBinaryApp .getTag q.2.1 q.2.2.2 q.1 q.2.2.1 c env := by
  obtain ⟨h₁, h₂⟩ := mem_tagReads (h ▸ hq)
  obtain ⟨_, hx⟩ := pathTx_sound h₁
  obtain ⟨_, ht⟩ := pathTx_sound h₂
  exact typeOf_binaryApp hx ht

/-- Every judgment in the list is `typeOf`'s. -/
def SoundL (c : Capabilities) : Option (List J) → Prop
  | none => True
  | some js => ∀ j ∈ js, Judg c j

theorem SoundL.cons (hx : SoundO c (some x)) (hr : SoundL c r) : SoundL c (r.map (x :: ·)) := by
  cases r with
  | none => trivial
  | some js => rintro j (_ | ⟨_, hj⟩); exacts [hx, hr j hj]

/-- Every field's judgment is `typeOf`'s. -/
def SoundF (c : Capabilities) : Option (List (Attr × J)) → Prop
  | none => True
  | some fs => ∀ p ∈ fs, Judg c p.2

theorem SoundF.cons (hx : SoundO c (some x)) (hr : SoundF c r) : SoundF c (r.map ((a, x) :: ·)) := by
  cases r with
  | none => trivial
  | some fs => rintro p (_ | ⟨_, hp⟩); exacts [hx, hr p hp]

/-- A typed record literal `typeOf` gives exactly this typed expression. -/
def SoundR (c : Capabilities) : Option (Spec.Expr × TypedExpr) → Prop
  | none => True
  | some (r, tr) => ∃ cr, typeOf r c env = .ok (tr, cr)

theorem first_sound (ho : SoundO c o) (h : o.map (fun j => [(a, j)]) = some fs) :
    ∀ p ∈ fs, Judg c p.2 := by
  cases o with
  | none => simp at h
  | some j => simp at h; subst h; intro p hp; simp at hp; subst hp; exact ho

theorem rec_sound (h₁ : ∀ p ∈ fs, Judg c p.2) (h₂ : SoundF c (some rest)) :
    SoundR c (some (.record ((fs ++ rest).map fun (a, j) => (a, j.e)),
      .record ((fs ++ rest).map fun (a, j) => (a, j.tx))
        (.record (Map.make ((fs ++ rest).map fun (a, j) => (a, Qualified.required j.tx.typeOf)))))) :=
  ⟨∅, typeOf_record (fs := fs ++ rest) fun p hp => by
    rcases List.mem_append.mp hp with hp | hp
    exacts [h₁ p hp, h₂ p hp]⟩

theorem recHas_eq (h : SoundR c (some (r, tr))) :
    typeOf (.hasAttr r a) c env = typeOfHasAttr tr r a c env :=
  let ⟨_, h⟩ := h; typeOf_hasAttr h

theorem recGet_eq (h : SoundR c (some (r, tr))) :
    typeOf (.getAttr r a) c env = typeOfGetAttr tr r a c env :=
  let ⟨_, h⟩ := h; typeOf_getAttr h

theorem triv_sound (g : SPMF α) : IsSoundFor g (fun _ => True) := fun _ _ => trivial

/-- Closes a rule's leaf: the judgment `ofR e r`, `r` the helper `typeOf` applies to `e`. -/
macro "judg" : tactic => `(tactic| first
  | trivial
  | assumption
  | (simp [SoundL, SoundO]; done)
  | (apply ofR_sound; simp_all [SoundO, Judg, J.res, J.ty, typeOf]; done)
  | (apply ofR_sound; simp_all [SoundO, Judg, J.res, J.ty, typeOf, typeOfAnd, typeOfOr, typeOfIf]; done)
  | (apply ofR_sound; apply capRead_eq (by assumption) (by assumption))
  | (apply ofR_sound; apply typeOf_set1; assumption)
  | (apply ofR_sound; exact typeOf_call_str)
  | (apply ofR_sound; apply tagRead_eq (by assumption) (by assumption))
  | (apply SoundL.cons <;> assumption)
  | (apply SoundF.cons <;> assumption)
  | (apply ofR_sound; apply recHas_eq; assumption)
  | (apply ofR_sound; apply recGet_eq; assumption)
  | (apply ofR_sound; apply typeOf_call; assumption)
  | (apply ofR_sound; apply typeOf_set; assumption)
  | (simp_all [SoundO, Judg, typeOf, ok]; done)
  | (simp; done))

theorem leaf_sound (c : Capabilities) : (t : CedarType) → IsSoundFor (leaf c t) (SoundO c)
  | .set elt => by
    have ih := leaf_sound c elt
    rw [IsSoundFor.iff_obs, leaf]
    walk [ih.obs]
    all_goals judg
  | .bool _ | .int | .string | .entity _ | .record _ | .ext _ => by
    rw [IsSoundFor.iff_obs, leaf]
    walk [(triv_sound CedarTyped.genInt64).obs, (triv_sound CedarTyped.genString).obs]
    all_goals judg

section rules
variable (f : Fam SPMF) (hf : FamSound f)
include hf

theorem ruleAnd_sound : IsSoundFor (ruleAnd f c) (SoundO c) := by
  rw [IsSoundFor.iff_obs, ruleAnd]
  walk [(any_sound f).obs, fun c' => (hf.bool c').obs]
  all_goals judg

theorem ruleOr_sound : IsSoundFor (ruleOr f c) (SoundO c) := by
  rw [IsSoundFor.iff_obs, ruleOr]
  walk [(any_sound f).obs, fun c' => (hf.bool c').obs]
  all_goals judg

theorem ruleIte_sound (hb : ∀ c', IsSoundFor (branch c') (SoundO c')) :
    IsSoundFor (ruleIte f c branch) (SoundO c) := by
  rw [IsSoundFor.iff_obs, ruleIte]
  walk [(any_sound f).obs, fun c' => (hf.bool c').obs, fun c' => (hb c').obs]
  all_goals judg

theorem binary_sound : IsSoundFor (binary f c op t₁ t₂) (SoundO c) := by
  rw [IsSoundFor.iff_obs, binary]
  walk [fun c' t => (hf.atTy c' t).obs]
  all_goals judg

theorem unary_sound : IsSoundFor (unary f c op t) (SoundO c) := by
  rw [IsSoundFor.iff_obs]
  cases t <;> unfold unary <;> walk [fun c' t => (hf.atTy c' t).obs, fun c' => (hf.bool c').obs]
  all_goals judg

theorem ruleHas_sound : IsSoundFor (ruleHas f c) (SoundO c) := by
  rw [IsSoundFor.iff_obs, ruleHas]
  walk [fun c' t => (hf.atTy c' t).obs, (triv_sound CedarWide.genAttr).obs]
  all_goals judg

theorem ruleRead_sound : IsSoundFor (ruleRead f c t) (SoundO c) := by
  rw [IsSoundFor.iff_obs, ruleRead]
  walk [fun c' t => (hf.atTy c' t).obs]
  all_goals judg

theorem call_args_sound : (tys : List CedarType) → IsSoundFor (call.args f c tys) (SoundL c)
  | [] => by rw [IsSoundFor.iff_obs, call.args]; walk; all_goals judg
  | ty :: tys => by
    have ih := call_args_sound (c := c) tys
    rw [IsSoundFor.iff_obs, call.args]
    walk [fun c' t => (hf.atTy c' t).obs, ih.obs]
    all_goals judg

theorem call_sound : IsSoundFor (call f c fn tys) (SoundO c) := by
  rw [IsSoundFor.iff_obs, call]
  walk [(call_args_sound f hf tys).obs]
  all_goals judg

theorem ruleSet_elems_sound : (n : Nat) → IsSoundFor (ruleSet.elems f c elt n) (SoundL c)
  | 0 => by rw [IsSoundFor.iff_obs, ruleSet.elems]; walk; all_goals judg
  | n + 1 => by
    have ih := ruleSet_elems_sound (c := c) (elt := elt) n
    rw [IsSoundFor.iff_obs, ruleSet.elems]
    walk [fun c' t => (hf.atTy c' t).obs, ih.obs]
    all_goals judg

theorem ruleSet_sound : IsSoundFor (ruleSet f c elt) (SoundO c) := by
  rw [IsSoundFor.iff_obs, ruleSet]
  walk [fun n => (ruleSet_elems_sound f hf n).obs]
  all_goals judg

theorem ruleHasTag_sound : IsSoundFor (ruleHasTag f c) (SoundO c) := by
  rw [IsSoundFor.iff_obs, ruleHasTag]
  walk [fun op t₁ t₂ => (binary_sound f hf (c := c) (op := op) (t₁ := t₁) (t₂ := t₂)).obs]
  all_goals judg

theorem ruleExtHas_sound : IsSoundFor (ruleExtHas f c) (SoundO c) := by
  rw [IsSoundFor.iff_obs, ruleExtHas]
  walk [fun c' t => (hf.atTy c' t).obs, fun b n => (triv_sound (genChain b n)).obs]
  all_goals judg

omit hf in
theorem more_sound (field : CedarType → SPMF (Option J)) (pickTy : SPMF CedarType)
    (hfield : ∀ ty, IsSoundFor (field ty) (SoundO c)) :
    (names : List Attr) → (n : Nat) → IsSoundFor (recordLit.more field pickTy names n) (SoundF c)
  | _, 0 => by rw [IsSoundFor.iff_obs, recordLit.more]; walk; all_goals simp [SoundF]
  | names, n + 1 => by
    have ih := fun names => more_sound field pickTy hfield names n
    rw [IsSoundFor.iff_obs, recordLit.more]
    walk [fun ty => (hfield ty).obs, fun names => (ih names).obs, (triv_sound pickTy).obs,
      (triv_sound CedarWide.genAttr).obs]
    all_goals first | judg | simp [SoundF]

theorem recordLit_sound : IsSoundFor (recordLit f c need) (SoundR c) := by
  rw [IsSoundFor.iff_obs]; unfold recordLit
  extract_lets field pickTy
  have hfield : ∀ ty, IsSoundFor (field ty) (SoundO c) := by
    intro ty; simp only [field]; split
    · exact hf.bool c
    · exact hf.atTy c ty
  walk [fun ty => (hfield ty).obs, fun names n => (more_sound field pickTy hfield names n).obs,
    (triv_sound pickTy).obs, (triv_sound CedarWide.genAttr).obs, fun c' => (hf.bool c').obs,
    fun c' t => (hf.atTy c' t).obs]
  all_goals first
    | trivial
    | exact rec_sound (first_sound (by assumption) (by assumption)) (by assumption)

theorem ruleRecordHas_sound : IsSoundFor (ruleRecordHas f c) (SoundO c) := by
  rw [IsSoundFor.iff_obs, ruleRecordHas]
  walk [fun need => (recordLit_sound f hf (c := c) (need := need)).obs,
    (triv_sound CedarWide.genAttr).obs]
  all_goals judg

theorem ruleRecordGet_sound : IsSoundFor (ruleRecordGet f c ty) (SoundO c) := by
  rw [IsSoundFor.iff_obs, ruleRecordGet]
  walk [fun need => (recordLit_sound f hf (c := c) (need := need)).obs,
    (triv_sound CedarWide.genAttr).obs]
  all_goals judg

theorem stepBool_sound : IsSoundFor (stepBool f c) (SoundO c) := by
  rw [IsSoundFor.iff_obs]; unfold stepBool pick
  split <;> simp only [List.append_nil, List.cons_append, List.nil_append]
  all_goals walk [(ruleAnd_sound f hf).obs, (ruleOr_sound f hf).obs,
    (ruleIte_sound f hf (fun c' => hf.bool c')).obs, (ruleHas_sound f hf).obs,
    (ruleHasTag_sound f hf).obs, (ruleExtHas_sound f hf).obs, (ruleRecordHas_sound f hf).obs,
    fun ty => (ruleRecordGet_sound f hf (ty := ty)).obs, fun ty => (ruleRead_sound f hf (t := ty)).obs,
    fun op t => (unary_sound f hf (op := op) (t := t)).obs,
    fun op t₁ t₂ => (binary_sound f hf (op := op) (t₁ := t₁) (t₂ := t₂)).obs,
    fun fn tys => (call_sound f hf (fn := fn) (tys := tys)).obs,
    fun c' => (hf.bool c').obs, (triv_sound CedarTyped.genBool).obs,
    (triv_sound genName).obs, fun n => (triv_sound (genPattern n)).obs, (triv_sound genPrim).obs]
  all_goals judg

theorem stepAt_sound : IsSoundFor (stepAt f c ty) (SoundO c) := by
  rw [IsSoundFor.iff_obs]; unfold stepAt pick construct
  split <;> (try split) <;> (try split) <;> simp only [List.append_nil, List.cons_append, List.nil_append]
  all_goals walk [fun ty => (leaf_sound c ty).obs,
    fun ty => (ruleIte_sound f hf (branch := fun c' => f.atTy c' ty) (fun c' => hf.atTy c' ty)).obs,
    fun ty => (ruleRecordGet_sound f hf (ty := ty)).obs, fun ty => (ruleRead_sound f hf (t := ty)).obs,
    fun elt => (ruleSet_sound f hf (elt := elt)).obs,
    fun op t => (unary_sound f hf (op := op) (t := t)).obs,
    fun op t₁ t₂ => (binary_sound f hf (op := op) (t₁ := t₁) (t₂ := t₂)).obs,
    fun fn tys => (call_sound f hf (fn := fn) (tys := tys)).obs]
  all_goals judg

end rules

theorem fam_sound : (d : Nat) → FamSound (fam (G := SPMF) d)
  | 0 => {
      bool := fun c => by
        rw [fam, IsSoundFor.iff_obs]
        walk [(triv_sound CedarTyped.genBool).obs]
        all_goals judg
      atTy := fun c ty => leaf_sound c ty }
  | d + 1 => {
      bool := fun c => stepBool_sound (fam d) (fam_sound d)
      atTy := fun c ty => stepAt_sound (fam d) (fam_sound d) }

/-- **Soundness.** Every judgment `CedarGen` generates, at any fuel, is exactly the one Cedar's
typechecker derives for its expression, under no capabilities. -/
theorem genS_sound (d : Nat) : IsSoundFor (genS (G := SPMF) d) (SoundO []) :=
  (fam_sound d).bool []

end CedarGen
