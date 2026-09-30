/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Cedar.Thm.Validation.Typechecker.And
import Cedar.Thm.Validation.Typechecker.BinaryApp
import Cedar.Thm.Validation.Typechecker.GetAttr
import Cedar.Thm.Validation.Typechecker.HasAttr
import Cedar.Thm.Validation.Typechecker.IfThenElse
import Cedar.Thm.Validation.Typechecker.LUB
import Cedar.Thm.Validation.Typechecker.Or
import Cedar.Thm.Validation.Typechecker.UnaryApp
import Basalt
import BasaltFuzz.Cedar.Typed

/-!
# Cedar's typing judgment: the generator is sound and complete

`CedarTyped.genS caps d` (`BasaltFuzz/Cedar/Typed.lean`) generates boolean Cedar expressions with the
type and output capabilities the *real* `Cedar.Validation.typeOf` assigns them; `genC` does the same at
a non-boolean type. `genS.sound`/`genC.sound`: every result is exactly `typeOf`'s judgment, at every
fuel and capability set. `genS.complete`/`genC.complete`: every fragment (`Frag`) expression `typeOf`
accepts is a result at some fuel, with exactly its judgment — including capability flows through any
guard, `tt`/`ff` short-circuiting, and ill-typed dead branches.
-/

open Cedar Cedar.Data Cedar.Spec Cedar.Validation

namespace CedarTyped

/-- The judgment a `genS` result claims: `typeOf` gives it exactly this boolean type and these output
capabilities. `none` — a branch that could not complete — claims nothing. -/
def SoundS (caps : Capabilities) : Option (Spec.Expr × BoolType × Capabilities) → Prop
  | none => True
  | some (e, b, c) => ∃ tx, typeOf e caps env = .ok (tx, c) ∧ tx.typeOf = .bool b

/-- The judgment a `genC` result at type `ty` claims. -/
def SoundC (caps : Capabilities) (ty : CedarType) : Option (Spec.Expr × Capabilities) → Prop
  | none => True
  | some (e, c) => ∃ tx, typeOf e caps env = .ok (tx, c) ∧ tx.typeOf = ty

theorem finishS_sound (caps : Capabilities) (o : Option Spec.Expr) :
    SoundS caps (o.bind (finishS caps)) := by
  cases o with
  | none => trivial
  | some e =>
    simp only [Option.bind_some, finishS]
    split
    · rename_i tx c h
      split
      · rename_i b hb; exact ⟨tx, h, hb⟩
      · trivial
    · trivial

theorem finishC_sound (caps : Capabilities) (ty : CedarType) (o : Option Spec.Expr) :
    SoundC caps ty (o.bind (finishC caps ty)) := by
  cases o with
  | none => trivial
  | some e =>
    simp only [Option.bind_some, finishC]
    split
    · rename_i tx c h
      split
      · rename_i hty; exact ⟨tx, h, hty⟩
      · trivial
    · trivial

theorem genS.sound : IsSoundFor (genS caps d) (SoundS caps) := by
  intro r hr
  rw [genS] at hr
  support_simp at hr
  obtain ⟨o, _, rfl⟩ := hr
  exact finishS_sound caps o

theorem genC.sound : IsSoundFor (genC caps d ty) (SoundC caps ty) := by
  intro r hr
  rw [genC] at hr
  support_simp at hr
  obtain ⟨o, _, rfl⟩ := hr
  exact finishC_sound caps ty o

/-! ## Completeness

Over the fragment `Frag`: literals, variables, `ite`/`&&`/`||`, `!`/`-`/`is` (at the request's entity
types), `==`/`<`/`<=`/`+`/`-`/`*`, and `has`/`.` at any attribute name. -/

/-- The fragment the generator is complete for. -/
inductive Frag : Spec.Expr → Prop where
  | lit_bool (b : Bool) : Frag (.lit (.bool b))
  | lit_int (i : Int64) : Frag (.lit (.int i))
  | lit_string (s : String) : Frag (.lit (.string s))
  | var (v : Var) : Frag (.var v)
  | ite : Frag a → Frag b → Frag c → Frag (.ite a b c)
  | and : Frag a → Frag b → Frag (.and a b)
  | or : Frag a → Frag b → Frag (.or a b)
  | not : Frag a → Frag (.unaryApp .not a)
  | neg : Frag a → Frag (.unaryApp .neg a)
  | is (ety : EntityType) : ety ∈ entityTypes → Frag a → Frag (.unaryApp (.is ety) a)
  | binaryApp (op : BinaryOp) : op ∈ [BinaryOp.eq, .less, .lessEq, .add, .sub, .mul] →
      Frag a → Frag b → Frag (.binaryApp op a b)
  | hasAttr (attr : Attr) : Frag a → Frag (.hasAttr a attr)
  | getAttr (attr : Attr) : Frag a → Frag (.getAttr a attr)

/-! ### The leaves reach every value -/

theorem Char.toNat_le_max (c : Char) : c.toNat ≤ 0x10FFFF := by
  have h := c.valid
  unfold UInt32.isValidChar Nat.isValidChar at h
  show c.val.toNat ≤ _
  omega

theorem genBool.complete : IsCompleteFor genBool (fun _ => True) := by
  intro b _
  rw [genBool, SPMF.mem_support_iff_may]; walk
  cases b <;> simp

theorem genInt64.complete : IsCompleteFor genInt64 (fun _ => True) := by
  intro i _
  rw [genInt64, SPMF.mem_support_iff_may]; walk
  refine Or.inr ⟨i.toInt, ⟨?_, ?_⟩, Int64.ofInt_toInt i⟩
  · have := Int64.le_toInt i; omega
  · have := Int64.toInt_le i; simp [Int64.maxValue] at this ⊢; omega

theorem genChar.complete : IsCompleteFor genChar (fun _ => True) := by
  intro c _
  rw [genChar, SPMF.mem_support_iff_may]; walk
  exact Or.inr ⟨c.toNat, ⟨Nat.zero_le _, Char.toNat_le_max c⟩, Char.ofNat_toNat c⟩

theorem genString.complete : IsCompleteFor genString (fun _ => True) := by
  intro s _
  rw [genString, SPMF.mem_support_iff_may]
  walk [genChar.complete.obs]
  exact Or.inr ⟨s.toList, by simp, String.ofList_toList⟩

theorem genAttr.complete : IsCompleteFor genAttr (fun _ => True) := by
  intro s _
  rw [genAttr, SPMF.mem_support_iff_may]
  walk [genString.complete.obs]
  simp

/-- The literals of the fragment: booleans, integers, strings. -/
def FragPrim : Prim → Prop
  | .entityUID _ => False
  | _ => True

theorem genPrim.complete : IsCompleteFor genPrim FragPrim := by
  intro p hp
  rw [genPrim, SPMF.mem_support_iff_may]
  walk [genBool.complete.obs, genInt64.complete.obs, genString.complete.obs]
  cases p <;> simp_all [FragPrim]

/-! ### Dead branches: `genAny` reaches every fragment expression -/

theorem genAny.complete : Frag e → ∃ d, e ∈ SPMF.support (genAny d) := by
  intro h
  induction h with
  | lit_bool b =>
    refine ⟨0, ?_⟩; rw [genAny, SPMF.mem_support_iff_may]; walk [genPrim.complete.obs]
    exact ⟨.bool b, trivial, rfl⟩
  | lit_int i =>
    refine ⟨0, ?_⟩; rw [genAny, SPMF.mem_support_iff_may]; walk [genPrim.complete.obs]
    exact ⟨.int i, trivial, rfl⟩
  | lit_string s =>
    refine ⟨0, ?_⟩; rw [genAny, SPMF.mem_support_iff_may]; walk [genPrim.complete.obs]
    exact ⟨.string s, trivial, rfl⟩
  | var v =>
    refine ⟨0, ?_⟩; rw [genAny, SPMF.mem_support_iff_may]; walk
    cases v <;> simp
  | ite _ _ _ iha ihb ihc =>
    obtain ⟨da, ha⟩ := iha; obtain ⟨db, hb⟩ := ihb; obtain ⟨dc, hc⟩ := ihc
    refine ⟨max da (max db dc) + 1, ?_⟩
    rw [genAny, SPMF.mem_support_iff_may]; walk
    exact Or.inr ⟨da, ⟨by omega, by omega⟩, _, ha, db, ⟨by omega, by omega⟩, _, hb,
      dc, ⟨by omega, by omega⟩, _, hc, rfl⟩
  | and _ _ iha ihb =>
    obtain ⟨da, ha⟩ := iha; obtain ⟨db, hb⟩ := ihb
    refine ⟨max da db + 1, ?_⟩
    rw [genAny, SPMF.mem_support_iff_may]; walk
    exact Or.inr ⟨da, ⟨by omega, by omega⟩, _, ha, db, ⟨by omega, by omega⟩, _, hb, rfl⟩
  | or _ _ iha ihb =>
    obtain ⟨da, ha⟩ := iha; obtain ⟨db, hb⟩ := ihb
    refine ⟨max da db + 1, ?_⟩
    rw [genAny, SPMF.mem_support_iff_may]; walk
    exact Or.inr ⟨da, ⟨by omega, by omega⟩, _, ha, db, ⟨by omega, by omega⟩, _, hb, rfl⟩
  | not _ iha =>
    obtain ⟨da, ha⟩ := iha
    refine ⟨da + 1, ?_⟩
    rw [genAny, SPMF.mem_support_iff_may]; walk
    exact Or.inr ⟨_, by simp, da, ⟨by omega, by omega⟩, _, ha, rfl⟩
  | neg _ iha =>
    obtain ⟨da, ha⟩ := iha
    refine ⟨da + 1, ?_⟩
    rw [genAny, SPMF.mem_support_iff_may]; walk
    exact Or.inr ⟨_, by simp, da, ⟨by omega, by omega⟩, _, ha, rfl⟩
  | is ety hety _ iha =>
    obtain ⟨da, ha⟩ := iha
    refine ⟨da + 1, ?_⟩
    rw [genAny, SPMF.mem_support_iff_may]; walk
    exact Or.inr ⟨.is ety, by simp_all [entityTypes], da, ⟨by omega, by omega⟩, _, ha, rfl⟩
  | binaryApp op hop _ _ iha ihb =>
    obtain ⟨da, ha⟩ := iha; obtain ⟨db, hb⟩ := ihb
    refine ⟨max da db + 1, ?_⟩
    rw [genAny, SPMF.mem_support_iff_may]; walk
    exact Or.inr ⟨op, hop, da, ⟨by omega, by omega⟩, _, ha, db, ⟨by omega, by omega⟩, _, hb, rfl⟩
  | hasAttr attr _ iha =>
    obtain ⟨da, ha⟩ := iha
    refine ⟨da + 1, ?_⟩
    rw [genAny, SPMF.mem_support_iff_may]; walk [genAttr.complete.obs]
    exact Or.inr ⟨da, ⟨by omega, by omega⟩, _, ha, attr, rfl⟩
  | getAttr attr _ iha =>
    obtain ⟨da, ha⟩ := iha
    refine ⟨da + 1, ?_⟩
    rw [genAny, SPMF.mem_support_iff_may]; walk [genAttr.complete.obs]
    exact Or.inr ⟨da, ⟨by omega, by omega⟩, _, ha, attr, rfl⟩

/-! ### The typing rules: `candS`/`candC` reach every well-typed fragment expression -/

theorem finishS_of (h : typeOf e caps env = .ok (tx, c)) (hb : tx.typeOf = .bool b) :
    finishS caps e = some (e, b, c) := by
  simp [finishS, h, hb]

theorem finishC_of (h : typeOf e caps env = .ok (tx, c)) (hty : tx.typeOf = ty) :
    finishC caps ty e = some (e, c) := by
  simp [finishC, h, hty]

/-! ### The fragment's types -/

/-- The types a fragment expression can have: a boolean, or one of `valueTypes`. -/
def FragTy (ty : CedarType) : Prop := (∃ b, ty = .bool b) ∨ ty ∈ valueTypes

theorem lub_ctx_addr : (CedarType.record ctxTy ⊔ .record addrTy) = none := by
  decide

theorem lub_addr_ctx : (CedarType.record addrTy ⊔ .record ctxTy) = none := by
  decide

theorem ctx_ne_addr : ctxTy ≠ addrTy := by
  intro h
  have : ctxTy.contains "cReq" = addrTy.contains "cReq" := by rw [h]
  revert this; decide

/-- Least upper bounds among the value types are trivial: two of them have one exactly when they are
equal. A finite check over the seven types. -/
theorem lub_valueTypes : ∀ t₂ ∈ valueTypes, ∀ t₃ ∈ valueTypes,
    (t₂ ⊔ t₃) = (if t₂ = t₃ then some t₂ else none) := by
  intro t₂ h₂ t₃ h₃
  simp only [valueTypes, List.mem_cons, List.not_mem_nil, or_false] at h₂ h₃
  rcases h₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases h₃ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | (simp [Cedar.Thm.lub_refl]; done)
    | (simp [lub?, pType, rType, aType]; done)
    | (simp [lub_ctx_addr, lub_addr_ctx, ctx_ne_addr, ctx_ne_addr.symm]; done)

/-- The schema's record types, canonicalized. -/
theorem ctxTy_eq : ctxTy =
    Map.mk [("cOpt", .optional .int), ("cReq", .required (.bool .anyBool))] := by rfl

theorem addrTy_eq : addrTy =
    Map.mk [("city", .optional .string), ("zip", .required .int)] := by rfl

theorem pAttrs_eq : pAttrs =
    Map.mk [("addr", .optional (.record addrTy)), ("opt", .optional .string),
      ("req", .required .string)] := by rfl

theorem attrs_pType : env.ets.attrs? pType = some pAttrs := by rfl
theorem attrs_rType : env.ets.attrs? rType = some Map.empty := by rfl
theorem attrs_aType : env.ets.attrs? aType = none := by rfl

theorem FragTy.bool : FragTy (.bool b) := Or.inl ⟨b, rfl⟩

theorem lub_bool_value (hv : v ∈ valueTypes) : (CedarType.bool b ⊔ v) = none := by
  simp only [valueTypes, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [lub?]

theorem lub_value_bool (hv : v ∈ valueTypes) : (v ⊔ CedarType.bool b) = none := by
  simp only [valueTypes, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [lub?]

/-- Two fragment types with a least upper bound: both booleans, or one value type twice. -/
theorem lub_fragTy (h₂ : FragTy t₂) (h₃ : FragTy t₃) (h : (t₂ ⊔ t₃) = some t) :
    (∃ b₂ b₃, t₂ = .bool b₂ ∧ t₃ = .bool b₃ ∧ t = .bool (lubBool b₂ b₃)) ∨
      (t ∈ valueTypes ∧ t₂ = t ∧ t₃ = t) := by
  rcases h₂ with ⟨b₂, rfl⟩ | h₂ <;> rcases h₃ with ⟨b₃, rfl⟩ | h₃
  · simp [lub?] at h; exact Or.inl ⟨_, _, rfl, rfl, h.symm⟩
  · simp [lub_bool_value h₃] at h
  · simp [lub_value_bool h₂] at h
  · rw [lub_valueTypes t₂ h₂ t₃ h₃] at h
    split at h
    · simp at h; subst_vars; exact Or.inr ⟨h₂, rfl, rfl⟩
    · simp at h

theorem typeOfHasAttr_bool (h : typeOfHasAttr ty x a caps env = .ok (tx, c)) :
    ∃ b, tx.typeOf = .bool b := by
  unfold typeOfHasAttr at h
  split at h
  · simp only [hasAttrInRecord] at h
    split at h <;> (try split at h) <;> simp [ok, bind, Except.bind] at h <;>
      (obtain ⟨rfl, -⟩ := h; exact ⟨_, rfl⟩)
  · split at h
    · simp only [hasAttrInRecord] at h
      split at h <;> (try split at h) <;> simp [ok, bind, Except.bind] at h <;>
        (obtain ⟨rfl, -⟩ := h; exact ⟨_, rfl⟩)
    · split at h <;> simp [ok, err] at h
      obtain ⟨rfl, -⟩ := h; exact ⟨_, rfl⟩
  · simp [err] at h

theorem typeOf_hasAttr (h : typeOf (.hasAttr x a) caps env = .ok (tx, c)) :
    ∃ tx₁ c₁, typeOf x caps env = .ok (tx₁, c₁) ∧ typeOfHasAttr tx₁ x a caps env = .ok (tx, c) := by
  simp only [typeOf] at h
  cases h₁ : typeOf x caps env with
  | error e => simp [h₁, bind, Except.bind] at h
  | ok p => exact ⟨p.1, p.2, rfl, by simpa [h₁, bind, Except.bind] using h⟩

theorem typeOf_getAttr (h : typeOf (.getAttr x a) caps env = .ok (tx, c)) :
    ∃ tx₁ c₁, typeOf x caps env = .ok (tx₁, c₁) ∧ typeOfGetAttr tx₁ x a caps env = .ok (tx, c) := by
  simp only [typeOf] at h
  cases h₁ : typeOf x caps env with
  | error e => simp [h₁, bind, Except.bind] at h
  | ok p => exact ⟨p.1, p.2, rfl, by simpa [h₁, bind, Except.bind] using h⟩

theorem getAttrInRecord_ty (h : getAttrInRecord ty rty x a caps = .ok (t, c)) :
    ∃ q, (a, q) ∈ rty.toList ∧ t = q.getType := by
  unfold getAttrInRecord at h
  split at h
  · rename_i aty hf; simp [ok] at h
    exact ⟨_, Map.find?_mem_toList hf, by simp [Qualified.getType, h.1]⟩
  · rename_i aty hf; split at h
    · simp [ok] at h; exact ⟨_, Map.find?_mem_toList hf, by simp [Qualified.getType, h.1]⟩
    · simp [err] at h
  · simp [err] at h

/-- Every attribute a fragment base type has is of a fragment type. -/
theorem attr_fragTy (hb : bt ∈ valueTypes)
    (h : typeOfGetAttr tx₁ x a caps env = .ok (tx, c)) (hty : tx₁.typeOf = bt) :
    FragTy tx.typeOf := by
  unfold typeOfGetAttr at h
  simp only [valueTypes, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [hty] at h
  all_goals try simp only [attrs_pType, attrs_rType, attrs_aType] at h
  all_goals first
    | (simp [err] at h; done)
    | skip
  all_goals
    simp only [bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i p hg
      simp [ok] at h
      obtain ⟨rfl, -⟩ := h
      obtain ⟨q, hq, ht⟩ := getAttrInRecord_ty hg
      try rw [ctxTy_eq] at hq
      try rw [pAttrs_eq] at hq
      try rw [addrTy_eq] at hq
      simp only [Map.toList, Map.empty, List.mem_cons, List.not_mem_nil, or_false,
        Prod.mk.injEq] at hq
      all_goals simp only [TypedExpr.typeOf]
      all_goals rw [ht]
      all_goals casesm* _ ∨ _ <;> casesm* _ ∧ _ <;> subst_vars <;>
        first
          | exact FragTy.bool
          | (right; simp [valueTypes, Qualified.getType]; done)
          | (right; simp only [Qualified.getType, valueTypes, List.mem_cons]; simp [← addrTy_eq])

theorem frag_ty (hf : Frag e) :
    ∀ {caps tx c}, typeOf e caps env = .ok (tx, c) → FragTy tx.typeOf := by
  induction hf with
  | lit_bool b =>
    intro caps tx c h
    cases b <;> simp [typeOf, typeOfLit, ok, Function.comp] at h <;> obtain ⟨rfl, -⟩ := h <;>
      exact FragTy.bool
  | lit_int i =>
    intro caps tx c h
    simp [typeOf, typeOfLit, ok, Function.comp] at h; obtain ⟨rfl, -⟩ := h
    right; simp [TypedExpr.typeOf, valueTypes]
  | lit_string s =>
    intro caps tx c h
    simp [typeOf, typeOfLit, ok, Function.comp] at h; obtain ⟨rfl, -⟩ := h
    right; simp [TypedExpr.typeOf, valueTypes]
  | var v =>
    intro caps tx c h
    cases v <;> simp [typeOf, typeOfVar, ok, Function.comp] at h <;> obtain ⟨rfl, -⟩ := h <;>
      right <;> simp [TypedExpr.typeOf, valueTypes, env, act]
  | ite _ _ _ iha ihb ihc =>
    intro caps tx c h
    obtain ⟨tx₁, bty₁, c₁, tx₂, c₂, tx₃, c₃, -, h₁, hty₁, hrest⟩ := Cedar.Thm.type_of_ite_inversion h
    cases bty₁ with
    | ff => obtain ⟨h₃, heq, -⟩ := hrest; rw [heq]; exact ihc h₃
    | tt => obtain ⟨h₂, heq, -⟩ := hrest; rw [heq]; exact ihb h₂
    | anyBool =>
      obtain ⟨h₂, h₃, hlub, -⟩ := hrest
      rcases lub_fragTy (ihb h₂) (ihc h₃) hlub with ⟨_, _, -, -, hb⟩ | ⟨hv, -, -⟩
      · rw [hb]; exact FragTy.bool
      · exact Or.inr hv
  | and _ _ iha ihb =>
    intro caps tx c h
    obtain ⟨tx₁, bty₁, c₁, h₁, hty₁, hrest⟩ := Cedar.Thm.type_of_and_inversion h
    split at hrest
    · obtain ⟨rfl, -⟩ := hrest; rw [hty₁]; exact FragTy.bool
    · obtain ⟨bty, tx₂, bty₂, c₂, rfl, -⟩ := hrest; simp [TypedExpr.typeOf]; exact FragTy.bool
  | or _ _ iha ihb =>
    intro caps tx c h
    obtain ⟨tx₁, bty₁, c₁, h₁, hty₁, hrest⟩ := Cedar.Thm.type_of_or_inversion h
    split at hrest
    · obtain ⟨rfl, -⟩ := hrest; rw [hty₁]; exact FragTy.bool
    · obtain ⟨bty, tx₂, bty₂, c₂, rfl, -⟩ := hrest; simp [TypedExpr.typeOf]; exact FragTy.bool
  | not _ iha =>
    intro caps tx c h
    obtain ⟨-, bty, -, hty, -⟩ := Cedar.Thm.type_of_not_inversion h
    rw [hty]; exact FragTy.bool
  | neg _ iha =>
    intro caps tx c h
    obtain ⟨-, hty, -⟩ := Cedar.Thm.type_of_neg_inversion h
    rw [hty]; right; simp [valueTypes]
  | is ety _ _ iha =>
    intro caps tx c h
    obtain ⟨-, ety', -, hty, -⟩ := Cedar.Thm.type_of_is_inversion h
    rw [hty]; exact FragTy.bool
  | binaryApp op hop _ _ iha ihb =>
    intro caps tx c h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨-, hrest⟩ := Cedar.Thm.type_of_eq_inversion h
      split at hrest
      · split at hrest <;> (rw [hrest]; exact FragTy.bool)
      · obtain ⟨_, _, _, _, _, _, hm⟩ := hrest
        split at hm
        · rw [hm]; exact FragTy.bool
        · rw [hm.1]; exact FragTy.bool
    iterate 2
      · obtain ⟨-, hty, -⟩ := Cedar.Thm.type_of_int_cmp_inversion (by simp) h
        rw [hty]; exact FragTy.bool
    all_goals
      obtain ⟨-, hty, -⟩ := Cedar.Thm.type_of_int_arith_inversion (by simp) h
      rw [hty]; right; simp [valueTypes]
  | hasAttr attr _ iha =>
    intro caps tx c h
    obtain ⟨tx₁, c₁, -, h'⟩ := typeOf_hasAttr h
    obtain ⟨b, hb⟩ := typeOfHasAttr_bool h'
    rw [hb]; exact FragTy.bool
  | getAttr attr _ iha =>
    intro caps tx c h
    obtain ⟨tx₁, c₁, h₁, h'⟩ := typeOf_getAttr h
    rcases iha h₁ with ⟨b, hb⟩ | hv
    · unfold typeOfGetAttr at h'; simp [hb, err] at h'
    · exact attr_fragTy hv h' rfl

/-! ### The main induction -/

/-- `e` is a candidate at its type: a boolean one from `candS`, any other from `candC`. -/
def Reach (caps : Capabilities) (e : Spec.Expr) : CedarType → Prop
  | .bool _ => ∃ d, some e ∈ SPMF.support (candS caps d)
  | ty => ∃ d, some e ∈ SPMF.support (candC caps d ty)

theorem Reach.bool (h : Reach caps e (.bool b)) : ∃ d, some e ∈ SPMF.support (candS caps d) := h

theorem Reach.value (hv : ty ∈ valueTypes) (h : Reach caps e ty) :
    ∃ d, some e ∈ SPMF.support (candC caps d ty) := by
  simp only [valueTypes, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact h

theorem ResultType.typeOf_ok {r : ResultType} (h : r.typeOf = .ok (ty, c)) :
    ∃ tx, r = .ok (tx, c) ∧ tx.typeOf = ty := by
  cases r with
  | error e => simp [ResultType.typeOf, Except.map] at h
  | ok p => simp [ResultType.typeOf, Except.map] at h; exact ⟨p.1, by simp [← h.2], h.1⟩

theorem entity_mem (hv : CedarType.entity ety ∈ valueTypes) : ety ∈ entityTypes := by
  simp [valueTypes, entityTypes] at hv ⊢; exact hv

theorem Frag.lit_prim (h : Frag (.lit p)) : FragPrim p := by
  cases h <;> trivial

theorem not_fragTy_ext : ¬ FragTy (.ext x) := by
  rintro (⟨_, h⟩ | h)
  · cases h
  · simp [valueTypes] at h

theorem Reach.of_value (hv : ty ∈ valueTypes) (h : ∃ d, some e ∈ SPMF.support (candC caps d ty)) :
    Reach caps e ty := by
  simp only [valueTypes, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact h

/-! ### Attribute reads -/

theorem base_value (h : bt ∈ baseTypes) : bt ∈ valueTypes := by
  simp only [baseTypes, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [valueTypes]

/-- An accepted `has` or `.` is applied to a base of one of the `baseTypes`. -/
theorem base_of_fragTy (hf : FragTy ty) (hne : ∀ b, ty ≠ .bool b) (hi : ty ≠ .int)
    (hs : ty ≠ .string) : ty ∈ baseTypes := by
  rcases hf with ⟨b, rfl⟩ | hv
  · exact absurd rfl (hne b)
  · simp only [valueTypes, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [baseTypes]

theorem genRead_cap (hc : (x, Key.attr a) ∈ caps) (hg : getOut caps x a = some t) (hp : p t = true) :
    some (Spec.Expr.getAttr x a) ∈ SPMF.support (genRead caps d p) := by
  have hmem : (Spec.Expr.getAttr x a, t) ∈ capReads caps p := by
    simp only [capReads, List.mem_filterMap]
    exact ⟨(x, .attr a), hc, by simp [hg, hp]⟩
  rw [genRead, SPMF.mem_support_iff_may]; walk
  all_goals first
    | (exfalso; simp_all; done)
    | (refine Or.inl ⟨(Spec.Expr.getAttr x a, t), ?_, rfl⟩; simp_all)
    | (refine ⟨(Spec.Expr.getAttr x a, t), ?_, rfl⟩; simp_all)

theorem genRead_req (hq : (bt, a, t) ∈ requiredAttrs p) (hx : some x ∈ SPMF.support (candC caps d bt))
    (h₁ : typeOf x caps env = .ok (tx₁, c₁)) (hty : tx₁.typeOf = bt) :
    some (Spec.Expr.getAttr x a) ∈ SPMF.support (genRead caps d p) := by
  rw [genRead, SPMF.mem_support_iff_may]; walk
  all_goals first
    | (exfalso; simp_all; done)
    | (refine Or.inr ⟨(bt, a, t), ?_, some x, hx, by simp [finishC_of h₁ hty]⟩; simp_all)
    | (refine ⟨(bt, a, t), ?_, some x, hx, by simp [finishC_of h₁ hty]⟩; simp_all)

/-- An accepted read `x.a` is either of a required attribute of `x`'s type or justified by a
capability in scope, and `getOut` computes its type. -/
theorem read_route (h₁ : typeOf x caps env = .ok (tx₁, c₁))
    (h' : typeOfGetAttr tx₁ x a caps env = .ok (tx, c)) :
    getOut caps x a = some tx.typeOf ∧
      ((a, Qualified.required tx.typeOf) ∈ attrsOf tx₁.typeOf ∨ (x, Key.attr a) ∈ caps) := by
  have hro : ∀ {ty : CedarType} {rty : RecordType} {p : CedarType × Capabilities},
      getAttrInRecord ty rty x a caps = .ok p →
      (a, Qualified.required p.1) ∈ rty.toList ∨ (x, Key.attr a) ∈ caps := by
    intro ty rty p hg
    unfold getAttrInRecord at hg
    split at hg
    · rename_i aty hf; simp [ok] at hg; left; rw [← hg]; exact Map.find?_mem_toList hf
    · split at hg
      · right; assumption
      · simp [err] at hg
    · simp [err] at hg
  unfold typeOfGetAttr at h'
  split at h'
  · rename_i rty hrty
    simp only [bind, Except.bind] at h'
    split at h'
    · simp at h'
    · rename_i p hg
      rw [hrty] at hg
      simp [ok] at h'; obtain ⟨rfl, -⟩ := h'
      show getOut caps x a = some p.1 ∧
        ((a, Qualified.required p.1) ∈ attrsOf tx₁.typeOf ∨ (x, Key.attr a) ∈ caps)
      rw [hrty]
      exact ⟨by simp [getOut, h₁, hrty, hg], hro hg⟩
  · rename_i ety hety
    split at h'
    · rename_i rty hrty
      simp only [bind, Except.bind] at h'
      split at h'
      · simp at h'
      · rename_i p hg
        rw [hety] at hg
        simp [ok] at h'; obtain ⟨rfl, -⟩ := h'
        show getOut caps x a = some p.1 ∧
          ((a, Qualified.required p.1) ∈ attrsOf tx₁.typeOf ∨ (x, Key.attr a) ∈ caps)
        rw [hety]
        refine ⟨by simp [getOut, h₁, hety, hrty, hg], ?_⟩
        simp only [attrsOf, hrty, Option.map_some, Option.getD_some]
        exact hro hg
    · simp [err] at h'
  · simp [err] at h'

set_option maxHeartbeats 4000000 in
theorem reach (hf : Frag e) :
    ∀ {caps tx c}, typeOf e caps env = .ok (tx, c) → Reach caps e tx.typeOf := by
  induction hf with
  | lit_bool b =>
    intro caps tx c h
    cases b <;> simp [typeOf, typeOfLit, ok, Function.comp] at h <;> obtain ⟨rfl, -⟩ := h <;>
      exact ⟨0, by rw [candS, SPMF.mem_support_iff_may]; walk [genBool.complete.obs]; exact ⟨_, rfl⟩⟩
  | lit_int i =>
    intro caps tx c h
    simp [typeOf, typeOfLit, ok, Function.comp] at h; obtain ⟨rfl, -⟩ := h
    refine ⟨0, ?_⟩; simp only [TypedExpr.typeOf]
    rw [candC, SPMF.mem_support_iff_may]; walk [genInt64.complete.obs]; exact ⟨_, rfl⟩
  | lit_string s =>
    intro caps tx c h
    simp [typeOf, typeOfLit, ok, Function.comp] at h; obtain ⟨rfl, -⟩ := h
    refine ⟨0, ?_⟩; simp only [TypedExpr.typeOf]
    rw [candC, SPMF.mem_support_iff_may]; walk [genString.complete.obs]; exact ⟨_, rfl⟩
  | var v =>
    intro caps tx c h
    cases v <;> simp [typeOf, typeOfVar, ok, Function.comp] at h <;> obtain ⟨rfl, -⟩ := h <;>
      exact ⟨0, by
        simp only [TypedExpr.typeOf, env, act]
        rw [candC, SPMF.mem_support_iff_may]; walk
        all_goals simp [pType, rType, aType]⟩
  | @and a b hfa hfb iha ihb =>
    intro caps tx c h
    obtain ⟨tx₁, bty₁, c₁, h₁, hty₁, hrest⟩ := Cedar.Thm.type_of_and_inversion h
    have ra := iha h₁; rw [hty₁] at ra; obtain ⟨da, ha⟩ := ra.bool
    split at hrest
    · rename_i hff; subst hff
      obtain ⟨rfl, -⟩ := hrest
      obtain ⟨db, hb⟩ := genAny.complete hfb
      rw [hty₁]; refine ⟨max da db + 1, ?_⟩
      rw [candS, SPMF.mem_support_iff_may]; walk
      refine Or.inr (Or.inl ⟨da, ⟨by omega, by omega⟩, some a, ha, ?_⟩)
      simp only [Option.bind_some, finishS_of h₁ hty₁]
      exact ⟨db, ⟨by omega, by omega⟩, _, hb, rfl⟩
    · rename_i hnff
      obtain ⟨bty, tx₂, bty₂, c₂, rfl, h₂, hty₂, -⟩ := hrest
      have rb := ihb h₂; rw [hty₂] at rb; obtain ⟨db, hb⟩ := rb.bool
      refine ⟨max da db + 1, ?_⟩
      rw [candS, SPMF.mem_support_iff_may]; walk
      refine Or.inr (Or.inl ⟨da, ⟨by omega, by omega⟩, some a, ha, ?_⟩)
      simp only [Option.bind_some, finishS_of h₁ hty₁]
      cases bty₁
      · exact ⟨db, ⟨by omega, by omega⟩, some b, hb, by simp [finishS_of h₂ hty₂]⟩
      · exact ⟨db, ⟨by omega, by omega⟩, some b, hb, by simp [finishS_of h₂ hty₂]⟩
      · exact absurd rfl hnff
  | @or a b hfa hfb iha ihb =>
    intro caps tx c h
    obtain ⟨tx₁, bty₁, c₁, h₁, hty₁, hrest⟩ := Cedar.Thm.type_of_or_inversion h
    have ra := iha h₁; rw [hty₁] at ra; obtain ⟨da, ha⟩ := ra.bool
    split at hrest
    · rename_i htt; subst htt
      obtain ⟨rfl, -⟩ := hrest
      obtain ⟨db, hb⟩ := genAny.complete hfb
      rw [hty₁]; refine ⟨max da db + 1, ?_⟩
      rw [candS, SPMF.mem_support_iff_may]; walk
      refine Or.inr (Or.inr (Or.inl ⟨da, ⟨by omega, by omega⟩, some a, ha, ?_⟩))
      simp only [Option.bind_some, finishS_of h₁ hty₁]
      exact ⟨db, ⟨by omega, by omega⟩, _, hb, rfl⟩
    · rename_i hntt
      obtain ⟨bty, tx₂, bty₂, c₂, rfl, h₂, hty₂, -⟩ := hrest
      have rb := ihb h₂; rw [hty₂] at rb; obtain ⟨db, hb⟩ := rb.bool
      refine ⟨max da db + 1, ?_⟩
      rw [candS, SPMF.mem_support_iff_may]; walk
      refine Or.inr (Or.inr (Or.inl ⟨da, ⟨by omega, by omega⟩, some a, ha, ?_⟩))
      simp only [Option.bind_some, finishS_of h₁ hty₁]
      cases bty₁
      · exact ⟨db, ⟨by omega, by omega⟩, some b, hb, by simp [finishS_of h₂ hty₂]⟩
      · exact absurd rfl hntt
      · exact ⟨db, ⟨by omega, by omega⟩, some b, hb, by simp [finishS_of h₂ hty₂]⟩
  | @not a hfa iha =>
    intro caps tx c h
    obtain ⟨-, tx₁, ty, c₁, rfl, h₁, bty, rfl, hty₁⟩ := Cedar.Thm.type_of_unary_inversion h
    have ra := iha h₁; rw [hty₁] at ra; obtain ⟨da, ha⟩ := ra.bool
    refine ⟨da + 1, ?_⟩
    rw [candS, SPMF.mem_support_iff_may]; walk
    iterate 6 refine Or.inr ?_
    refine Or.inl ⟨da, ⟨by omega, by omega⟩, some a, ha, ?_⟩
    simp [finishS_of h₁ hty₁]
  | @ite g t e hfg hft hfe ihg iht ihe =>
    intro caps tx c h
    obtain ⟨tx₁, bty₁, c₁, tx₂, c₂, tx₃, c₃, -, h₁, hty₁, hrest⟩ := Cedar.Thm.type_of_ite_inversion h
    have rg := ihg h₁; rw [hty₁] at rg; obtain ⟨dg, hg⟩ := rg.bool
    cases bty₁ with
    | ff =>
      obtain ⟨h₃, heq, -⟩ := hrest
      obtain ⟨dt, ht⟩ := genAny.complete hft
      have re := ihe h₃
      rw [heq]
      rcases frag_ty hfe h₃ with ⟨b, hb⟩ | hv
      · rw [hb] at re ⊢; obtain ⟨de, he⟩ := re.bool
        refine ⟨max dg (max dt de) + 1, ?_⟩
        rw [candS, SPMF.mem_support_iff_may]; walk
        refine Or.inr (Or.inr (Or.inr (Or.inl ⟨dg, ⟨by omega, by omega⟩, some g, hg, ?_⟩)))
        simp only [Option.bind_some, finishS_of h₁ hty₁]
        exact ⟨de, ⟨by omega, by omega⟩, some e, he, by
          simp only [Option.bind_some, finishS_of h₃ hb]
          exact ⟨dt, ⟨by omega, by omega⟩, _, ht, rfl⟩⟩
      · obtain ⟨de, he⟩ := re.value hv
        refine Reach.of_value hv ⟨max dg (max dt de) + 1, ?_⟩
        rw [candC, SPMF.mem_support_iff_may]; walk
        refine Or.inr (Or.inl ⟨dg, ⟨by omega, by omega⟩, some g, hg, ?_⟩)
        simp only [Option.bind_some, finishS_of h₁ hty₁]
        exact ⟨de, ⟨by omega, by omega⟩, some e, he, by
          simp only [Option.bind_some, finishC_of h₃ rfl]
          exact ⟨dt, ⟨by omega, by omega⟩, _, ht, rfl⟩⟩
    | tt =>
      obtain ⟨h₂, heq, -⟩ := hrest
      obtain ⟨de, he⟩ := genAny.complete hfe
      have rt := iht h₂
      rw [heq]
      rcases frag_ty hft h₂ with ⟨b, hb⟩ | hv
      · rw [hb] at rt ⊢; obtain ⟨dt, ht⟩ := rt.bool
        refine ⟨max dg (max dt de) + 1, ?_⟩
        rw [candS, SPMF.mem_support_iff_may]; walk
        refine Or.inr (Or.inr (Or.inr (Or.inl ⟨dg, ⟨by omega, by omega⟩, some g, hg, ?_⟩)))
        simp only [Option.bind_some, finishS_of h₁ hty₁]
        exact ⟨dt, ⟨by omega, by omega⟩, some t, ht, by
          simp only [Option.bind_some, finishS_of h₂ hb]
          exact ⟨de, ⟨by omega, by omega⟩, _, he, rfl⟩⟩
      · obtain ⟨dt, ht⟩ := rt.value hv
        refine Reach.of_value hv ⟨max dg (max dt de) + 1, ?_⟩
        rw [candC, SPMF.mem_support_iff_may]; walk
        refine Or.inr (Or.inl ⟨dg, ⟨by omega, by omega⟩, some g, hg, ?_⟩)
        simp only [Option.bind_some, finishS_of h₁ hty₁]
        exact ⟨dt, ⟨by omega, by omega⟩, some t, ht, by
          simp only [Option.bind_some, finishC_of h₂ rfl]
          exact ⟨de, ⟨by omega, by omega⟩, _, he, rfl⟩⟩
    | anyBool =>
      obtain ⟨h₂, h₃, hlub, -⟩ := hrest
      have rt := iht h₂; have re := ihe h₃
      rcases lub_fragTy (frag_ty hft h₂) (frag_ty hfe h₃) hlub with
        ⟨b₂, b₃, hb₂, hb₃, hb⟩ | ⟨hv, h₂t, h₃t⟩
      · rw [hb]; rw [hb₂] at rt; rw [hb₃] at re
        obtain ⟨dt, ht⟩ := rt.bool; obtain ⟨de, he⟩ := re.bool
        refine ⟨max dg (max dt de) + 1, ?_⟩
        rw [candS, SPMF.mem_support_iff_may]; walk
        refine Or.inr (Or.inr (Or.inr (Or.inl ⟨dg, ⟨by omega, by omega⟩, some g, hg, ?_⟩)))
        simp only [Option.bind_some, finishS_of h₁ hty₁]
        exact ⟨dt, ⟨by omega, by omega⟩, some t, ht, by
          simp only [Option.bind_some, finishS_of h₂ hb₂]
          exact ⟨de, ⟨by omega, by omega⟩, some e, he, by simp [finishS_of h₃ hb₃]⟩⟩
      · rw [h₂t] at rt; rw [h₃t] at re
        obtain ⟨dt, ht⟩ := rt.value hv; obtain ⟨de, he⟩ := re.value hv
        refine Reach.of_value hv ⟨max dg (max dt de) + 1, ?_⟩
        rw [candC, SPMF.mem_support_iff_may]; walk
        refine Or.inr (Or.inl ⟨dg, ⟨by omega, by omega⟩, some g, hg, ?_⟩)
        simp only [Option.bind_some, finishS_of h₁ hty₁]
        exact ⟨dt, ⟨by omega, by omega⟩, some t, ht, by
          simp only [Option.bind_some, finishC_of h₂ h₂t]
          exact ⟨de, ⟨by omega, by omega⟩, some e, he, by simp [finishC_of h₃ h₃t]⟩⟩
  | @neg a hfa iha =>
    intro caps tx c h
    obtain ⟨-, tx₁, ty, c₁, rfl, h₁, hty₁, rfl⟩ := Cedar.Thm.type_of_unary_inversion h
    have ra := iha h₁; rw [hty₁] at ra
    obtain ⟨da, ha⟩ := ra.value (by simp [valueTypes])
    simp only [TypedExpr.typeOf]
    refine Reach.of_value (by simp [valueTypes]) ⟨da + 1, ?_⟩
    rw [candC, SPMF.mem_support_iff_may]; walk
    iterate 4 refine Or.inr ?_
    exact ⟨da, ⟨by omega, by omega⟩, some a, ha, by simp [finishC_of h₁ hty₁]⟩
  | @is a ety hety hfa iha =>
    intro caps tx c h
    obtain ⟨-, tx₁, ty, c₁, rfl, h₁, ety₁, rfl, hty₁⟩ := Cedar.Thm.type_of_unary_inversion h
    have hv := frag_ty hfa h₁; rw [hty₁] at hv
    have hv' : CedarType.entity ety₁ ∈ valueTypes := by
      rcases hv with ⟨_, hb⟩ | hv
      · cases hb
      · exact hv
    have ra := iha h₁; rw [hty₁] at ra
    obtain ⟨da, ha⟩ := ra.value hv'
    refine ⟨da + 1, ?_⟩
    rw [candS, SPMF.mem_support_iff_may]; walk
    iterate 7 refine Or.inr ?_
    refine Or.inl ⟨ety₁, entity_mem hv', ety, hety, da, ⟨by omega, by omega⟩, some a, ha, ?_⟩
    simp [finishC_of h₁ hty₁]
  | @binaryApp a b op hop hfa hfb iha ihb =>
    intro caps tx c h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨-, hrest⟩ := Cedar.Thm.type_of_eq_inversion h
      split at hrest
      · rename_i p₁ p₂ _
        have hp₁ := hfa.lit_prim; have hp₂ := hfb.lit_prim
        have hb : ∃ bt, tx.typeOf = .bool bt := by split at hrest <;> exact ⟨_, hrest⟩
        obtain ⟨bt, hbt⟩ := hb
        rw [hbt]; refine ⟨1, ?_⟩
        rw [candS, SPMF.mem_support_iff_may]; walk [genPrim.complete.obs]
        iterate 12 refine Or.inr ?_
        exact ⟨p₁, hp₁, p₂, hp₂, rfl⟩
      · obtain ⟨ty₁, c₁, ty₂, c₂, h₁, h₂, hm⟩ := hrest
        have ra := iha h₁; have rb := ihb h₂
        split at hm
        · rename_i t hlub
          rw [hm]
          rcases lub_fragTy (frag_ty hfa h₁) (frag_ty hfb h₂) hlub with
            ⟨b₂, b₃, hb₂, hb₃, -⟩ | ⟨hv, h₂t, h₃t⟩
          · rw [hb₂] at ra; rw [hb₃] at rb
            obtain ⟨da, ha⟩ := ra.bool; obtain ⟨db, hb⟩ := rb.bool
            refine ⟨max da db + 1, ?_⟩
            rw [candS, SPMF.mem_support_iff_may]; walk
            iterate 10 refine Or.inr ?_
            refine Or.inl ⟨da, ⟨by omega, by omega⟩, some a, ha, ?_⟩
            simp only [Option.bind_some, finishS_of h₁ hb₂]
            exact ⟨db, ⟨by omega, by omega⟩, some b, hb, by simp [finishS_of h₂ hb₃]⟩
          · rw [h₂t] at ra; rw [h₃t] at rb
            obtain ⟨da, ha⟩ := ra.value hv; obtain ⟨db, hb⟩ := rb.value hv
            refine ⟨max da db + 1, ?_⟩
            rw [candS, SPMF.mem_support_iff_may]; walk
            iterate 9 refine Or.inr ?_
            refine Or.inl ⟨t, hv, da, ⟨by omega, by omega⟩, some a, ha, ?_⟩
            simp only [Option.bind_some, finishC_of h₁ h₂t]
            exact ⟨db, ⟨by omega, by omega⟩, some b, hb, by simp [finishC_of h₂ h₃t]⟩
        · obtain ⟨hm, ety₁, ety₂, he₁, he₂⟩ := hm
          rw [hm]
          have hv₁ := frag_ty hfa h₁; have hv₂ := frag_ty hfb h₂
          rw [he₁] at hv₁ ra; rw [he₂] at hv₂ rb
          have hv₁' : CedarType.entity ety₁ ∈ valueTypes := by
            rcases hv₁ with ⟨_, h⟩ | h
            · cases h
            · exact h
          have hv₂' : CedarType.entity ety₂ ∈ valueTypes := by
            rcases hv₂ with ⟨_, h⟩ | h
            · cases h
            · exact h
          obtain ⟨da, ha⟩ := ra.value hv₁'; obtain ⟨db, hb⟩ := rb.value hv₂'
          refine ⟨max da db + 1, ?_⟩
          rw [candS, SPMF.mem_support_iff_may]; walk
          iterate 11 refine Or.inr ?_
          refine Or.inl ⟨ety₁, entity_mem hv₁', ety₂, entity_mem hv₂', da, ⟨by omega, by omega⟩,
            some a, ha, ?_⟩
          simp only [Option.bind_some, finishC_of h₁ he₁]
          exact ⟨db, ⟨by omega, by omega⟩, some b, hb, by simp [finishC_of h₂ he₂]⟩
    · obtain ⟨-, hty, hops⟩ := Cedar.Thm.type_of_int_cmp_inversion (Or.inl rfl) h
      rw [hty]
      rcases hops with ⟨⟨c₁, h₁⟩, ⟨c₂, h₂⟩⟩ | ⟨⟨c₁, h₁⟩, -⟩ | ⟨⟨c₁, h₁⟩, -⟩
      · obtain ⟨tx₁, h₁, hty₁⟩ := ResultType.typeOf_ok h₁
        obtain ⟨tx₂, h₂, hty₂⟩ := ResultType.typeOf_ok h₂
        have ra := iha h₁; rw [hty₁] at ra; have rb := ihb h₂; rw [hty₂] at rb
        obtain ⟨da, ha⟩ := ra.value (by simp [valueTypes])
        obtain ⟨db, hb⟩ := rb.value (by simp [valueTypes])
        refine ⟨max da db + 1, ?_⟩
        rw [candS, SPMF.mem_support_iff_may]; walk
        iterate 8 refine Or.inr ?_
        refine Or.inl ⟨BinaryOp.less, by simp, da, ⟨by omega, by omega⟩, some a, ha, ?_⟩
        simp only [Option.bind_some, finishC_of h₁ hty₁]
        exact ⟨db, ⟨by omega, by omega⟩, some b, hb, by simp [finishC_of h₂ hty₂]⟩
      all_goals
        obtain ⟨tx₁, h₁, hty₁⟩ := ResultType.typeOf_ok h₁
        have := frag_ty hfa h₁; rw [hty₁] at this; exact absurd this not_fragTy_ext
    · obtain ⟨-, hty, hops⟩ := Cedar.Thm.type_of_int_cmp_inversion (Or.inr rfl) h
      rw [hty]
      rcases hops with ⟨⟨c₁, h₁⟩, ⟨c₂, h₂⟩⟩ | ⟨⟨c₁, h₁⟩, -⟩ | ⟨⟨c₁, h₁⟩, -⟩
      · obtain ⟨tx₁, h₁, hty₁⟩ := ResultType.typeOf_ok h₁
        obtain ⟨tx₂, h₂, hty₂⟩ := ResultType.typeOf_ok h₂
        have ra := iha h₁; rw [hty₁] at ra; have rb := ihb h₂; rw [hty₂] at rb
        obtain ⟨da, ha⟩ := ra.value (by simp [valueTypes])
        obtain ⟨db, hb⟩ := rb.value (by simp [valueTypes])
        refine ⟨max da db + 1, ?_⟩
        rw [candS, SPMF.mem_support_iff_may]; walk
        iterate 8 refine Or.inr ?_
        refine Or.inl ⟨BinaryOp.lessEq, by simp, da, ⟨by omega, by omega⟩, some a, ha, ?_⟩
        simp only [Option.bind_some, finishC_of h₁ hty₁]
        exact ⟨db, ⟨by omega, by omega⟩, some b, hb, by simp [finishC_of h₂ hty₂]⟩
      all_goals
        obtain ⟨tx₁, h₁, hty₁⟩ := ResultType.typeOf_ok h₁
        have := frag_ty hfa h₁; rw [hty₁] at this; exact absurd this not_fragTy_ext
    · obtain ⟨-, hty, ⟨c₁, h₁⟩, ⟨c₂, h₂⟩⟩ := Cedar.Thm.type_of_int_arith_inversion (Or.inl rfl) h
      obtain ⟨tx₁, h₁, hty₁⟩ := ResultType.typeOf_ok h₁
      obtain ⟨tx₂, h₂, hty₂⟩ := ResultType.typeOf_ok h₂
      have ra := iha h₁; rw [hty₁] at ra; have rb := ihb h₂; rw [hty₂] at rb
      obtain ⟨da, ha⟩ := ra.value (by simp [valueTypes])
      obtain ⟨db, hb⟩ := rb.value (by simp [valueTypes])
      rw [hty]
      refine Reach.of_value (by simp [valueTypes]) ⟨max da db + 1, ?_⟩
      generalize hT : CedarType.int = T
      rw [candC, SPMF.mem_support_iff_may]; walk
      iterate 3 refine Or.inr ?_
      refine Or.inl ⟨BinaryOp.add, by simp, da, ⟨by omega, by omega⟩, some a, ha, ?_⟩
      simp only [Option.bind_some, finishC_of h₁ hty₁]
      exact ⟨db, ⟨by omega, by omega⟩, some b, hb, by simp [finishC_of h₂ hty₂]⟩
    · obtain ⟨-, hty, ⟨c₁, h₁⟩, ⟨c₂, h₂⟩⟩ := Cedar.Thm.type_of_int_arith_inversion (Or.inr (Or.inl rfl)) h
      obtain ⟨tx₁, h₁, hty₁⟩ := ResultType.typeOf_ok h₁
      obtain ⟨tx₂, h₂, hty₂⟩ := ResultType.typeOf_ok h₂
      have ra := iha h₁; rw [hty₁] at ra; have rb := ihb h₂; rw [hty₂] at rb
      obtain ⟨da, ha⟩ := ra.value (by simp [valueTypes])
      obtain ⟨db, hb⟩ := rb.value (by simp [valueTypes])
      rw [hty]
      refine Reach.of_value (by simp [valueTypes]) ⟨max da db + 1, ?_⟩
      generalize hT : CedarType.int = T
      rw [candC, SPMF.mem_support_iff_may]; walk
      iterate 3 refine Or.inr ?_
      refine Or.inl ⟨BinaryOp.sub, by simp, da, ⟨by omega, by omega⟩, some a, ha, ?_⟩
      simp only [Option.bind_some, finishC_of h₁ hty₁]
      exact ⟨db, ⟨by omega, by omega⟩, some b, hb, by simp [finishC_of h₂ hty₂]⟩
    · obtain ⟨-, hty, ⟨c₁, h₁⟩, ⟨c₂, h₂⟩⟩ := Cedar.Thm.type_of_int_arith_inversion (Or.inr (Or.inr rfl)) h
      obtain ⟨tx₁, h₁, hty₁⟩ := ResultType.typeOf_ok h₁
      obtain ⟨tx₂, h₂, hty₂⟩ := ResultType.typeOf_ok h₂
      have ra := iha h₁; rw [hty₁] at ra; have rb := ihb h₂; rw [hty₂] at rb
      obtain ⟨da, ha⟩ := ra.value (by simp [valueTypes])
      obtain ⟨db, hb⟩ := rb.value (by simp [valueTypes])
      rw [hty]
      refine Reach.of_value (by simp [valueTypes]) ⟨max da db + 1, ?_⟩
      generalize hT : CedarType.int = T
      rw [candC, SPMF.mem_support_iff_may]; walk
      iterate 3 refine Or.inr ?_
      refine Or.inl ⟨BinaryOp.mul, by simp, da, ⟨by omega, by omega⟩, some a, ha, ?_⟩
      simp only [Option.bind_some, finishC_of h₁ hty₁]
      exact ⟨db, ⟨by omega, by omega⟩, some b, hb, by simp [finishC_of h₂ hty₂]⟩
  | @hasAttr x attr hfx ihx =>
    intro caps tx c h
    obtain ⟨tx₁, c₁, h₁, h'⟩ := typeOf_hasAttr h
    obtain ⟨b, hb⟩ := typeOfHasAttr_bool h'
    rw [hb]
    have hbase : tx₁.typeOf ∈ baseTypes := by
      unfold typeOfHasAttr at h'
      refine base_of_fragTy (frag_ty hfx h₁) ?_ ?_ ?_
      · intro b' heq; rw [heq] at h'; simp [err] at h'
      · intro heq; rw [heq] at h'; simp [err] at h'
      · intro heq; rw [heq] at h'; simp [err] at h'
    obtain ⟨dx, hx⟩ := (ihx h₁).value (base_value hbase)
    refine ⟨dx + 1, ?_⟩
    rw [candS, SPMF.mem_support_iff_may]; walk [genAttr.complete.obs]
    iterate 4 refine Or.inr ?_
    refine Or.inl ⟨tx₁.typeOf, hbase, dx, ⟨by omega, by omega⟩, some x, hx, ?_⟩
    simp [finishC_of h₁ rfl]
  | @getAttr x attr hfx ihx =>
    intro caps tx c h
    obtain ⟨tx₁, c₁, h₁, h'⟩ := typeOf_getAttr h
    have hbase : tx₁.typeOf ∈ baseTypes := by
      have h'' := h'
      unfold typeOfGetAttr at h''
      refine base_of_fragTy (frag_ty hfx h₁) ?_ ?_ ?_
      · intro b' heq; rw [heq] at h''; simp [err] at h''
      · intro heq; rw [heq] at h''; simp [err] at h''
      · intro heq; rw [heq] at h''; simp [err] at h''
    obtain ⟨dx, hx⟩ := (ihx h₁).value (base_value hbase)
    obtain ⟨hget, hroute⟩ := read_route h₁ h'
    have hread : ∀ p : CedarType → Bool, p tx.typeOf = true →
        some (Spec.Expr.getAttr x attr) ∈ SPMF.support (genRead caps dx p) := by
      intro p hp
      rcases hroute with hm | hc
      · refine genRead_req (bt := tx₁.typeOf) (t := tx.typeOf) ?_ hx h₁ rfl
        simp only [requiredAttrs, List.mem_flatMap, List.mem_filterMap]
        exact ⟨_, hbase, _, hm, by simp [hp]⟩
      · exact genRead_cap hc hget hp
    rcases frag_ty (Frag.getAttr attr hfx) h with ⟨b, hb⟩ | hv
    · rw [hb]; refine ⟨dx + 1, ?_⟩
      rw [candS, SPMF.mem_support_iff_may]; walk
      iterate 5 refine Or.inr ?_
      exact Or.inl ⟨dx, ⟨by omega, by omega⟩, hread isBool (by simp [hb, isBool])⟩
    · refine Reach.of_value hv ⟨dx + 1, ?_⟩
      rw [candC, SPMF.mem_support_iff_may]; walk
      exact Or.inr (Or.inr (Or.inl ⟨dx, ⟨by omega, by omega⟩, hread (· == tx.typeOf) (by simp)⟩))

/-! ### Completeness, stated on the generators -/

/-- **Completeness of `genS`.** Every boolean fragment expression the real typechecker accepts under
`caps` is generated, together with exactly the type and output capabilities `typeOf` gives it, at some
fuel. With `genS.sound`, the union over fuel of `genS caps d`'s results is exactly Cedar's typing
judgment on the fragment, at boolean types. -/
theorem genS.complete (hf : Frag e) (h : typeOf e caps env = .ok (tx, c))
    (hb : tx.typeOf = .bool b) : ∃ d, some (e, b, c) ∈ SPMF.support (genS caps d) := by
  have r := reach hf h; rw [hb] at r
  obtain ⟨d, hd⟩ := r.bool
  refine ⟨d, ?_⟩
  rw [genS, SPMF.mem_support_iff_may]; walk
  exact ⟨some e, hd, by simp [finishS_of h hb]⟩

/-- **Completeness of `genC`**, at each of the fragment's non-boolean types. -/
theorem genC.complete (hf : Frag e) (h : typeOf e caps env = .ok (tx, c))
    (hv : tx.typeOf ∈ valueTypes) : ∃ d, some (e, c) ∈ SPMF.support (genC caps d tx.typeOf) := by
  obtain ⟨d, hd⟩ := (reach hf h).value hv
  refine ⟨d, ?_⟩
  rw [genC, SPMF.mem_support_iff_may]; walk
  exact ⟨some e, hd, by simp [finishC_of h rfl]⟩

end CedarTyped

