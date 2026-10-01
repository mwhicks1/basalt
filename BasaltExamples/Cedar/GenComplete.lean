/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import BasaltExamples.Cedar.Gen
import BasaltExamples.Cedar.Typed

/-!
# `CedarGen` is complete over a scoped fragment
-/

open Cedar Cedar.Data Cedar.Spec Cedar.Validation
open CedarWide (env)
open CedarTyped (genBool genInt64 genString genChar)

namespace CedarGen

/-! ## The leaves -/

theorem genListUpTo_complete {g : SPMF α} {P : α → Prop} (hg : IsCompleteFor g P) :
    (n : Nat) → (xs : List α) → xs.length ≤ n → (∀ x ∈ xs, P x) → xs ∈ (genListUpTo (G := SPMF) g n).support
  | 0, [], _, _ => by rw [genListUpTo, SPMF.mem_support_iff_may]; walk
  | n + 1, [], _, _ => by rw [genListUpTo, SPMF.mem_support_iff_may]; walk
  | n + 1, x :: xs, hl, hp => by
    have ih := genListUpTo_complete hg n xs (by simp at hl; omega) (fun y hy => hp y (by simp [hy]))
    rw [genListUpTo, SPMF.mem_support_iff_may]; walk [hg.obs]
    exact ⟨x, hp x (by simp), xs, ih, rfl⟩

theorem genAttr_complete : IsCompleteFor CedarWide.genAttr (fun _ => True) := by
  intro s _
  rw [CedarWide.genAttr, SPMF.mem_support_iff_may]
  walk [CedarTyped.genString.complete.obs]
  simp

theorem genName_complete : IsCompleteFor genName (fun _ => True) := by
  intro n _
  rw [genName, SPMF.mem_support_iff_may]
  walk [CedarTyped.genString.complete.obs]
  exact Or.inr ⟨n.id, n.path, by simp, rfl⟩

theorem genPattern_complete : (n : Nat) → (p : Pattern) → p.length ≤ n → p ∈ (genPattern (G := SPMF) n).support
  | 0, [], _ => by rw [genPattern, SPMF.mem_support_iff_may]; walk
  | n + 1, [], _ => by rw [genPattern, SPMF.mem_support_iff_may]; walk
  | n + 1, e :: p, hl => by
    have ih := genPattern_complete n p (by simp at hl; omega)
    rw [genPattern, SPMF.mem_support_iff_may]; walk [CedarTyped.genChar.complete.obs]
    cases e with
    | star => exact Or.inl ⟨p, ih, rfl⟩
    | justChar ch => exact Or.inr ⟨ch, p, ih, rfl⟩

/-! ### The schema, computed -/

open CedarWide (userT groupT photoT albumT actionT view read userAttrs groupAttrs photoAttrs ctxTy
  addrTy actEntry)

theorem ets_eq : env.ets = Map.mk [
    (albumT, .standard ⟨Set.empty, Map.empty, none⟩),
    (groupT, .standard ⟨Set.empty, groupAttrs, none⟩),
    (photoT, .standard ⟨Set.make [albumT], photoAttrs, none⟩),
    (userT,  .standard ⟨Set.make [groupT], userAttrs, some .string⟩)] := by
  rfl

theorem acts_eq : env.acts = Map.mk [(read, actEntry []), (view, actEntry [read])] := by
  rfl

/-- The entity literals `typeOf` accepts: any identifier of a schema entity type, or a declared action. -/
def ValidUID (uid : EntityUID) : Prop :=
  uid.ty ∈ [albumT, groupT, photoT, userT] ∨ uid = view ∨ uid = read

theorem validUID_of (h : (env.ets.isValidEntityUID uid || env.acts.contains uid) = true) :
    ValidUID uid := by
  rw [ets_eq, acts_eq] at h
  simp only [EntitySchema.isValidEntityUID, ActionSchema.contains, Map.find?, Map.toList,
    List.find?, Bool.or_eq_true] at h
  unfold ValidUID
  cases h1 : albumT == uid.ty <;> cases h2 : groupT == uid.ty <;> cases h3 : photoT == uid.ty <;>
    cases h4 : userT == uid.ty <;> cases h5 : CedarWide.read == uid <;> cases h6 : view == uid <;>
    simp_all [EntitySchemaEntry.isValidEntityEID]

theorem genUID_complete (h : ValidUID uid) : uid ∈ (genUID (G := SPMF) uid.ty).support := by
  rw [genUID, SPMF.mem_support_iff_may]
  rcases h with h | rfl | rfl
  · have hne : (uid.ty == actionT) = false := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h <;> rw [h] <;> decide
    rw [if_neg (by simp [hne])]
    walk [CedarTyped.genString.complete.obs]
    exact Or.inr ⟨uid.eid, rfl⟩
  · rw [if_pos (by decide)]; walk; simp
  · rw [if_pos (by decide)]; walk; simp

/-- The literals `typeOf` accepts. -/
def ValidPrim : Prim → Prop
  | .entityUID uid => ValidUID uid
  | _ => True

theorem entityTypes_of_valid (h : ValidUID uid) : uid.ty ∈ CedarWide.entityTypes := by
  rcases h with h | rfl | rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h <;> rw [h] <;> decide
  all_goals decide

theorem genPrim_complete : IsCompleteFor (genPrim (G := SPMF)) ValidPrim := by
  intro p hp
  rw [genPrim, SPMF.mem_support_iff_may]
  walk [CedarTyped.genBool.complete.obs, CedarTyped.genInt64.complete.obs,
    CedarTyped.genString.complete.obs]
  cases p with
  | bool b => exact Or.inl ⟨b, rfl⟩
  | int i => exact Or.inr (Or.inl ⟨i, rfl⟩)
  | string s => exact Or.inr (Or.inr (Or.inl ⟨s, rfl⟩))
  | entityUID uid =>
    refine Or.inr (Or.inr (Or.inr ⟨uid.ty, entityTypes_of_valid hp, ?_⟩))
    split
    · rename_i ha
      rcases hp with h | rfl | rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h | h | h <;> rw [h] at ha <;> exact absurd ha (by decide)
      all_goals simp
    · exact Or.inr ⟨uid.eid, rfl⟩

theorem genAnyPrim_complete : IsCompleteFor (genAnyPrim (G := SPMF)) (fun _ => True) := by
  intro p _
  rw [genAnyPrim, SPMF.mem_support_iff_may]
  walk [CedarTyped.genBool.complete.obs, CedarTyped.genInt64.complete.obs,
    CedarTyped.genString.complete.obs, genName_complete.obs]
  cases p with
  | bool b => exact Or.inl ⟨b, rfl⟩
  | int i => exact Or.inr (Or.inl ⟨i, rfl⟩)
  | string s => exact Or.inr (Or.inr (Or.inl ⟨s, rfl⟩))
  | entityUID uid => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨uid.ty, uid.eid, rfl⟩)))

/-! ## Dead branches: `genAny` reaches every expression -/

/-- `e` is within `genAny n`'s bounds: nesting depth, list lengths, `like` patterns, and `has` chains
at most `n`. -/
inductive AnyE : Spec.Expr → Nat → Prop where
  | lit (p : Prim) (n : Nat) : AnyE (.lit p) n
  | var (v : Var) (n : Nat) : AnyE (.var v) n
  | ite : AnyE a n → AnyE b n → AnyE c n → AnyE (.ite a b c) (n + 1)
  | and : AnyE a n → AnyE b n → AnyE (.and a b) (n + 1)
  | or : AnyE a n → AnyE b n → AnyE (.or a b) (n + 1)
  | unaryApp : (∀ p, op = .like p → p.length ≤ n) → AnyE x n → AnyE (.unaryApp op x) (n + 1)
  | binaryApp : AnyE a n → AnyE b n → AnyE (.binaryApp op a b) (n + 1)
  | hasAttr : AnyE x n → AnyE (.hasAttr x a) (n + 1)
  | getAttr : AnyE x n → AnyE (.getAttr x a) (n + 1)
  | extHasAttr : atts.length ≤ n → AnyE x n → AnyE (.extHasAttr x a atts) (n + 1)
  | set : xs.length ≤ n → (∀ x ∈ xs, AnyE x n) → AnyE (.set xs) (n + 1)
  | record : fs.length ≤ n → (∀ p ∈ fs, AnyE p.2 n) → AnyE (.record fs) (n + 1)
  | call : xs.length ≤ n → (∀ x ∈ xs, AnyE x n) → AnyE (.call fn xs) (n + 1)

theorem AnyE.succ (h : AnyE e n) : AnyE e (n + 1) := by
  induction h with
  | lit => exact .lit _ _
  | var => exact .var _ _
  | ite _ _ _ iha ihb ihc => exact .ite iha ihb ihc
  | and _ _ iha ihb => exact .and iha ihb
  | or _ _ iha ihb => exact .or iha ihb
  | unaryApp hp _ ih => exact .unaryApp (fun p h => by have := hp p h; omega) ih
  | binaryApp _ _ iha ihb => exact .binaryApp iha ihb
  | hasAttr _ ih => exact .hasAttr ih
  | getAttr _ ih => exact .getAttr ih
  | extHasAttr hl _ ih => exact .extHasAttr (by omega) ih
  | set hl _ ih => exact .set (by omega) ih
  | record hl _ ih => exact .record (by omega) ih
  | call hl _ ih => exact .call (by omega) ih

theorem AnyE.le (h : AnyE e n) (hnm : n ≤ m) : AnyE e m := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact ih.succ

theorem AnyE.forall_list {P : α → Spec.Expr} :
    (xs : List α) → (∀ x ∈ xs, ∃ n, AnyE (P x) n) → ∃ n, xs.length ≤ n ∧ ∀ x ∈ xs, AnyE (P x) n
  | [], _ => ⟨0, by simp⟩
  | x :: xs, h => by
    obtain ⟨n, hn⟩ := h x (by simp)
    obtain ⟨m, hl, hm⟩ := AnyE.forall_list xs (fun y hy => h y (by simp [hy]))
    refine ⟨max n m + 1, by simp; omega, ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hn.le (by omega)
    · exact (hm y hy).le (by omega)

theorem AnyE.exists : (e : Spec.Expr) → ∃ n, AnyE e n
  | .lit p => ⟨0, .lit p 0⟩
  | .var v => ⟨0, .var v 0⟩
  | .ite a b c => by
    obtain ⟨na, ha⟩ := AnyE.exists a; obtain ⟨nb, hb⟩ := AnyE.exists b
    obtain ⟨nc, hc⟩ := AnyE.exists c
    exact ⟨max na (max nb nc) + 1, .ite (ha.le (by omega)) (hb.le (by omega)) (hc.le (by omega))⟩
  | .and a b => by
    obtain ⟨na, ha⟩ := AnyE.exists a; obtain ⟨nb, hb⟩ := AnyE.exists b
    exact ⟨max na nb + 1, .and (ha.le (by omega)) (hb.le (by omega))⟩
  | .or a b => by
    obtain ⟨na, ha⟩ := AnyE.exists a; obtain ⟨nb, hb⟩ := AnyE.exists b
    exact ⟨max na nb + 1, .or (ha.le (by omega)) (hb.le (by omega))⟩
  | .unaryApp op x => by
    obtain ⟨n, h⟩ := AnyE.exists x
    let k := match op with | .like p => p.length | _ => 0
    refine ⟨max n k + 1, .unaryApp (fun p hp => ?_) (h.le (by omega))⟩
    subst hp; simp [k]
  | .binaryApp op a b => by
    obtain ⟨na, ha⟩ := AnyE.exists a; obtain ⟨nb, hb⟩ := AnyE.exists b
    exact ⟨max na nb + 1, .binaryApp (ha.le (by omega)) (hb.le (by omega))⟩
  | .hasAttr x a => by
    obtain ⟨n, h⟩ := AnyE.exists x; exact ⟨n + 1, .hasAttr h⟩
  | .getAttr x a => by
    obtain ⟨n, h⟩ := AnyE.exists x; exact ⟨n + 1, .getAttr h⟩
  | .extHasAttr x a atts => by
    obtain ⟨n, h⟩ := AnyE.exists x
    exact ⟨max n atts.length + 1, .extHasAttr (by omega) (h.le (by omega))⟩
  | .set xs => by
    obtain ⟨n, hl, h⟩ := AnyE.forall_list (P := id) xs (fun x _ => AnyE.exists x)
    exact ⟨n + 1, .set hl h⟩
  | .record fs => by
    obtain ⟨n, hl, h⟩ := AnyE.forall_list (P := Prod.snd) fs (fun p hp =>
      have : sizeOf p.2 < 1 + sizeOf fs := by
        have := List.sizeOf_lt_of_mem hp; cases p; simp at this ⊢; omega
      AnyE.exists p.2)
    exact ⟨n + 1, .record hl h⟩
  | .call fn xs => by
    obtain ⟨n, hl, h⟩ := AnyE.forall_list (P := id) xs (fun x _ => AnyE.exists x)
    exact ⟨n + 1, .call hl h⟩

/-- Closes a disjunction of generator branches by the first disjunct `t` proves. -/
syntax "branch " term : tactic
macro_rules
  | `(tactic| branch $t) => `(tactic| first | exact $t | exact Or.inl $t | (apply Or.inr; branch $t))

theorem genAny_zero_mono (h : e ∈ (genAny (G := SPMF) 0).support) :
    e ∈ (genAny (G := SPMF) n).support := by
  cases n with
  | zero => exact h
  | succ n =>
    rw [genAny, SPMF.mem_support_iff_may]
    walk [(show IsCompleteFor (genAny (G := SPMF) 0) (· ∈ (genAny (G := SPMF) 0).support)
      from fun _ h => h).obs, genAttr_complete.obs, genName_complete.obs]
    exact Or.inl h

theorem genAny_complete (h : AnyE e n) : e ∈ (genAny (G := SPMF) n).support := by
  have self : ∀ n, IsCompleteFor (genAny (G := SPMF) n) (· ∈ (genAny (G := SPMF) n).support) :=
    fun _ _ h => h
  induction h with
  | lit p n =>
    apply genAny_zero_mono; rw [genAny, SPMF.mem_support_iff_may]; walk [genAnyPrim_complete.obs]
    exact ⟨p, rfl⟩
  | var v n =>
    apply genAny_zero_mono; rw [genAny, SPMF.mem_support_iff_may]; walk
    exact ⟨v, by cases v <;> simp, rfl⟩
  | ite _ _ _ iha ihb ihc =>
    rw [genAny, SPMF.mem_support_iff_may]
    walk [self 0 |>.obs, self _ |>.obs, genAttr_complete.obs, genName_complete.obs]
    branch ⟨_, iha, _, ihb, _, ihc, rfl⟩
  | and _ _ iha ihb =>
    rw [genAny, SPMF.mem_support_iff_may]
    walk [self 0 |>.obs, self _ |>.obs, genAttr_complete.obs, genName_complete.obs]
    branch ⟨_, iha, _, ihb, rfl⟩
  | or _ _ iha ihb =>
    rw [genAny, SPMF.mem_support_iff_may]
    walk [self 0 |>.obs, self _ |>.obs, genAttr_complete.obs, genName_complete.obs]
    branch ⟨_, iha, _, ihb, rfl⟩
  | @unaryApp op n x hp _ ih =>
    rw [genAny, SPMF.mem_support_iff_may]
    walk [self 0 |>.obs, self _ |>.obs, genAttr_complete.obs, genName_complete.obs]
    cases op with
    | like p => branch ⟨p, genPattern_complete n p (hp p rfl), _, ih, rfl⟩
    | is ety => branch ⟨ety, _, ih, rfl⟩
    | _ => branch ⟨_, ih, rfl⟩
  | @binaryApp a n b op _ _ iha ihb =>
    rw [genAny, SPMF.mem_support_iff_may]
    walk [self 0 |>.obs, self _ |>.obs, genAttr_complete.obs, genName_complete.obs]
    branch ⟨op, by cases op <;> simp, _, iha, _, ihb, rfl⟩
  | @hasAttr x n a _ ih =>
    rw [genAny, SPMF.mem_support_iff_may]
    walk [self 0 |>.obs, self _ |>.obs, genAttr_complete.obs, genName_complete.obs]
    branch ⟨_, ih, a, rfl⟩
  | @getAttr x n a _ ih =>
    rw [genAny, SPMF.mem_support_iff_may]
    walk [self 0 |>.obs, self _ |>.obs, genAttr_complete.obs, genName_complete.obs]
    branch ⟨_, ih, a, rfl⟩
  | extHasAttr hl _ ih =>
    rw [genAny, SPMF.mem_support_iff_may]
    walk [self 0 |>.obs, self _ |>.obs, genAttr_complete.obs, genName_complete.obs]
    branch ⟨_, ih, _, _, genListUpTo_complete genAttr_complete _ _ hl (fun _ _ => trivial), rfl⟩
  | @set n xs hl _ ih =>
    rw [genAny, SPMF.mem_support_iff_may]
    walk [self 0 |>.obs, self _ |>.obs, genAttr_complete.obs, genName_complete.obs]
    branch ⟨xs, genListUpTo_complete (self n) n xs hl ih, rfl⟩
  | @record n fs hl _ ih =>
    have hpair : IsCompleteFor (do let a ← CedarWide.genAttr; let x ← genAny (G := SPMF) n; pure (a, x))
        (fun p => p.2 ∈ (genAny (G := SPMF) n).support) := by
      intro p hp; rw [SPMF.mem_support_iff_may]; walk [genAttr_complete.obs, (self n).obs]
      exact ⟨p.1, p.2, hp, rfl⟩
    rw [genAny, SPMF.mem_support_iff_may]
    walk [self 0 |>.obs, self _ |>.obs, genAttr_complete.obs, genName_complete.obs]
    branch ⟨fs, genListUpTo_complete hpair n fs hl ih, rfl⟩
  | @call n xs fn hl _ ih =>
    rw [genAny, SPMF.mem_support_iff_may]
    walk [self 0 |>.obs, self _ |>.obs, genAttr_complete.obs, genName_complete.obs]
    branch ⟨fn, by cases fn <;> decide, xs, genListUpTo_complete (self n) n xs hl ih, rfl⟩

/-! ## Each rule reaches every judgment its helper gives -/

section rules
variable (f : Fam SPMF)

/-- The generator's own support, as a fact a walk can use. -/
theorem supp_complete (g : SPMF α) : IsCompleteFor g (· ∈ g.support) := fun _ h => h

theorem ruleAnd_ff (ha : some a ∈ (f.bool c).support) (hff : a.ty = .bool .ff)
    (hb : b ∈ f.any.support) :
    ofR (.and a.e b) (typeOfAnd (a.tx, a.out) dead) ∈ (ruleAnd f c).support := by
  rw [SPMF.mem_support_iff_may, ruleAnd]
  walk [(supp_complete (f.bool c)).obs, (supp_complete f.any).obs]
  refine ⟨some a, ha, ?_⟩; dsimp only
  rw [if_pos (by simp [hff])]
  exact ⟨b, hb, rfl⟩

theorem ruleAnd_both (ha : some a ∈ (f.bool c).support) (hff : a.ty ≠ .bool .ff)
    (hb : some b ∈ (f.bool (c ∪ a.out)).support) :
    ofR (.and a.e b.e) (typeOfAnd (a.tx, a.out) b.res) ∈ (ruleAnd f c).support := by
  rw [SPMF.mem_support_iff_may, ruleAnd]
  walk [(supp_complete (f.bool c)).obs, (supp_complete (f.bool (c ∪ a.out))).obs]
  refine ⟨some a, ha, ?_⟩; dsimp only
  rw [if_neg (by simpa using hff)]
  exact ⟨some b, hb, rfl⟩

theorem ruleOr_tt (ha : some a ∈ (f.bool c).support) (htt : a.ty = .bool .tt)
    (hb : b ∈ f.any.support) :
    ofR (.or a.e b) (typeOfOr (a.tx, a.out) dead) ∈ (ruleOr f c).support := by
  rw [SPMF.mem_support_iff_may, ruleOr]
  walk [(supp_complete (f.bool c)).obs, (supp_complete f.any).obs]
  refine ⟨some a, ha, ?_⟩; dsimp only
  rw [if_pos (by simp [htt])]
  exact ⟨b, hb, rfl⟩

theorem ruleOr_both (ha : some a ∈ (f.bool c).support) (htt : a.ty ≠ .bool .tt)
    (hb : some b ∈ (f.bool c).support) :
    ofR (.or a.e b.e) (typeOfOr (a.tx, a.out) b.res) ∈ (ruleOr f c).support := by
  rw [SPMF.mem_support_iff_may, ruleOr]
  walk [(supp_complete (f.bool c)).obs]
  refine ⟨some a, ha, ?_⟩; dsimp only
  rw [if_neg (by simpa using htt)]
  exact ⟨some b, hb, rfl⟩

theorem ruleIte_tt (hg : some g ∈ (f.bool c).support) (htt : g.ty = .bool .tt)
    (ht : some t ∈ (branch (c ∪ g.out)).support) (he : e ∈ f.any.support) :
    ofR (.ite g.e t.e e) (typeOfIf (g.tx, g.out) t.res dead) ∈ (ruleIte f c branch).support := by
  rw [SPMF.mem_support_iff_may, ruleIte]
  walk [(supp_complete (f.bool c)).obs, (supp_complete f.any).obs,
    fun c' => (supp_complete (branch c')).obs]
  refine ⟨some g, hg, ?_⟩; dsimp only
  rw [if_pos (by simp [htt])]
  exact ⟨some t, ht, e, he, rfl⟩

theorem ruleIte_ff (hg : some g ∈ (f.bool c).support) (hff : g.ty = .bool .ff)
    (he : some e ∈ (branch c).support) (ht : t ∈ f.any.support) :
    ofR (.ite g.e t e.e) (typeOfIf (g.tx, g.out) dead e.res) ∈ (ruleIte f c branch).support := by
  rw [SPMF.mem_support_iff_may, ruleIte]
  walk [(supp_complete (f.bool c)).obs, (supp_complete f.any).obs,
    fun c' => (supp_complete (branch c')).obs]
  refine ⟨some g, hg, ?_⟩; dsimp only
  rw [if_neg (by simp [hff]), if_pos (by simp [hff])]
  exact ⟨some e, he, t, ht, rfl⟩

theorem ruleIte_any (hg : some g ∈ (f.bool c).support) (htt : g.ty ≠ .bool .tt)
    (hff : g.ty ≠ .bool .ff) (ht : some t ∈ (branch (c ∪ g.out)).support)
    (he : some e ∈ (branch c).support) :
    ofR (.ite g.e t.e e.e) (typeOfIf (g.tx, g.out) t.res e.res) ∈ (ruleIte f c branch).support := by
  rw [SPMF.mem_support_iff_may, ruleIte]
  walk [(supp_complete (f.bool c)).obs, (supp_complete f.any).obs,
    fun c' => (supp_complete (branch c')).obs]
  refine ⟨some g, hg, ?_⟩; dsimp only
  rw [if_neg (by simpa using htt), if_neg (by simpa using hff)]
  exact ⟨some t, ht, some e, he, rfl⟩

theorem binary_complete (ha : some a ∈ (f.atTy c t₁).support) (hb : some b ∈ (f.atTy c t₂).support) :
    ofR (.binaryApp op a.e b.e) (typeOfBinaryApp op a.tx b.tx a.e b.e c env) ∈
      (binary f c op t₁ t₂).support := by
  rw [SPMF.mem_support_iff_may, binary]
  walk [fun c' t => (supp_complete (f.atTy c' t)).obs]
  exact ⟨some a, ha, some b, hb, rfl⟩

theorem unary_bool (hx : some x ∈ (f.bool c).support) :
    ofR (.unaryApp op x.e) (typeOfUnaryApp op x.tx) ∈ (unary f c op (.bool bt)).support := by
  rw [SPMF.mem_support_iff_may, unary]
  walk [fun c' => (supp_complete (f.bool c')).obs]
  exact ⟨some x, hx, rfl⟩

theorem unary_value (hne : ∀ b, ty ≠ .bool b) (hx : some x ∈ (f.atTy c ty).support) :
    ofR (.unaryApp op x.e) (typeOfUnaryApp op x.tx) ∈ (unary f c op ty).support := by
  rw [SPMF.mem_support_iff_may]
  unfold unary
  split
  · rename_i b; exact absurd rfl (hne b)
  · walk [fun c' t => (supp_complete (f.atTy c' t)).obs]
    exact ⟨some x, hx, rfl⟩

theorem ruleHas_complete (hbt : bt ∈ baseTypes c) (hx : some x ∈ (f.atTy c bt).support) :
    ofR (.hasAttr x.e a) (typeOfHasAttr x.tx x.e a c env) ∈ (ruleHas f c).support := by
  rw [SPMF.mem_support_iff_may, ruleHas]
  walk [fun c' t => (supp_complete (f.atTy c' t)).obs, genAttr_complete.obs]
  exact ⟨bt, hbt, some x, hx, a, rfl⟩

theorem ruleRead_cap (hq : q ∈ capReads c ty) :
    ofR (.getAttr q.1 q.2.2) (typeOfGetAttr q.2.1 q.1 q.2.2 c env) ∈ (ruleRead f c ty).support := by
  rw [SPMF.mem_support_iff_may, ruleRead]
  walk [fun c' t => (supp_complete (f.atTy c' t)).obs]
  all_goals rename_i h1 h2
  all_goals first | (rw [h1] at hq; cases hq; done) | branch ⟨q, h1 ▸ hq, rfl⟩

theorem ruleRead_req (hr : r ∈ requiredReads c ty) (hx : some x ∈ (f.atTy c r.1).support) :
    ofR (.getAttr x.e r.2) (typeOfGetAttr x.tx x.e r.2 c env) ∈ (ruleRead f c ty).support := by
  rw [SPMF.mem_support_iff_may, ruleRead]
  walk [fun c' t => (supp_complete (f.atTy c' t)).obs]
  all_goals rename_i h1 h2
  all_goals first | (rw [h2] at hr; cases hr; done) | branch ⟨r, h2 ▸ hr, some x, hx, rfl⟩

theorem call_args_complete : (tys : List CedarType) → (xs : List J) →
    List.Forall₂ (fun x ty => some x ∈ (f.atTy c ty).support) xs tys →
    some xs ∈ (call.args f c tys).support
  | [], [], _ => by rw [SPMF.mem_support_iff_may, call.args]; walk
  | ty :: tys, x :: xs, .cons hx hxs => by
    have ih := call_args_complete tys xs hxs
    rw [SPMF.mem_support_iff_may, call.args]
    walk [fun c' t => (supp_complete (f.atTy c' t)).obs, (supp_complete (call.args f c tys)).obs]
    exact ⟨some x, hx, some xs, ih, rfl⟩

theorem call_complete (h : List.Forall₂ (fun x ty => some x ∈ (f.atTy c ty).support) xs tys) :
    ofR (.call fn (xs.map J.e)) (typeOfCall fn (xs.map J.tx) (xs.map J.e)) ∈
      (call f c fn tys).support := by
  rw [SPMF.mem_support_iff_may, call]
  walk [fun tys => (supp_complete (call.args f c tys)).obs]
  exact ⟨some xs, call_args_complete f tys xs h, rfl⟩

theorem ruleSet_elems_complete : (n : Nat) → (xs : List J) → xs.length = n →
    (∀ x ∈ xs, some x ∈ (f.atTy c elt).support) → some xs ∈ (ruleSet.elems f c elt n).support
  | 0, [], _, _ => by rw [SPMF.mem_support_iff_may, ruleSet.elems]; walk
  | n + 1, x :: xs, hl, hx => by
    have ih := ruleSet_elems_complete n xs (by simpa using hl) (fun y hy => hx y (by simp [hy]))
    rw [SPMF.mem_support_iff_may, ruleSet.elems]
    walk [fun c' t => (supp_complete (f.atTy c' t)).obs,
      (supp_complete (ruleSet.elems f c elt n)).obs]
    exact ⟨some x, hx x (by simp), some xs, ih, rfl⟩

theorem ruleSet_complete {xs : List J} (h₁ : 1 ≤ xs.length) (h₂ : xs.length ≤ f.fuel + 1)
    (hx : ∀ x ∈ xs, some x ∈ (f.atTy c elt).support) :
    ofR (.set (xs.map J.e)) (typeOfSet (xs.map J.tx)) ∈ (ruleSet f c elt).support := by
  rw [SPMF.mem_support_iff_may, ruleSet]
  walk [fun n => (supp_complete (ruleSet.elems f c elt n)).obs]
  exact ⟨xs.length, ⟨h₁, h₂⟩, some xs, ruleSet_elems_complete f _ xs rfl hx, rfl⟩

end rules

/-! ### Multi-attribute `has` chains -/

/-- The chains `genChain cur` draws: after the first attribute, each is an entity- or record-typed
attribute of the type reached so far, or absent (after which anything goes). -/
def ChainOK : Option CedarType → List Attr → Prop
  | _, [] => False
  | _, [_] => True
  | none, _ :: rest => ChainOK none rest
  | some bt, a :: rest =>
    match (attrTy bt a).map Qualified.getType with
    | none => ChainOK none rest
    | some t@(.entity _) | some t@(.record _) => ChainOK (some t) rest
    | some _ => False

theorem genChain_complete : (n : Nat) → (cur : Option CedarType) → (l : List Attr) →
    l.length = n + 1 → ChainOK cur l → l ∈ (genChain (G := SPMF) cur n).support
  | 0, cur, [a], _, _ => by
    rw [SPMF.mem_support_iff_may, genChain]; walk [genAttr_complete.obs]
    exact ⟨a, rfl⟩
  | n + 1, none, a :: rest, hl, hc => by
    have ih := genChain_complete n none rest (by simpa using hl) (by cases rest <;> simp_all [ChainOK])
    rw [SPMF.mem_support_iff_may, genChain]
    walk [genAttr_complete.obs, fun c m => (supp_complete (genChain (G := SPMF) c m)).obs]
    exact ⟨a, rest, ih, rfl⟩
  | n + 1, some bt, a :: rest, hl, hc => by
    have hl' : rest.length = n + 1 := by simpa using hl
    rw [genChain, SPMF.mem_support_bind_iff]
    refine ⟨a, genAttr_complete a trivial, ?_⟩
    obtain ⟨r, rs, rfl⟩ : ∃ r rs, rest = r :: rs := by
      cases rest with
      | nil => simp at hl'
      | cons r rs => exact ⟨r, rs, rfl⟩
    simp only [ChainOK] at hc
    dsimp only
    have go : ∀ cur, ChainOK cur (r :: rs) → ∀ hd, hd :: r :: rs ∈
        (do let t ← genChain (G := SPMF) cur n; pure (hd :: t)).support := fun cur hc hd => by
      rw [SPMF.mem_support_iff_may]
      walk [fun c m => (supp_complete (genChain (G := SPMF) c m)).obs]
      exact ⟨r :: rs, genChain_complete n cur _ hl' hc, rfl⟩
    cases hm : (attrTy bt a).map Qualified.getType with
    | none => simp only [hm] at hc; exact go none hc a
    | some t =>
      simp only [hm] at hc
      cases t <;> first | exact absurd hc id | exact go _ hc a

section rules2
variable (f : Fam SPMF)

theorem ruleExtHas_complete (hbt : bt ∈ baseTypes c) (hx : some x ∈ (f.atTy c bt).support)
    (hl₁ : 1 ≤ atts.length) (hl₂ : atts.length ≤ f.fuel + 1) (hch : ChainOK (some bt) (a :: atts))
    (ht : typeOfExtHasAttr x.tx x.e (a :: atts) c env = .ok (bty, c')) :
    some ⟨.extHasAttr x.e a atts, .extHasAttr x.tx a atts (.bool bty), c'⟩ ∈
      (ruleExtHas f c).support := by
  rw [SPMF.mem_support_iff_may, ruleExtHas]
  walk [fun c' t => (supp_complete (f.atTy c' t)).obs,
    fun b n => (supp_complete (genChain (G := SPMF) b n)).obs]
  refine ⟨bt, hbt, some x, hx, atts.length, ⟨hl₁, hl₂⟩, a :: atts,
    genChain_complete _ _ _ rfl hch, ?_⟩
  simp [ht]

theorem more_complete (field : CedarType → SPMF (Option J)) (pickTy : SPMF CedarType) :
    (n : Nat) → (names : List Attr) → (fs : List (Attr × J)) → fs.length ≤ n →
    (fs.map Prod.fst).Nodup → (∀ p ∈ fs, p.1 ∉ names) →
    (∀ p ∈ fs, ∃ ty ∈ pickTy.support, some p.2 ∈ (field ty).support) →
    some fs ∈ (recordLit.more field pickTy names n).support
  | 0, _, [], _, _, _, _ => by rw [SPMF.mem_support_iff_may, recordLit.more]; walk
  | n + 1, _, [], _, _, _, _ => by rw [SPMF.mem_support_iff_may, recordLit.more]; walk
  | n + 1, names, (a, j) :: fs, hl, hnd, hn, hf => by
    obtain ⟨ty, hty, hj⟩ := hf (a, j) (by simp)
    have ih := more_complete field pickTy n (a :: names) fs (by simp at hl; omega)
      (List.nodup_cons.mp hnd).2
      (fun p hp => by
        simp only [List.mem_cons, not_or]
        refine ⟨fun h => ?_, hn p (by simp [hp])⟩
        refine (List.nodup_cons.mp hnd).1 ?_
        rw [← h]; exact List.mem_map.mpr ⟨p, hp, rfl⟩)
      (fun p hp => hf p (by simp [hp]))
    rw [SPMF.mem_support_iff_may, recordLit.more]
    walk [genAttr_complete.obs, (supp_complete pickTy).obs, fun t => (supp_complete (field t)).obs,
      fun nm m => (supp_complete (recordLit.more field pickTy nm m)).obs]
    refine Or.inr ⟨a, ?_⟩
    rw [if_neg (hn (a, j) (by simp))]
    exact ⟨ty, hty, some j, hj, some fs, ih, rfl⟩

/-- `j` is reachable from `f` at its own type, under `c`: a boolean from `f.bool`, any other type a
value type inhabited under `c`, from `f.atTy`. -/
def ReachF (f : Fam SPMF) (c : Capabilities) (j : J) : Prop :=
  (∃ b, j.ty = .bool b ∧ some j ∈ (f.bool c).support) ∨
  (j.ty ∈ valueTypes ∧ inhabited c j.ty = true ∧ some j ∈ (f.atTy c j.ty).support)

theorem ReachF.not_bool (h : ReachF f c j) (hne : ∀ b, j.ty ≠ .bool b) :
    j.ty ∈ valueTypes ∧ inhabited c j.ty = true ∧ some j ∈ (f.atTy c j.ty).support := by
  rcases h with ⟨b, hb, _⟩ | h
  · exact absurd hb (hne b)
  · exact h

theorem fields_pick {fs : List (Attr × J)} (hf : ∀ p ∈ fs, ReachF f c p.2) :
    ∀ p ∈ fs, ∃ ty ∈ (elements (G := SPMF)
        (CedarType.bool .anyBool :: valueTypes.filter (inhabited c)) (by simp)).support,
      some p.2 ∈ (match ty with | .bool _ => f.bool c | _ => f.atTy c ty).support := by
  intro p hp
  rcases hf p hp with ⟨b, hb, h⟩ | ⟨hv, hi, h⟩
  · refine ⟨.bool .anyBool, ?_, h⟩
    rw [SPMF.mem_support_iff_may]; walk; simp
  · refine ⟨p.2.ty, ?_, ?_⟩
    · rw [SPMF.mem_support_iff_may]; walk; simp [hv, hi]
    · split
      · rename_i b hb; rw [hb] at hv; simp [valueTypes, setElts, entityTys] at hv
      · exact h

theorem recordLit_none {fs : List (Attr × J)} (hl : fs.length ≤ f.fuel) (hnd : (fs.map Prod.fst).Nodup)
    (hf : ∀ p ∈ fs, ReachF f c p.2) : some (recordOf fs) ∈ (recordLit f c none).support := by
  unfold recordLit
  extract_lets field pickTy
  rw [SPMF.mem_support_iff_may]
  walk [fun nm m => (supp_complete (recordLit.more field pickTy nm m)).obs]
  exact ⟨some fs, more_complete field pickTy _ [] fs hl hnd (by simp) (fields_pick f hf), rfl⟩

theorem recordLit_some {rest : List (Attr × J)}
    (hj : ((∃ b, ty = .bool b) ∧ some j ∈ (f.bool c).support) ∨
      ((∀ b, ty ≠ .bool b) ∧ some j ∈ (f.atTy c ty).support))
    (hl : rest.length ≤ f.fuel) (hnd : (rest.map Prod.fst).Nodup) (ha : a ∉ rest.map Prod.fst)
    (hf : ∀ p ∈ rest, ReachF f c p.2) (hi : i ≤ rest.length) :
    some (recordOf (rest.insertIdx i (a, j))) ∈ (recordLit f c (some (a, ty))).support := by
  unfold recordLit
  extract_lets field pickTy
  have hfj : some j ∈ (field ty).support := by
    simp only [field]
    rcases hj with ⟨⟨b, rfl⟩, h⟩ | ⟨hne, h⟩
    · exact h
    · split
      · rename_i b; exact absurd rfl (hne b)
      · exact h
  have hpick : ∀ p ∈ rest, ∃ ty ∈ pickTy.support, some p.2 ∈ (field ty).support := fields_pick f hf
  clear_value field pickTy
  rw [SPMF.mem_support_iff_may]
  walk [fun t => (supp_complete (field t)).obs,
    fun nm m => (supp_complete (recordLit.more field pickTy nm m)).obs]
  refine ⟨some j, hfj, some rest,
    more_complete field pickTy _ [a] rest hl hnd
      (fun p hp h => ha (List.mem_map.mpr ⟨p, hp, by simpa using h⟩)) hpick,
    i, ⟨Nat.zero_le _, hi⟩, rfl⟩

theorem ruleRecordHas_complete {fs : List (Attr × J)} (hl : fs.length ≤ f.fuel) (hnd : (fs.map Prod.fst).Nodup)
    (hf : ∀ p ∈ fs, ReachF f c p.2) :
    ofR (.hasAttr (recordOf fs).1 a) (typeOfHasAttr (recordOf fs).2 (recordOf fs).1 a c env) ∈
      (ruleRecordHas f c).support := by
  rw [SPMF.mem_support_iff_may, ruleRecordHas]
  walk [fun n => (supp_complete (recordLit f c n)).obs, genAttr_complete.obs]
  exact ⟨some (recordOf fs), recordLit_none f hl hnd hf, a, rfl⟩

theorem ruleRecordGet_complete {rest : List (Attr × J)}
    (hj : ((∃ b, ty = .bool b) ∧ some j ∈ (f.bool c).support) ∨
      ((∀ b, ty ≠ .bool b) ∧ some j ∈ (f.atTy c ty).support))
    (hl : rest.length ≤ f.fuel) (hnd : (rest.map Prod.fst).Nodup) (ha : a ∉ rest.map Prod.fst)
    (hf : ∀ p ∈ rest, ReachF f c p.2) (hi : i ≤ rest.length) :
    let r := recordOf (rest.insertIdx i (a, j))
    ofR (.getAttr r.1 a) (typeOfGetAttr r.2 r.1 a c env) ∈ (ruleRecordGet f c ty).support := by
  intro r
  rw [SPMF.mem_support_iff_may, ruleRecordGet]
  walk [fun n => (supp_complete (recordLit f c n)).obs, genAttr_complete.obs]
  exact ⟨a, some r, recordLit_some f hj hl hnd ha hf hi, rfl⟩

/-- The strings `typeOf` accepts as an extension constructor's argument. -/
def ValidArg : ExtType → String → Prop
  | .ipAddr, s => (Ext.IPAddr.ip s).isSome
  | .decimal, s => (Ext.Decimal.decimal s).isSome
  | .datetime, s => (Ext.Datetime.parse s).isSome
  | .duration, s => (Ext.Datetime.Duration.parse s).isSome

theorem genExtArg_complete (h : ValidArg xt s) : s ∈ (genExtArg (G := SPMF) xt).support := by
  rw [SPMF.mem_support_iff_may]
  cases xt <;> (unfold genExtArg; walk [CedarTyped.genString.complete.obs]) <;>
    exact Or.inr ⟨s, by simp_all [ValidArg]⟩

theorem leaf_int : ofR (.lit (.int i)) (typeOfLit (.int i) env) ∈ (leaf (G := SPMF) c .int).support := by
  rw [SPMF.mem_support_iff_may, leaf]; walk [CedarTyped.genInt64.complete.obs]
  exact ⟨i, rfl⟩

theorem leaf_string : ofR (.lit (.string s)) (typeOfLit (.string s) env) ∈ (leaf (G := SPMF) c .string).support := by
  rw [SPMF.mem_support_iff_may, leaf]; walk [CedarTyped.genString.complete.obs]
  exact ⟨s, rfl⟩

theorem leaf_uid (h : ValidUID uid) :
    ofR (.lit (.entityUID uid)) (typeOfLit (.entityUID uid) env) ∈ (leaf (G := SPMF) c (.entity uid.ty)).support := by
  rw [SPMF.mem_support_iff_may, leaf]
  walk [(supp_complete (genUID (G := SPMF) uid.ty)).obs]
  all_goals first
    | exact ⟨uid, genUID_complete h, Or.inr rfl⟩
    | exact ⟨uid, genUID_complete h, rfl⟩

theorem leaf_ext (h : ValidArg xt s) :
    ofR (.call (ctorOf xt) [.lit (.string s)])
      (typeOfCall (ctorOf xt) [.lit (.string s) .string] [.lit (.string s)]) ∈
      (leaf (G := SPMF) c (.ext xt)).support := by
  rw [SPMF.mem_support_iff_may, leaf]
  walk [(supp_complete (genExtArg (G := SPMF) xt)).obs]
  exact ⟨s, genExtArg_complete h, rfl⟩

theorem leaf_var (hv : (v, ety) ∈ [(Var.principal, userT), (.resource, photoT), (.action, actionT)]) :
    ofR (.var v) (typeOfVar v env) ∈ (leaf (G := SPMF) c (.entity ety)).support := by
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hv
  rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hu : ValidUID ⟨userT, ""⟩ := Or.inl (by simp)
    rw [SPMF.mem_support_iff_may, leaf]
    walk [(supp_complete (genUID (G := SPMF) userT)).obs]
    exact ⟨_, genUID_complete hu⟩
  · have hu : ValidUID ⟨photoT, ""⟩ := Or.inl (by simp)
    rw [SPMF.mem_support_iff_may, leaf]
    walk [(supp_complete (genUID (G := SPMF) photoT)).obs]
    exact ⟨_, genUID_complete hu⟩
  · have hu : ValidUID view := Or.inr (Or.inl rfl)
    rw [SPMF.mem_support_iff_may, leaf]
    walk [(supp_complete (genUID (G := SPMF) actionT)).obs]
    exact ⟨_, genUID_complete hu⟩

theorem leaf_ctx : ofR (.var .context) (typeOfVar .context env) ∈
    (leaf (G := SPMF) c (.record ctxTy)).support := by
  rw [SPMF.mem_support_iff_may, leaf]
  walk
  all_goals simp

end rules2

/-! ## The fuel levels -/

theorem mem_pick {first : Nat × (Unit → SPMF α)} {rest : List (Nat × (Unit → SPMF α))} {h}
    (hm : (w, g) ∈ first :: rest) (hw : 0 < w) (hx : x ∈ (g ()).support) :
    x ∈ (pick first rest h).support := by
  rw [pick, SPMF.support_frequency]; exact ⟨w, g, hm, hw, hx⟩

theorem stepBool_and (f : Fam SPMF) (hx : x ∈ (ruleAnd f c).support) : x ∈ (stepBool f c).support := by
  unfold stepBool
  exact mem_pick (w := 4) (g := fun _ => ruleAnd f c) (by simp) (by decide) hx

theorem stepBool_or (f : Fam SPMF) (hx : x ∈ (ruleOr f c).support) : x ∈ (stepBool f c).support := by
  unfold stepBool
  exact mem_pick (w := 2) (g := fun _ => ruleOr f c) (by simp) (by decide) hx

theorem stepBool_ite (f : Fam SPMF) (hx : x ∈ (ruleIte f c fun c' => f.bool c').support) :
    x ∈ (stepBool f c).support := by
  unfold stepBool
  exact mem_pick (w := 2) (g := fun _ => ruleIte f c fun c' => f.bool c') (by simp) (by decide) hx

theorem stepAt_ite (f : Fam SPMF) (hx : x ∈ (ruleIte f c fun c' => f.atTy c' ty).support) :
    x ∈ (stepAt f c ty).support := by
  unfold stepAt
  exact mem_pick (w := 2) (g := fun _ => ruleIte f c fun c' => f.atTy c' ty) (by simp) (by decide) hx

theorem fam_any : (fam (G := SPMF) n).any = genAny n := by cases n <;> rfl

theorem fam_bool_lit (b : Bool) :
    ofR (.lit (.bool b)) (typeOfLit (.bool b) env) ∈ ((fam (G := SPMF) n).bool c).support := by
  cases n with
  | zero =>
    show _ ∈ (do let p := Prim.bool (← genBool); return ofR (.lit p) (typeOfLit p env) : SPMF _).support
    rw [SPMF.mem_support_iff_may]; walk [CedarTyped.genBool.complete.obs]; exact ⟨b, rfl⟩
  | succ n =>
    show _ ∈ (stepBool (fam (G := SPMF) n) c).support
    unfold stepBool
    refine mem_pick (List.mem_cons_self ..) (by decide) ?_
    rw [SPMF.mem_support_iff_may]; walk [CedarTyped.genBool.complete.obs]; exact ⟨b, rfl⟩

theorem fam_leaf (hx : x ∈ (leaf (G := SPMF) c ty).support) :
    x ∈ ((fam (G := SPMF) n).atTy c ty).support := by
  cases n with
  | zero => exact hx
  | succ n =>
    show _ ∈ (stepAt (fam (G := SPMF) n) c ty).support
    unfold stepAt
    exact mem_pick (w := 3) (g := fun _ => leaf c ty) (by simp) (by decide) hx

/-! ## Least upper bounds over the value types -/

theorem lub_ctx_addr : (CedarType.record ctxTy ⊔ .record addrTy) = none := by decide
theorem lub_addr_ctx : (CedarType.record addrTy ⊔ .record ctxTy) = none := by decide

/-- Two value types have a least upper bound only when they are equal. A finite check. -/
theorem lub_value (h₂ : t₂ ∈ valueTypes) (h₃ : t₃ ∈ valueTypes) (h : (t₂ ⊔ t₃) = some t) :
    t₂ = t ∧ t₃ = t := by
  simp only [valueTypes, setElts, entityTys, CedarWide.entityTypes, List.map, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at h₂ h₃
  rcases h₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases h₃ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | (rw [Cedar.Thm.lub_refl] at h; simp at h; exact ⟨h, h⟩)
    | (simp [lub_ctx_addr, lub_addr_ctx] at h; done)
    | (simp [lub?, userT, groupT, photoT, albumT, actionT] at h; done)

/-! ## The fragment -/

/-- A variable or literal followed by attribute reads. -/
inductive IsPath : Spec.Expr → Prop where
  | var (v : Var) : IsPath (.var v)
  | lit (p : Prim) : IsPath (.lit p)
  | getAttr : IsPath x → IsPath (.getAttr x a)

/-- A type the generator builds values of under `c`. -/
def TyU (c : Capabilities) (ty : CedarType) : Prop :=
  (∃ b, ty = .bool b) ∨ (ty ∈ valueTypes ∧ inhabited c ty = true)

/-- `e`'s type under `c`, if it has one, is one the generator builds. -/
def TyOK (c : Capabilities) (e : Spec.Expr) : Prop :=
  ∀ tx ce, typeOf e c env = .ok (tx, ce) → TyU c tx.typeOf

/-- The fragment `CedarGen` is complete for, under capabilities `c`, at fuel `n`. A node's own
fuel bounds its depth and the lengths of the lists it holds; the rest are the generator's
restrictions:

* a read justified by a capability is of a path;
* a tag is read only from a path, by a path;
* a record literal appears only as the base of a `has` or a read, with distinct field names;
* a set, conditional, or read has a type the generator builds (`TyOK`): a boolean or one of the
  `valueTypes`, the address record only where a capability lets it be read;
* a dead branch (`&&`'s right operand after `false`, `||`'s after `true`, a singleton guard's
  untaken branch) is anything (`AnyE`). -/
inductive Scope : Capabilities → Spec.Expr → Nat → Prop where
  | lit (p : Prim) (n : Nat) : Scope c (.lit p) n
  | var (v : Var) (n : Nat) : Scope c (.var v) n
  | and : Scope c a n → AnyE b n →
      (∀ ta ca, typeOf a c env = .ok (ta, ca) → ta.typeOf ≠ .bool .ff → Scope (c ∪ ca) b n) →
      Scope c (.and a b) (n + 1)
  | or : Scope c a n → AnyE b n →
      (∀ ta ca, typeOf a c env = .ok (ta, ca) → ta.typeOf ≠ .bool .tt → Scope c b n) →
      Scope c (.or a b) (n + 1)
  | ite : Scope c g n → AnyE t n → AnyE e n →
      (∀ tg cg, typeOf g c env = .ok (tg, cg) → tg.typeOf ≠ .bool .ff → Scope (c ∪ cg) t n) →
      (∀ tg cg, typeOf g c env = .ok (tg, cg) → tg.typeOf ≠ .bool .tt → Scope c e n) →
      TyOK c (.ite g t e) → Scope c (.ite g t e) (n + 1)
  | unaryApp : (∀ p, op = .like p → p.length ≤ n) → Scope c x n → Scope c (.unaryApp op x) (n + 1)
  | binaryApp : op ≠ .getTag → Scope c a n → Scope c b n → Scope c (.binaryApp op a b) (n + 1)
  | getTag : IsPath x → IsPath t → Scope c (.binaryApp .getTag x t) (n + 1)
  | hasAttr : Scope c x n → Scope c (.hasAttr x a) (n + 1)
  | hasAttr_rec : fs.length ≤ n → (fs.map Prod.fst).Nodup → (∀ p ∈ fs, Scope c p.2 n) →
      Scope c (.hasAttr (.record fs) a) (n + 1)
  | getAttr : Scope c x n →
      (∀ tx cx, typeOf x c env = .ok (tx, cx) → ∃ t, attrTy tx.typeOf a = some (.required t)) →
      TyOK c (.getAttr x a) → Scope c (.getAttr x a) (n + 1)
  | getAttr_cap : IsPath x → (x, .attr a) ∈ c → TyOK c (.getAttr x a) → Scope c (.getAttr x a) (n + 1)
  | getAttr_rec : fs.length ≤ n + 1 → (fs.map Prod.fst).Nodup → (∀ p ∈ fs, Scope c p.2 n) →
      TyOK c (.getAttr (.record fs) a) → Scope c (.getAttr (.record fs) a) (n + 1)
  | extHasAttr : atts ≠ [] → atts.length ≤ n + 1 → Scope c x n →
      Scope c (.extHasAttr x a atts) (n + 1)
  | set : xs ≠ [] → xs.length ≤ n + 1 → (∀ x ∈ xs, Scope c x n) → TyOK c (.set xs) →
      Scope c (.set xs) (n + 1)
  | call : (∀ x ∈ xs, Scope c x n) → Scope c (.call fn xs) (n + 1)

theorem ofR_ok (h : r = .ok (tx, out)) : ofR e r = some ⟨e, tx, out⟩ := by simp [ofR, h]

theorem ReachF.bool (h : ReachF f c j) (hb : j.ty = .bool b) : some j ∈ (f.bool c).support := by
  rcases h with ⟨_, _, h⟩ | ⟨hv, _, _⟩
  · exact h
  · rw [hb] at hv; simp [valueTypes, setElts, entityTys] at hv

theorem reach_bool (hb : tx.typeOf = .bool b) (h : some ⟨e, tx, out⟩ ∈ (f.bool c).support) :
    ReachF f c ⟨e, tx, out⟩ := Or.inl ⟨b, hb, h⟩

theorem reach_val (hv : tx.typeOf ∈ valueTypes) (hi : inhabited c tx.typeOf = true)
    (h : some ⟨e, tx, out⟩ ∈ (f.atTy c tx.typeOf).support) : ReachF f c ⟨e, tx, out⟩ :=
  Or.inr ⟨hv, hi, h⟩

theorem inhabited_of_ne (h : ty ≠ .record addrTy) : inhabited c ty = true := by
  simp [inhabited, h]

theorem entity_value (h : ety ∈ CedarWide.entityTypes) : CedarType.entity ety ∈ valueTypes := by
  simp only [valueTypes, entityTys, List.mem_append, List.mem_map]
  exact Or.inl (Or.inl (Or.inr ⟨ety, h, rfl⟩))

theorem reach_lit : typeOf (.lit p) c env = .ok (tx, out) →
    ReachF (fam (G := SPMF) n) c ⟨.lit p, tx, out⟩ := by
  intro h
  simp only [typeOf] at h
  have hr := ofR_ok (e := .lit p) h
  cases p with
  | bool b =>
    have : ∃ bt, tx.typeOf = .bool bt := by
      cases b <;> simp [typeOfLit, ok] at h <;> obtain ⟨rfl, rfl⟩ := h <;> exact ⟨_, rfl⟩
    obtain ⟨bt, hbt⟩ := this
    exact reach_bool hbt (hr ▸ fam_bool_lit b)
  | int i =>
    simp [typeOfLit, ok] at h; obtain ⟨rfl, rfl⟩ := h
    exact reach_val (by simp [TypedExpr.typeOf, valueTypes]) (inhabited_of_ne (by simp [TypedExpr.typeOf]))
      (fam_leaf (hr ▸ leaf_int))
  | string s =>
    simp [typeOfLit, ok] at h; obtain ⟨rfl, rfl⟩ := h
    exact reach_val (by simp [TypedExpr.typeOf, valueTypes]) (inhabited_of_ne (by simp [TypedExpr.typeOf]))
      (fam_leaf (hr ▸ leaf_string))
  | entityUID uid =>
    by_cases hc : (env.ets.isValidEntityUID uid || env.acts.contains uid) = true
    · have hv := validUID_of hc
      simp [typeOfLit, hc, ok] at h; obtain ⟨rfl, rfl⟩ := h
      exact reach_val (by simpa [TypedExpr.typeOf] using entity_value (entityTypes_of_valid hv))
        (inhabited_of_ne (by simp [TypedExpr.typeOf])) (fam_leaf (hr ▸ leaf_uid hv))
    · simp [typeOfLit, hc, err] at h

theorem reqty_eq : env.reqty = (⟨userT, view, photoT, ctxTy⟩ : RequestType) := rfl

theorem ctx_ne_addr : ctxTy ≠ addrTy := by
  intro h
  have : ctxTy.contains "ip" = addrTy.contains "ip" := by rw [h]
  revert this; decide

theorem reach_var : typeOf (.var v) c env = .ok (tx, out) →
    ReachF (fam (G := SPMF) n) c ⟨.var v, tx, out⟩ := by
  intro h
  simp only [typeOf] at h
  have hr := ofR_ok (e := .var v) h
  cases v <;> simp [typeOfVar, ok, reqty_eq] at h <;> obtain ⟨rfl, rfl⟩ := h
  · exact reach_val (by simp [TypedExpr.typeOf, valueTypes, entityTys, CedarWide.entityTypes])
      (inhabited_of_ne (by simp [TypedExpr.typeOf])) (fam_leaf (hr ▸ leaf_var (by simp)))
  · exact reach_val (by simp [TypedExpr.typeOf, valueTypes, entityTys, CedarWide.entityTypes, view])
      (inhabited_of_ne (by simp [TypedExpr.typeOf])) (fam_leaf (hr ▸ leaf_var (by simp [view])))
  · exact reach_val (by simp [TypedExpr.typeOf, valueTypes, entityTys, CedarWide.entityTypes])
      (inhabited_of_ne (by simp [TypedExpr.typeOf])) (fam_leaf (hr ▸ leaf_var (by simp)))
  · exact reach_val (by simp [TypedExpr.typeOf, valueTypes])
      (inhabited_of_ne (by simp [TypedExpr.typeOf, ctx_ne_addr])) (fam_leaf (hr ▸ leaf_ctx))

theorem typeOf_and' (ha : typeOf a c env = .ok (ta, ca)) :
    typeOf (.and a b) c env = typeOfAnd (ta, ca) (typeOf b (c ∪ ca) env) := by
  simp [typeOf, ha]

theorem typeOf_or' (ha : typeOf a c env = .ok (ta, ca)) :
    typeOf (.or a b) c env = typeOfOr (ta, ca) (typeOf b c env) := by
  simp [typeOf, ha]

theorem typeOf_ite' (hg : typeOf g c env = .ok (tg, cg)) :
    typeOf (.ite g t e) c env = typeOfIf (tg, cg) (typeOf t (c ∪ cg) env) (typeOf e c env) := by
  simp [typeOf, hg]

theorem fam_succ_bool : ((fam (G := SPMF) (n + 1)).bool c) = stepBool (fam n) c := rfl
theorem fam_succ_atTy : ((fam (G := SPMF) (n + 1)).atTy c ty) = stepAt (fam n) c ty := rfl

theorem lub_bool_value (hv : v ∈ valueTypes) : (CedarType.bool b ⊔ v) = none := by
  simp only [valueTypes, setElts, entityTys, CedarWide.entityTypes, List.map, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> simp [lub?]

theorem lub_value_bool (hv : v ∈ valueTypes) : (v ⊔ CedarType.bool b) = none := by
  simp only [valueTypes, setElts, entityTys, CedarWide.entityTypes, List.map, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> simp [lub?]

theorem bool_not_value : CedarType.bool b ∉ valueTypes := by
  simp [valueTypes, setElts, entityTys]

/-- Two types the generator builds with a least upper bound: both booleans, or one value type twice. -/
theorem lub_U (h₂ : TyU c₂ t₂) (h₃ : TyU c₃ t₃) (h : (t₂ ⊔ t₃) = some t) :
    ((∃ b, t₂ = .bool b) ∧ (∃ b, t₃ = .bool b) ∧ (∃ b, t = .bool b)) ∨
      (t ∈ valueTypes ∧ t₂ = t ∧ t₃ = t) := by
  rcases h₂ with ⟨b₂, rfl⟩ | ⟨h₂, -⟩ <;> rcases h₃ with ⟨b₃, rfl⟩ | ⟨h₃, -⟩
  · simp [lub?] at h; exact Or.inl ⟨⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, h.symm⟩⟩
  · simp [lub_bool_value h₃] at h
  · simp [lub_value_bool h₂] at h
  · obtain ⟨rfl, rfl⟩ := lub_value h₂ h₃ h; exact Or.inr ⟨h₂, rfl, rfl⟩

theorem ReachF.tyU (h : ReachF f c j) : TyU c j.ty := by
  rcases h with ⟨b, hb, _⟩ | ⟨hv, hi, _⟩
  · exact Or.inl ⟨b, hb⟩
  · exact Or.inr ⟨hv, hi⟩

theorem ReachF.value (h : ReachF f c j) (hv : j.ty ∈ valueTypes) :
    some j ∈ (f.atTy c j.ty).support := by
  rcases h with ⟨b, hb, _⟩ | ⟨_, _, h⟩
  · rw [hb] at hv; exact absurd hv bool_not_value
  · exact h

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
