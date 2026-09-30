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

end CedarGen
