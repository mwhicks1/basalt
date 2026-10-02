/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Cedar.Thm.Validation.Typechecker.Set
import BasaltExamples.Cedar.Gen
import BasaltExamples.Cedar.Typed

/-!
# `CedarGen`'s completeness, rule by rule

Each rule reaches every judgment its helper gives from reachable sub-judgments, and each typing rule
of the fragment is matched by a rule; `GenComplete` assembles them.
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
    rw [ite_eq_right (by simp [hne])]
    walk [CedarTyped.genString.complete.obs]
    exact Or.inr ⟨uid.eid, rfl⟩
  · rw [ite_eq_left (by decide)]; walk; simp
  · rw [ite_eq_left (by decide)]; walk; simp

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
  rw [ite_eq_left (by simp [hff])]
  exact ⟨b, hb, rfl⟩

theorem ruleAnd_both (ha : some a ∈ (f.bool c).support) (hff : a.ty ≠ .bool .ff)
    (hb : some b ∈ (f.bool (c ∪ a.out)).support) :
    ofR (.and a.e b.e) (typeOfAnd (a.tx, a.out) b.res) ∈ (ruleAnd f c).support := by
  rw [SPMF.mem_support_iff_may, ruleAnd]
  walk [(supp_complete (f.bool c)).obs, (supp_complete (f.bool (c ∪ a.out))).obs]
  refine ⟨some a, ha, ?_⟩; dsimp only
  rw [ite_eq_right (by simpa using hff)]
  exact ⟨some b, hb, rfl⟩

theorem ruleOr_tt (ha : some a ∈ (f.bool c).support) (htt : a.ty = .bool .tt)
    (hb : b ∈ f.any.support) :
    ofR (.or a.e b) (typeOfOr (a.tx, a.out) dead) ∈ (ruleOr f c).support := by
  rw [SPMF.mem_support_iff_may, ruleOr]
  walk [(supp_complete (f.bool c)).obs, (supp_complete f.any).obs]
  refine ⟨some a, ha, ?_⟩; dsimp only
  rw [ite_eq_left (by simp [htt])]
  exact ⟨b, hb, rfl⟩

theorem ruleOr_both (ha : some a ∈ (f.bool c).support) (htt : a.ty ≠ .bool .tt)
    (hb : some b ∈ (f.bool c).support) :
    ofR (.or a.e b.e) (typeOfOr (a.tx, a.out) b.res) ∈ (ruleOr f c).support := by
  rw [SPMF.mem_support_iff_may, ruleOr]
  walk [(supp_complete (f.bool c)).obs]
  refine ⟨some a, ha, ?_⟩; dsimp only
  rw [ite_eq_right (by simpa using htt)]
  exact ⟨some b, hb, rfl⟩

theorem ruleIte_tt (hg : some g ∈ (f.bool c).support) (htt : g.ty = .bool .tt)
    (ht : some t ∈ (branch (c ∪ g.out)).support) (he : e ∈ f.any.support) :
    ofR (.ite g.e t.e e) (typeOfIf (g.tx, g.out) t.res dead) ∈ (ruleIte f c branch).support := by
  rw [SPMF.mem_support_iff_may, ruleIte]
  walk [(supp_complete (f.bool c)).obs, (supp_complete f.any).obs,
    fun c' => (supp_complete (branch c')).obs]
  refine ⟨some g, hg, ?_⟩; dsimp only
  rw [ite_eq_left (by simp [htt])]
  exact ⟨some t, ht, e, he, rfl⟩

theorem ruleIte_ff (hg : some g ∈ (f.bool c).support) (hff : g.ty = .bool .ff)
    (he : some e ∈ (branch c).support) (ht : t ∈ f.any.support) :
    ofR (.ite g.e t e.e) (typeOfIf (g.tx, g.out) dead e.res) ∈ (ruleIte f c branch).support := by
  rw [SPMF.mem_support_iff_may, ruleIte]
  walk [(supp_complete (f.bool c)).obs, (supp_complete f.any).obs,
    fun c' => (supp_complete (branch c')).obs]
  refine ⟨some g, hg, ?_⟩; dsimp only
  rw [ite_eq_right (by simp [hff]), ite_eq_left (by simp [hff])]
  exact ⟨some e, he, t, ht, rfl⟩

theorem ruleIte_any (hg : some g ∈ (f.bool c).support) (htt : g.ty ≠ .bool .tt)
    (hff : g.ty ≠ .bool .ff) (ht : some t ∈ (branch (c ∪ g.out)).support)
    (he : some e ∈ (branch c).support) :
    ofR (.ite g.e t.e e.e) (typeOfIf (g.tx, g.out) t.res e.res) ∈ (ruleIte f c branch).support := by
  rw [SPMF.mem_support_iff_may, ruleIte]
  walk [(supp_complete (f.bool c)).obs, (supp_complete f.any).obs,
    fun c' => (supp_complete (branch c')).obs]
  refine ⟨some g, hg, ?_⟩; dsimp only
  rw [ite_eq_right (by simpa using htt), ite_eq_right (by simpa using hff)]
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
    rw [ite_eq_right (hn (a, j) (by simp))]
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

theorem ruleHasTag_complete (he : ety ∈ CedarWide.entityTypes)
    (ha : some a ∈ (f.atTy c (.entity ety)).support) (hb : some b ∈ (f.atTy c .string).support) :
    ofR (.binaryApp .hasTag a.e b.e) (typeOfBinaryApp .hasTag a.tx b.tx a.e b.e c env) ∈
      (ruleHasTag f c).support := by
  rw [SPMF.mem_support_iff_may, ruleHasTag]
  walk [fun op t₁ t₂ => (supp_complete (binary f c op t₁ t₂)).obs]
  exact ⟨ety, he, binary_complete f ha hb⟩

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
    | (simp [lub_ctx_addr, lub_addr_ctx] at h)
    | (simp [lub?, userT, groupT, photoT, albumT, actionT] at h)

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

/-- Reduces membership in `stepBool f c` to a disjunction over its branches, each rule opaque. -/
macro "step_bool" : tactic => `(tactic| (
  rw [SPMF.mem_support_iff_may]; unfold stepBool pick
  split <;> simp only [List.append_nil, List.cons_append, List.nil_append] <;>
  walk [(supp_complete (ruleAnd _ _)).obs, (supp_complete (ruleOr _ _)).obs,
    (supp_complete (ruleIte _ _ _)).obs, (supp_complete (ruleHas _ _)).obs,
    (supp_complete (ruleHasTag _ _)).obs, (supp_complete (ruleExtHas _ _)).obs,
    (supp_complete (ruleRecordHas _ _)).obs, fun ty => (supp_complete (ruleRecordGet _ _ ty)).obs,
    fun ty => (supp_complete (ruleRead _ _ ty)).obs,
    fun op t => (supp_complete (unary _ _ op t)).obs,
    fun op t₁ t₂ => (supp_complete (binary _ _ op t₁ t₂)).obs,
    fun fn tys => (supp_complete (call _ _ fn tys)).obs,
    fun c' => (supp_complete (Fam.bool _ c')).obs, CedarTyped.genBool.complete.obs,
    genName_complete.obs, fun n => (supp_complete (genPattern (G := SPMF) n)).obs,
    (supp_complete (genPrim (G := SPMF))).obs]))

open Lean in
/-- Picks the `n`th disjunct (from 0) of a right-nested disjunction. -/
macro "nth_or " n:num : tactic => do
  let mut t ← `(tactic| first | apply Or.inl | skip)
  for _ in [0:n.getNat] do
    t ← `(tactic| (apply Or.inr; $t))
  return t

/-- Reduces membership in `stepAt f c ty` to a disjunction over its branches, each rule opaque. -/
macro "step_at" : tactic => `(tactic| (
  rw [SPMF.mem_support_iff_may]; unfold stepAt pick construct
  (try split) <;> simp only [List.append_nil, List.cons_append, List.nil_append] <;>
  walk [fun ty => (supp_complete (leaf (G := SPMF) _ ty)).obs, (supp_complete (ruleIte _ _ _)).obs,
    fun ty => (supp_complete (ruleRecordGet _ _ ty)).obs,
    fun ty => (supp_complete (ruleRead _ _ ty)).obs,
    fun elt => (supp_complete (ruleSet _ _ elt)).obs,
    fun op t => (supp_complete (unary _ _ op t)).obs,
    fun op t₁ t₂ => (supp_complete (binary _ _ op t₁ t₂)).obs,
    fun fn tys => (supp_complete (call _ _ fn tys)).obs]))

theorem typeOf_unaryApp' (hx : typeOf x c env = .ok (tx, cx)) :
    typeOf (.unaryApp op x) c env = typeOfUnaryApp op tx := by
  simp [typeOf, hx]

theorem fam_fuel : (fam (G := SPMF) n).fuel = n := by cases n <;> rfl

theorem entity_mem_tys (h : CedarType.entity ety ∈ valueTypes) : CedarType.entity ety ∈ entityTys := by
  simp [valueTypes, setElts, entityTys] at h ⊢; exact h

theorem set_value (h : CedarType.set ty ∈ valueTypes) : ty ∈ setElts := by
  simp [valueTypes, setElts, entityTys] at h ⊢; exact h

theorem typeOfHasAttr_bool (h : typeOfHasAttr ty x a c env = .ok (tx, c')) :
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
    · split at h <;> simp [ok, err] at h; obtain ⟨rfl, -⟩ := h; exact ⟨_, rfl⟩
  · simp [err] at h

theorem base_of_U (hu : TyU c t) (hb : (∃ ety, t = .entity ety) ∨ (∃ rty, t = .record rty)) :
    t ∈ baseTypes c := by
  rcases hu with ⟨b, rfl⟩ | ⟨hv, hi⟩
  · rcases hb with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
  rcases hb with ⟨ety, rfl⟩ | ⟨rty, rfl⟩
  · simp only [baseTypes, List.mem_append]; exact Or.inl (Or.inl (entity_mem_tys hv))
  · simp [valueTypes, setElts, entityTys, CedarWide.entityTypes] at hv
    rcases hv with rfl | rfl
    · simp [baseTypes]
    · simp [baseTypes, hi]

/-! ### The schema's attributes -/

theorem find?_make_mem {L : List (Attr × QualifiedType)} (h : (Map.make L).find? a = some q) :
    q ∈ L.map Prod.snd := by
  rw [Map.make_find?_eq_list_find?] at h
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
  exact List.mem_map.mpr ⟨p, List.mem_of_find?_eq_some hp, rfl⟩

theorem attrs?_mem (h : env.ets.attrs? ety = some rty) :
    rty ∈ [Map.empty, groupAttrs, photoAttrs, userAttrs] := by
  rw [ets_eq] at h
  simp only [EntitySchema.attrs?, Map.find?, Map.toList, List.find?] at h
  cases h1 : albumT == ety <;> cases h2 : groupT == ety <;> cases h3 : photoT == ety <;>
    cases h4 : userT == ety <;> simp_all [EntitySchemaEntry.attrs]

/-- Every attribute of a base type has a type the generator builds, a boolean one `anyBool`. -/
theorem attr_cases (hb : bt ∈ valueTypes) (h : attrTy bt a = some q) :
    q.getType ∈ valueTypes ∨ q.getType = .bool .anyBool := by
  have key : ∀ L : List (Attr × QualifiedType),
      (∀ q ∈ L.map Prod.snd, q.getType ∈ valueTypes ∨ q.getType = .bool .anyBool) →
      (Map.make L).find? a = some q → q.getType ∈ valueTypes ∨ q.getType = .bool .anyBool :=
    fun L hL h => hL q (find?_make_mem h)
  have hm : ∀ rty ∈ [Map.empty, groupAttrs, photoAttrs, userAttrs, ctxTy, addrTy],
      rty.find? a = some q → q.getType ∈ valueTypes ∨ q.getType = .bool .anyBool := by
    intro rty hr hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [Map.empty, Map.find?, Map.toList] at hf
    all_goals refine key _ ?_ hf
    all_goals simp [Qualified.getType, valueTypes, setElts, entityTys, CedarWide.entityTypes]
  unfold attrTy at h
  split at h
  · rename_i rty
    refine hm rty ?_ h
    simp [valueTypes, setElts, entityTys, CedarWide.entityTypes] at hb
    rcases hb with rfl | rfl <;> simp
  · obtain ⟨rty, hr, hf⟩ := Option.bind_eq_some_iff.mp h
    exact hm rty (by have := attrs?_mem hr; simp at this ⊢; tauto) hf
  · simp at h

/-! ### Reads -/

theorem getAttr_ty (h : typeOfGetAttr tx x a c env = .ok (t, c')) :
    ∃ q, attrTy tx.typeOf a = some q ∧ t.typeOf = q.getType ∧ c' = ∅ := by
  unfold typeOfGetAttr at h
  split at h
  · rename_i rty hrty
    simp only [getAttrInRecord] at h
    split at h <;> (try split at h) <;> simp [ok, err, bind, Except.bind] at h <;>
      (obtain ⟨rfl, rfl⟩ := h
       first
         | exact ⟨.required _, by simp only [attrTy, hrty]; assumption, rfl, rfl⟩
         | exact ⟨.optional _, by simp only [attrTy, hrty]; assumption, rfl, rfl⟩)
  · rename_i ety hety
    split at h
    · rename_i rty hrty
      simp only [getAttrInRecord] at h
      split at h <;> (try split at h) <;> simp [ok, err, bind, Except.bind] at h <;>
        (obtain ⟨rfl, rfl⟩ := h
         first
           | exact ⟨.required _, by simp only [attrTy, hety, hrty, Option.bind_some]; assumption, rfl, rfl⟩
           | exact ⟨.optional _, by simp only [attrTy, hety, hrty, Option.bind_some]; assumption, rfl, rfl⟩)
    · simp [err] at h
  · simp [err] at h

theorem mem_requiredReads (hbt : bt ∈ baseTypes c) (h : attrTy bt a = some (.required t))
    (hm : ∃ q, (a, q) ∈ CedarWide.attrsOf bt) : (bt, a) ∈ requiredReads c t := by
  simp only [requiredReads, List.mem_flatMap, List.mem_filterMap]
  obtain ⟨q, hq⟩ := hm
  exact ⟨bt, hbt, (a, q), hq, by simp [h]⟩

theorem attrsOf_of (h : attrTy bt a = some q) : (a, q) ∈ CedarWide.attrsOf bt := by
  unfold attrTy at h
  split at h
  · exact Map.find?_mem_toList h
  · obtain ⟨rty, hr, hf⟩ := Option.bind_eq_some_iff.mp h
    simp only [CedarWide.attrsOf, hr, Option.map_some, Option.getD_some]
    exact Map.find?_mem_toList hf
  · simp at h

theorem mem_capReads' (hc : (x, Key.attr a) ∈ c) (hp : pathTx c x = some tx)
    (h : attrTy tx.typeOf a = some q) : (x, tx, a) ∈ capReads c q.getType := by
  simp only [capReads, List.mem_filterMap]
  exact ⟨(x, .attr a), hc, by simp [hp, h]⟩

theorem pathTx_complete (hp : IsPath x) : typeOf x c env = .ok (tx, cx) → pathTx c x = some tx := by
  induction hp generalizing tx cx with
  | var v => intro h; simp only [typeOf] at h; simp [pathTx, h]
  | lit p => intro h; simp only [typeOf] at h; simp [pathTx, h]
  | @getAttr x a _ ih =>
    intro h
    obtain ⟨-, t₁, c₁, h₁, -⟩ := Cedar.Thm.type_of_getAttr_inversion h
    rw [typeOf_getAttr h₁] at h
    simp [pathTx, ih h₁, h]

theorem readable_of_req (h : r ∈ requiredReads c t) : readable c t = true := by
  have : requiredReads c t ≠ [] := List.ne_nil_of_mem h
  simp [readable, this]

theorem readable_of_cap (h : r ∈ capReads c t) : readable c t = true := by
  have : capReads c t ≠ [] := List.ne_nil_of_mem h
  simp [readable, this]

theorem path_value (hp : IsPath x) :
    typeOf x c env = .ok (tx, cx) → ((∃ ety, tx.typeOf = .entity ety) ∨ (∃ rty, tx.typeOf = .record rty)) →
    tx.typeOf ∈ valueTypes := by
  induction hp generalizing tx cx with
  | var v =>
    intro h _; simp only [typeOf] at h
    cases v <;> simp [typeOfVar, ok, reqty_eq] at h <;> obtain ⟨rfl, -⟩ := h <;>
      simp [TypedExpr.typeOf, valueTypes, entityTys, CedarWide.entityTypes, view]
  | lit p =>
    intro h hb
    have r := reach_lit (n := 0) h
    rcases r.tyU with ⟨b, hh⟩ | ⟨hh, _⟩
    · have hh' : tx.typeOf = .bool b := hh
      rcases hb with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [hh'] at h <;> cases h
    · exact hh
  | @getAttr x a _ ih =>
    intro h hb
    obtain ⟨-, t₁, c₁, h₁, -, hbase⟩ := Cedar.Thm.type_of_getAttr_inversion h
    rw [typeOf_getAttr h₁] at h
    obtain ⟨q, hq, hty, -⟩ := getAttr_ty h
    rcases attr_cases (ih h₁ hbase) hq with hv | hv
    · rw [hty]; exact hv
    · rw [hty, hv] at hb; rcases hb with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h

/-! ### Tags -/

theorem tags?_string (h : env.ets.tags? ety = some (some ty)) : ty = .string := by
  rw [ets_eq] at h
  simp only [EntitySchema.tags?, Map.find?, Map.toList, List.find?] at h
  cases h1 : albumT == ety <;> cases h2 : groupT == ety <;> cases h3 : photoT == ety <;>
    cases h4 : userT == ety <;> simp_all [EntitySchemaEntry.tags?]

theorem getTag_inv (h : typeOfBinaryApp .getTag tx tt x t c env = .ok (r, c')) :
    ∃ ety, tx.typeOf = .entity ety ∧ tt.typeOf = .string ∧ env.ets.tags? ety = some (some .string) ∧
      (x, Key.tag t) ∈ c ∧ r.typeOf = .string := by
  unfold typeOfBinaryApp at h
  split at h <;> (try contradiction); try (simp at h; done)
  rename_i ety _ h₁ h₂
  simp only [typeOfGetTag] at h
  split at h
  · simp [err] at h
  · rename_i ty hty
    split at h
    · simp [ok, bind, Except.bind] at h
      obtain ⟨rfl, -⟩ := h
      have := tags?_string hty; subst this
      exact ⟨ety, h₁, h₂, hty, by assumption, rfl⟩
    · simp [err] at h
  · simp [err] at h

theorem mem_tagReads' (hc : (x, Key.tag t) ∈ c) (hx : pathTx c x = some tx) (ht : pathTx c t = some tt)
    (he : tx.typeOf = .entity ety) (hs : tt.typeOf = .string)
    (htags : env.ets.tags? ety = some (some .string)) : (x, tx, t, tt) ∈ tagReads c := by
  simp only [tagReads, List.mem_filterMap]
  exact ⟨(x, .tag t), hc, by simp [hx, ht, he, hs, htags]⟩

/-! ### Multi-attribute `has` chains, from typing -/

theorem chainOK_none : (l : List Attr) → l ≠ [] → ChainOK none l
  | [_], _ => trivial
  | _ :: b :: l, _ => chainOK_none (b :: l) (by simp)

theorem hasAttr_ff (h : typeOfHasAttr tx x a c env = .ok (th, ci)) :
    th.typeOf = .bool .ff ↔ attrTy tx.typeOf a = none := by
  unfold typeOfHasAttr at h
  split at h
  · rename_i rty hrty
    simp only [hasAttrInRecord] at h
    split at h <;> (try split at h) <;> simp [ok, bind, Except.bind] at h <;>
      (obtain ⟨rfl, -⟩ := h; simp_all [attrTy, TypedExpr.typeOf])
  · rename_i ety hety
    split at h
    · rename_i rty hrty
      simp only [hasAttrInRecord] at h
      split at h <;> (try split at h) <;> simp [ok, bind, Except.bind] at h <;>
        (obtain ⟨rfl, -⟩ := h; simp_all [attrTy, TypedExpr.typeOf])
    · rename_i hrty
      split at h <;> simp [ok, err] at h
      obtain ⟨rfl, -⟩ := h; simp_all [attrTy, TypedExpr.typeOf]
  · simp [err] at h

theorem hasAttr_err (hne : ∀ ety, ty.typeOf ≠ .entity ety) (hnr : ∀ rty, ty.typeOf ≠ .record rty) :
    ∃ e, typeOfHasAttr ty x a c env = .error e := by
  unfold typeOfHasAttr
  split
  · rename_i rty h; exact absurd h (hnr rty)
  · rename_i ety h; exact absurd h (hne ety)
  · exact ⟨_, rfl⟩

theorem extHas_err (hne : ∀ ety, ty.typeOf ≠ .entity ety) (hnr : ∀ rty, ty.typeOf ≠ .record rty) :
    ∃ e, typeOfExtHasAttr ty x (a :: atts) c env = .error e := by
  obtain ⟨e, he⟩ := hasAttr_err (x := x) (a := a) (c := c) hne hnr
  cases atts <;> simp [typeOfExtHasAttr, he, bind, Except.bind]

theorem chainOK_of : (atts : List Attr) → (tx : TypedExpr) → (x : Spec.Expr) → (c : Capabilities) →
    (a : Attr) → tx.typeOf ∈ valueTypes →
    typeOfExtHasAttr tx x (a :: atts) c env = .ok r → ChainOK (some tx.typeOf) (a :: atts)
  | [], _, _, _, _, _, _ => trivial
  | b :: atts, tx, x, c, a, hv, h => by
    simp only [typeOfExtHasAttr] at h
    cases hh : typeOfHasAttr tx x a c env with
    | error e => simp [hh, bind, Except.bind] at h
    | ok p =>
      obtain ⟨th, ci⟩ := p
      have hff := hasAttr_ff hh
      simp only [ChainOK]
      cases hq : attrTy tx.typeOf a with
      | none => exact chainOK_none _ (by simp)
      | some q =>
        have hnf : th.typeOf ≠ .bool .ff := fun h => by rw [hff.mp h] at hq; cases hq
        simp only [Option.map_some]
        simp only [hh, bind, Except.bind] at h
        cases hg : typeOfGetAttr tx x a (c ∪ ci) env with
        | error e =>
          simp only [hg] at h; first | exact absurd ‹_› hnf | simp at h
        | ok p =>
          obtain ⟨tn, cn⟩ := p
          obtain ⟨q', hq', hty, -⟩ := getAttr_ty hg
          rw [hq] at hq'; cases hq'
          cases hr : typeOfExtHasAttr tn (.getAttr x a) (b :: atts) (c ∪ ci) env with
          | error e =>
            simp only [hg, hr] at h; first | exact absurd ‹_› hnf | simp at h
          | ok p =>
            have hvn := attr_cases hv hq
            rw [← hty] at hvn ⊢
            rcases hvn with hvn | hvn
            · by_cases he : ∃ ety, tn.typeOf = .entity ety
              · obtain ⟨ety, he⟩ := he
                have := chainOK_of atts tn _ _ b hvn hr; rw [he] at this ⊢; exact this
              · by_cases hrr : ∃ rty, tn.typeOf = .record rty
                · obtain ⟨rty, hrr⟩ := hrr
                  have := chainOK_of atts tn _ _ b hvn hr; rw [hrr] at this ⊢; exact this
                · obtain ⟨e, he'⟩ := extHas_err (x := .getAttr x a) (a := b) (atts := atts)
                    (c := c ∪ ci) (fun ety h => he ⟨ety, h⟩) (fun rty h => hrr ⟨rty, h⟩)
                  rw [he'] at hr; cases hr
            · obtain ⟨e, he'⟩ := extHas_err (ty := tn) (x := .getAttr x a) (a := b) (atts := atts)
                (c := c ∪ ci) (by intro _ h; rw [hvn] at h; cases h) (by intro _ h; rw [hvn] at h; cases h)
              rw [he'] at hr; cases hr

theorem extHas_base (h : typeOfExtHasAttr tx x (a :: atts) c env = .ok r) :
    (∃ ety, tx.typeOf = .entity ety) ∨ (∃ rty, tx.typeOf = .record rty) := by
  by_contra hn
  push Not at hn
  obtain ⟨e, he⟩ := extHas_err (x := x) (a := a) (atts := atts) (c := c) hn.1 hn.2
  rw [he] at h; cases h

theorem reach_extHas (hne : atts ≠ []) (hl : atts.length ≤ n + 1)
    (ihx : ∀ {tx out}, typeOf x c env = .ok (tx, out) → ReachF (fam (G := SPMF) n) c ⟨x, tx, out⟩) :
    typeOf (.extHasAttr x a atts) c env = .ok (tx, out) →
    ReachF (fam (G := SPMF) (n + 1)) c ⟨.extHasAttr x a atts, tx, out⟩ := by
  intro h
  simp only [typeOf] at h
  cases h₁ : typeOf x c env with
  | error e => simp [h₁, bind, Except.bind] at h
  | ok p =>
    obtain ⟨t₁, c₁⟩ := p
    cases he : typeOfExtHasAttr t₁ x (a :: atts) c env with
    | error e => simp [h₁, he, bind, Except.bind] at h
    | ok q =>
      obtain ⟨bty, c'⟩ := q
      simp [h₁, he, bind, Except.bind, ok] at h; obtain ⟨rfl, rfl⟩ := h
      have r := ihx h₁
      have hbase := extHas_base he
      have hv₁ : t₁.typeOf ∈ valueTypes := by
        rcases r.tyU with ⟨_, hh⟩ | ⟨hh, _⟩
        · have hh' : t₁.typeOf = .bool _ := hh
          rcases hbase with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [hh'] at h <;> cases h
        · exact hh
      have hm := ruleExtHas_complete (fam n) (x := ⟨x, t₁, c₁⟩) (base_of_U r.tyU hbase) (r.value hv₁)
        (by cases atts <;> simp_all) (by rw [fam_fuel]; exact hl) (chainOK_of atts t₁ x c a hv₁ he) he
      refine reach_bool rfl ?_
      rw [fam_succ_bool]; step_bool
      all_goals branch hm

/-! ### Lists of judgments, from typing -/

theorem mapM_typeOf_inv : (xs : List Spec.Expr) → (txs : List TypedExpr) →
    (xs.mapM fun x => justType (typeOf x c env)) = .ok txs →
    ∃ js : List J, js.map J.e = xs ∧ js.map J.tx = txs ∧ ∀ j ∈ js, Judg c j
  | [], txs, h => by
    simp [pure, Except.pure] at h; subst h; exact ⟨[], rfl, rfl, by simp⟩
  | x :: xs, txs, h => by
    simp only [List.mapM_cons] at h
    cases hx : typeOf x c env with
    | error e => simp [hx, justType, Except.map, bind, Except.bind] at h
    | ok p =>
      obtain ⟨tx, cx⟩ := p
      cases hr : xs.mapM (fun x => justType (typeOf x c env)) with
      | error e => rw [hr] at h; simp [hx, justType, Except.map, bind, Except.bind] at h
      | ok tys =>
        rw [hr] at h; simp [hx, justType, Except.map, bind, Except.bind, pure, Except.pure] at h
        subst h
        obtain ⟨js, h₁, h₂, h₃⟩ := mapM_typeOf_inv xs tys hr
        refine ⟨⟨x, tx, cx⟩ :: js, by simp [h₁], by simp [h₂], ?_⟩
        rintro j (_ | ⟨_, hj⟩)
        exacts [hx, h₃ j hj]

theorem set_inv (h : typeOf (.set xs) c env = .ok (tx, out)) :
    ∃ js : List J, js.map J.e = xs ∧ (∀ j ∈ js, Judg c j) ∧ typeOfSet (js.map J.tx) = .ok (tx, out) := by
  simp only [typeOf] at h
  rw [List.mapM₁_eq_mapM (fun x => justType (typeOf x c env))] at h
  cases hm : xs.mapM (fun x => justType (typeOf x c env)) with
  | error e => simp [hm, bind, Except.bind] at h
  | ok txs =>
    simp only [hm, bind, Except.bind] at h
    obtain ⟨js, h₁, h₂, h₃⟩ := mapM_typeOf_inv xs txs hm
    exact ⟨js, h₁, h₃, h₂ ▸ h⟩

theorem call_inv (h : typeOf (.call fn xs) c env = .ok (tx, out)) :
    ∃ js : List J, js.map J.e = xs ∧ (∀ j ∈ js, Judg c j) ∧
      typeOfCall fn (js.map J.tx) (js.map J.e) = .ok (tx, out) := by
  simp only [typeOf] at h
  rw [List.mapM₁_eq_mapM (fun x => justType (typeOf x c env))] at h
  cases hm : xs.mapM (fun x => justType (typeOf x c env)) with
  | error e => simp [hm, bind, Except.bind] at h
  | ok txs =>
    simp only [hm, bind, Except.bind] at h
    obtain ⟨js, h₁, h₂, h₃⟩ := mapM_typeOf_inv xs txs hm
    exact ⟨js, h₁, h₃, by rw [h₁, h₂]; exact h⟩

theorem reach_set (hne : xs ≠ []) (hl : xs.length ≤ n + 1)
    (ih : ∀ x ∈ xs, ∀ {tx out}, typeOf x c env = .ok (tx, out) →
      ReachF (fam (G := SPMF) n) c ⟨x, tx, out⟩)
    (hok : TyOK c (.set xs)) :
    typeOf (.set xs) c env = .ok (tx, out) → ReachF (fam (G := SPMF) (n + 1)) c ⟨.set xs, tx, out⟩ := by
  intro h
  have hu := hok _ _ h
  obtain ⟨-, txs, ty, htx, hall⟩ := Cedar.Thm.type_of_set_inversion h
  obtain ⟨js, hjs, hj, hts⟩ := set_inv h
  subst htx
  have hv : CedarType.set ty ∈ valueTypes := by
    rcases hu with ⟨_, hb⟩ | ⟨hv, _⟩
    · cases hb
    · exact hv
  have hi : inhabited c (.set ty) = true := inhabited_of_ne (by simp)
  have hty : ty ∈ valueTypes := by
    have := set_value hv; simp [setElts, entityTys, CedarWide.entityTypes] at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [valueTypes, setElts, entityTys, CedarWide.entityTypes]
  have hm : ∀ j ∈ js, some j ∈ ((fam (G := SPMF) n).atTy c ty).support := by
    intro j hjm
    have hx : j.e ∈ xs := hjs ▸ List.mem_map_of_mem hjm
    have r := ih j.e hx (hj j hjm)
    obtain ⟨tᵢ, cᵢ, -, hᵢ, hlub⟩ := hall j.e hx
    rw [hj j hjm] at hᵢ; cases hᵢ
    rcases lub_U (c₃ := c) r.tyU (Or.inr ⟨hty, inhabited_of_ne (by
        intro h; subst h; simp [valueTypes, setElts, entityTys] at hv)⟩) hlub with
      ⟨_, _, ⟨_, hb⟩⟩ | ⟨_, h₂, -⟩
    · subst hb; exact absurd hty bool_not_value
    · have := r.value (h₂ ▸ hty); rw [h₂] at this; exact this
  have hlen : 1 ≤ js.length := by
    cases js with
    | nil => simp at hjs; exact absurd hjs hne
    | cons => simp
  have hre := ruleSet_complete (fam n) (elt := ty) hlen
    (by rw [fam_fuel]; have := congrArg List.length hjs; simp at this; omega) hm
  rw [hjs, ofR_ok hts] at hre
  refine reach_val hv hi ?_
  rw [fam_succ_atTy]; step_at
  all_goals branch hre

/-! ### Extension calls -/

theorem forall₂_of : (js : List J) → (tys : List CedarType) →
    (js.map J.tx).map TypedExpr.typeOf = tys → (∀ j ∈ js, ReachF f c j) → (∀ t ∈ tys, t ∈ valueTypes) →
    List.Forall₂ (fun j ty => some j ∈ (f.atTy c ty).support) js tys
  | [], [], _, _, _ => .nil
  | j :: js, ty :: tys, h, hr, hv => by
    simp only [List.map_cons, List.cons.injEq] at h
    refine .cons ?_ (forall₂_of js tys h.2 (fun j hj => hr j (by simp [hj]))
      (fun t ht => hv t (by simp [ht])))
    have := (hr j (by simp)).value (by show j.tx.typeOf ∈ _; rw [h.1]; exact hv ty (by simp))
    rw [show j.ty = ty from h.1] at this; exact this
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h

set_option maxHeartbeats 8000000 in
theorem reach_call (ih : ∀ x ∈ xs, ∀ {tx out}, typeOf x c env = .ok (tx, out) →
      ReachF (fam (G := SPMF) n) c ⟨x, tx, out⟩) :
    typeOf (.call fn xs) c env = .ok (tx, out) →
    ReachF (fam (G := SPMF) (n + 1)) c ⟨.call fn xs, tx, out⟩ := by
  intro h
  obtain ⟨js, hjs, hj, hcall⟩ := call_inv h
  subst hjs
  have hr : ∀ j ∈ js, ReachF (fam (G := SPMF) n) c j := fun j hjm =>
    ih j.e (List.mem_map_of_mem hjm) (hj j hjm)
  have hre := ofR_ok (e := .call fn (js.map J.e)) hcall
  cases fn <;> simp only [typeOfCall] at hcall
  case decimal | ip | datetime | duration =>
    all_goals
      simp only [bind, Except.bind] at hcall
      split at hcall
      · simp at hcall
      · rename_i p hc
        simp only [ok, Except.ok.injEq] at hcall
        unfold typeOfConstructor at hc
        split at hc
        · rename_i s heq
          split at hc
          · rename_i hmk
            obtain ⟨j, rfl⟩ : ∃ j, js = [j] := by
              cases js with
              | nil => simp at heq
              | cons j js => cases js with
                | nil => exact ⟨j, rfl⟩
                | cons => simp at heq
            simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at heq
            have hjj := hj j (by simp)
            simp only [Judg, heq, typeOf, typeOfLit, ok, Function.comp, Except.ok.injEq,
              Prod.mk.injEq] at hjj
            obtain ⟨htx, -⟩ := hjj
            simp only [ok, Except.ok.injEq] at hc; subst hc
            simp only [Prod.mk.injEq] at hcall
            obtain ⟨rfl, rfl⟩ := hcall
            simp only [List.map_cons, List.map_nil, heq, ← htx] at hre ⊢
            refine reach_val (by simp [TypedExpr.typeOf, valueTypes])
              (inhabited_of_ne (by simp [TypedExpr.typeOf])) ?_
            simp only [TypedExpr.typeOf]
            exact fam_leaf (hre ▸ leaf_ext (xt := _) (by simp [ValidArg, hmk]))
          · simp [err] at hc
        · simp [err] at hc
  all_goals split at hcall <;> (try contradiction)
  all_goals rename_i heq
  all_goals simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hcall
  all_goals obtain ⟨rfl, rfl⟩ := hcall
  all_goals
    have hf := forall₂_of (f := fam (G := SPMF) n) (c := c) _ _ heq hr (by simp [valueTypes])
    have hm := hre ▸ call_complete (fam n) hf
    first
      | (refine reach_bool rfl ?_; rw [fam_succ_bool]; step_bool
         all_goals first | branch hm | branch ⟨_, by simp, hm⟩)
      | (refine reach_val (by simp [TypedExpr.typeOf, valueTypes])
           (inhabited_of_ne (by simp [TypedExpr.typeOf])) ?_
         simp only [TypedExpr.typeOf]; rw [fam_succ_atTy]; step_at
         all_goals first | branch hm | branch ⟨_, by simp, hm⟩)

/-! ### Binary operators -/

theorem ety_mem (h : CedarType.entity e ∈ entityTys) : e ∈ CedarWide.entityTypes := by
  simp [entityTys] at h; exact h

theorem setElts_value (h : t ∈ setElts) : t ∈ valueTypes := by
  simp only [setElts, List.mem_append] at h
  simp only [valueTypes, List.mem_append]
  tauto

theorem setElts_ne_addr (h : t ∈ setElts) : t ≠ .record addrTy := by
  simp [setElts, entityTys] at h
  rcases h with rfl | rfl | ⟨_, _, rfl⟩ <;> simp

theorem set_entity (h : CedarType.set (.entity e) ∈ valueTypes) : CedarType.entity e ∈ entityTys := by
  have := set_value h; simp [setElts] at this; exact this

theorem hasTag_bool (h : typeOfHasTag ety x t c env = .ok (r, c')) : ∃ b, r = .bool b := by
  unfold typeOfHasTag at h
  split at h
  · simp [ok] at h; exact ⟨_, h.1.symm⟩
  · split at h <;> simp [ok] at h <;> exact ⟨_, h.1.symm⟩
  · split at h <;> simp [ok, err] at h; exact ⟨_, h.1.symm⟩

theorem ifLub_ok (h : ifLubThenBool t₁ t₂ = .ok (r, c')) :
    r = .bool .anyBool ∧ c' = ∅ ∧ ∃ t, (t₁ ⊔ t₂) = some t := by
  unfold ifLubThenBool at h
  split at h
  · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl, _, by assumption⟩
  · simp [err] at h

theorem typeOfEq_nonlit (h : ¬ ∃ p₁ p₂, x₁ = .lit p₁ ∧ x₂ = .lit p₂) :
    typeOfEq t₁ t₂ x₁ x₂ =
      match t₁.typeOf ⊔ t₂.typeOf with
      | .some _ => ok (.binaryApp .eq t₁ t₂ (.bool .anyBool))
      | .none =>
        match t₁.typeOf, t₂.typeOf with
        | .entity _, .entity _ => ok (.binaryApp .eq t₁ t₂ (.bool .ff))
        | _, _ => err (.lubErr t₁.typeOf t₂.typeOf) := by
  unfold typeOfEq
  split
  · rename_i p₁ p₂; exact absurd ⟨p₁, p₂, rfl, rfl⟩ h
  · rfl

theorem validPrim_of (h : typeOfLit p env = .ok r) : ValidPrim p := by
  cases p with
  | entityUID uid =>
    simp only [typeOfLit] at h
    split at h
    · exact validUID_of (by assumption)
    · simp [err] at h
  | _ => trivial

set_option maxHeartbeats 8000000 in
theorem reach_binary (hop : op ≠ .getTag)
    (iha : ∀ {tx out}, typeOf a c env = .ok (tx, out) → ReachF (fam (G := SPMF) n) c ⟨a, tx, out⟩)
    (ihb : ∀ {tx out}, typeOf b c env = .ok (tx, out) → ReachF (fam (G := SPMF) n) c ⟨b, tx, out⟩) :
    typeOf (.binaryApp op a b) c env = .ok (tx, out) →
    ReachF (fam (G := SPMF) (n + 1)) c ⟨.binaryApp op a b, tx, out⟩ := by
  intro h
  obtain ⟨ta, ca, tb, cb, h₁, h₂, ty, rfl⟩ := Cedar.Thm.type_of_binaryApp_inversion h
  have h' := h; rw [typeOf_binaryApp h₁ h₂] at h'
  have hre := ofR_ok (e := .binaryApp op a b) h'
  have ra := iha h₁; have rb := ihb h₂
  cases op
  case eq =>
    have h'' := h'
    simp only [typeOfBinaryApp] at h''
    by_cases hl : ∃ p₁ p₂, a = .lit p₁ ∧ b = .lit p₂
    · obtain ⟨p₁, p₂, rfl, rfl⟩ := hl
      have hl1 : typeOfLit p₁ env = .ok (ta, ca) := by simpa [typeOf] using h₁
      have hl2 : typeOfLit p₂ env = .ok (tb, cb) := by simpa [typeOf] using h₂
      have hty : ∃ bt, ty = .bool bt := by
        simp only [typeOfEq] at h''
        split at h'' <;> simp [ok, Function.comp] at h'' <;> exact ⟨_, h''.1.symm⟩
      obtain ⟨bt, rfl⟩ := hty
      refine reach_bool rfl ?_
      rw [fam_succ_bool]; step_bool
      all_goals (nth_or 17; exact ⟨p₁, genPrim_complete p₁ (validPrim_of hl1), p₂,
        genPrim_complete p₂ (validPrim_of hl2), by rw [hl1, hl2]; exact hre⟩)
    · rw [typeOfEq_nonlit hl] at h''
      split at h''
      · rename_i t hlub
        simp only [ok, Except.ok.injEq, Prod.mk.injEq, TypedExpr.binaryApp.injEq,
          true_and] at h''
        obtain ⟨rfl, rfl⟩ := h''
        refine reach_bool rfl ?_
        rw [fam_succ_bool]; step_bool
        all_goals rcases lub_U ra.tyU rb.tyU hlub with ⟨⟨b₁, hb₁⟩, ⟨b₂, hb₂⟩, -⟩ | ⟨hv, h₁', h₂'⟩
        all_goals first
          | (nth_or 15; exact ⟨some _, ra.bool hb₁, some _, rb.bool hb₂, hre⟩)
          | (have hi : inhabited c t = true := by
               rcases ra.tyU with ⟨_, hb⟩ | ⟨_, hi⟩
               · rw [h₁'] at hb; rw [hb] at hv; exact absurd hv bool_not_value
               · rw [h₁'] at hi; exact hi
             have ma := ra.value (by rw [h₁']; exact hv); rw [h₁'] at ma
             have mb := rb.value (by rw [h₂']; exact hv); rw [h₂'] at mb
             nth_or 14
             exact ⟨t, List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hv, hi⟩),
               hre ▸ binary_complete (fam n) ma mb⟩)
      · split at h''
        · rename_i e₁ e₂ _ hta htb
          simp only [ok, Except.ok.injEq, Prod.mk.injEq, TypedExpr.binaryApp.injEq,
            true_and] at h''
          obtain ⟨rfl, rfl⟩ := h''
          have va := ra.not_bool _ (by intro b hb; simp only [J.ty] at hb; rw [hta] at hb; cases hb)
          have vb := rb.not_bool _ (by intro b hb; simp only [J.ty] at hb; rw [htb] at hb; cases hb)
          have ma := va.2.2; have mb := vb.2.2
          simp only [J.ty] at ma mb va vb
          rw [hta] at ma va; rw [htb] at mb vb
          refine reach_bool rfl ?_
          rw [fam_succ_bool]; step_bool
          all_goals (nth_or 16; exact ⟨_, entity_mem_tys va.1, _, entity_mem_tys vb.1,
            hre ▸ binary_complete (fam n) ma mb⟩)
        · simp [err] at h''
  case getTag => exact absurd rfl hop
  case contains =>
    have h'' := h'
    unfold typeOfBinaryApp at h''
    split at h'' <;> (try contradiction)
    rename_i ty₃ _ hta
    have va := ra.not_bool _ (by intro b hb; simp only [J.ty] at hb; rw [hta] at hb; cases hb)
    have ma := va.2.2
    simp only [J.ty] at ma va; rw [hta] at ma va
    have h3 := set_value va.1
    simp only [bind, Except.bind] at h''
    split at h''
    · simp at h''
    · rename_i p hl
      obtain ⟨hp1, -, t, hlub⟩ := ifLub_ok (r := p.1) (c' := p.2) hl
      simp only [ok, Except.ok.injEq, Prod.mk.injEq, TypedExpr.binaryApp.injEq, true_and] at h''
      obtain ⟨rfl, rfl⟩ := h''
      rcases lub_U (c₃ := c) rb.tyU (Or.inr ⟨setElts_value h3, inhabited_of_ne (setElts_ne_addr h3)⟩)
        hlub with ⟨_, ⟨b', hb'⟩, _⟩ | ⟨hv, htb, hty⟩
      · rw [hb'] at h3; simp [setElts, entityTys] at h3
      · subst hty
        have mb := rb.value (by rw [htb]; exact hv)
        rw [htb] at mb
        have hm := hre ▸ binary_complete (fam n) ma mb
        refine reach_bool (b := .anyBool) (by simp [TypedExpr.typeOf, hp1]) ?_
        rw [fam_succ_bool]; step_bool
        all_goals (nth_or 19; exact ⟨_, h3, hm⟩)
  all_goals have h'' := h'
  all_goals unfold typeOfBinaryApp at h''
  all_goals split at h'' <;> (try contradiction)
  all_goals rename_i hta htb
  all_goals
    have va := ra.not_bool _ (by intro b hb; simp only [J.ty] at hb; rw [hta] at hb; cases hb)
    have vb := rb.not_bool _ (by intro b hb; simp only [J.ty] at hb; rw [htb] at hb; cases hb)
    have ma := va.2.2; have mb := vb.2.2
    simp only [J.ty] at ma mb va vb
    rw [hta] at ma va; rw [htb] at mb vb
  case h_2 | h_3 | h_6 | h_7 | h_8 | h_9 | h_10 | h_11 =>
    all_goals
      simp only [ok, Except.ok.injEq, Prod.mk.injEq, TypedExpr.binaryApp.injEq, true_and] at h''
      obtain ⟨rfl, rfl⟩ := h''
      have hm := hre ▸ binary_complete (fam n) ma mb
      refine reach_bool rfl ?_
      rw [fam_succ_bool]; step_bool
      all_goals first
        | (nth_or 13; exact ⟨_, by simp, _, by simp, hm⟩)
        | (nth_or 18; exact ⟨_, entity_mem_tys vb.1, _, entity_mem_tys va.1, _, by simp, hm⟩)
        | (nth_or 18; exact ⟨_, set_entity vb.1, _, entity_mem_tys va.1, _, by simp, hm⟩)
  case h_12 | h_13 | h_14 =>
    all_goals
      simp only [ok, Except.ok.injEq, Prod.mk.injEq, TypedExpr.binaryApp.injEq, true_and] at h''
      obtain ⟨rfl, rfl⟩ := h''
      have hm := hre ▸ binary_complete (fam n) ma mb
      refine reach_val (by simp [TypedExpr.typeOf, valueTypes])
        (inhabited_of_ne (by simp [TypedExpr.typeOf])) ?_
      simp only [TypedExpr.typeOf]; rw [fam_succ_atTy]; step_at
      all_goals branch ⟨_, by simp, hm⟩
  case h_4 =>
    simp only [bind, Except.bind] at h''
    split at h''
    · simp at h''
    · rename_i p hht
      obtain ⟨bt, hbt⟩ := hasTag_bool (r := p.1) (c' := p.2) hht
      simp only [ok, Except.ok.injEq, Prod.mk.injEq, TypedExpr.binaryApp.injEq, true_and] at h''
      obtain ⟨rfl, rfl⟩ := h''
      have hm := hre ▸ ruleHasTag_complete (fam n) (ety_mem (entity_mem_tys va.1)) ma mb
      refine reach_bool hbt ?_
      rw [fam_succ_bool]; step_bool
      all_goals (nth_or 5; exact hm)
  case h_16 | h_17 =>
    all_goals
      simp only [bind, Except.bind] at h''
      split at h''
      · simp at h''
      · rename_i p hl
        obtain ⟨hp1, -, t, hlub⟩ := ifLub_ok (r := p.1) (c' := p.2) hl
        simp only [ok, Except.ok.injEq, Prod.mk.injEq, TypedExpr.binaryApp.injEq, true_and] at h''
        obtain ⟨rfl, rfl⟩ := h''
        obtain ⟨h3, h4⟩ := lub_value (setElts_value (set_value va.1)) (setElts_value (set_value vb.1)) hlub
        subst h3; subst h4
        have hm := hre ▸ binary_complete (fam n) ma mb
        refine reach_bool (b := .anyBool) (by simp [TypedExpr.typeOf, hp1]) ?_
        rw [fam_succ_bool]; step_bool
        all_goals (nth_or 20; exact ⟨_, set_value va.1, _, by simp, hm⟩)

end CedarGen
