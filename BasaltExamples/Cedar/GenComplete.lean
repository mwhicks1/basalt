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

theorem insertIdx_mid {α} : (l₁ l₂ : List α) → (x : α) → (l₁ ++ l₂).insertIdx l₁.length x = l₁ ++ x :: l₂
  | [], l₂, x => by simp
  | y :: l₁, l₂, x => by simp [List.insertIdx_succ_cons, insertIdx_mid l₁ l₂ x]

theorem find?_make_some {L : List (Attr × QualifiedType)} (h : (Map.make L).find? a = some q) :
    (a, q) ∈ L := by
  rw [Map.make_find?_eq_list_find?] at h
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
  have hm := List.mem_of_find?_eq_some hp
  have ha := List.find?_some hp
  simp at ha; subst ha; exact hm

theorem reach_getRec (hl : fs.length ≤ n + 1) (hnd : (fs.map Prod.fst).Nodup)
    (ih : ∀ p ∈ fs, ∀ {tx out}, typeOf p.2 c env = .ok (tx, out) →
      ReachF (fam (G := SPMF) n) c ⟨p.2, tx, out⟩)
    (hok : TyOK c (.getAttr (.record fs) a)) :
    typeOf (.getAttr (.record fs) a) c env = .ok (tx, out) →
    ReachF (fam (G := SPMF) (n + 1)) c ⟨.getAttr (.record fs) a, tx, out⟩ := by
  intro h
  have hu := hok _ _ h
  obtain ⟨-, tr, cr, h₁, -, -⟩ := Cedar.Thm.type_of_getAttr_inversion h
  obtain ⟨js, hjs, hj, hrec⟩ := record_inv h₁
  have h' := h; rw [typeOf_getAttr h₁] at h'
  obtain ⟨q, hq, hty, -⟩ := getAttr_ty h'
  have htr : tr = (recordOf js).2 := by rw [hrec]
  subst htr
  have hq' : (Map.make (js.map fun p => (p.1, Qualified.required p.2.tx.typeOf))).find? a = some q :=
    hq
  have hmem := find?_make_some hq'
  obtain ⟨⟨a', j⟩, hp, hpq⟩ := List.mem_map.mp hmem
  simp only [Prod.mk.injEq] at hpq
  obtain ⟨rfl, rfl⟩ := hpq
  obtain ⟨l₁, l₂, hsplit⟩ := List.append_of_mem hp
  have hnd' : ((a', j) :: (l₁ ++ l₂)).map Prod.fst |>.Nodup := by
    have := names_eq hjs ▸ hnd
    rw [hsplit, List.map_append, List.map_cons] at this
    simpa using List.nodup_middle.mp this
  have hr := fields_reach hjs hj ih
  have hrj := hr (a', j) hp
  have hrest : ∀ p ∈ l₁ ++ l₂, ReachF (fam (G := SPMF) n) c p.2 := fun p hp' =>
    hr p (by rw [hsplit]; simp at hp' ⊢; tauto)
  have hlen : (l₁ ++ l₂).length ≤ (fam (G := SPMF) n).fuel := by
    rw [fam_fuel]; have := congrArg List.length hjs; rw [hsplit] at this; simp at this hl ⊢; omega
  simp only [List.map_cons, List.nodup_cons] at hnd'
  have hre := ofR_ok (e := .getAttr (.record fs) a') h'
  have hjs' : (l₁ ++ l₂).insertIdx l₁.length (a', j) = js := by rw [insertIdx_mid, hsplit]
  simp only [Qualified.getType] at hty
  rcases hu with ⟨bt, hbt⟩ | ⟨hv, hi⟩
  · have hm := ruleRecordGet_complete (fam n) (ty := .bool .anyBool) (j := j) (a := a') (i := l₁.length)
      (Or.inl ⟨⟨_, rfl⟩, hrj.bool (b := bt) (by show j.tx.typeOf = _; rw [← hty]; exact hbt)⟩) hlen hnd'.2 hnd'.1 hrest
      (by simp)
    dsimp only at hm; rw [hjs', hrec] at hm
    rw [hre] at hm
    refine reach_bool hbt ?_
    rw [fam_succ_bool]; step_bool
    all_goals (nth_or 8; exact hm)
  · have hm := ruleRecordGet_complete (fam n) (ty := tx.typeOf) (j := j) (a := a') (i := l₁.length)
      (Or.inr ⟨fun b hb => by rw [hb] at hv; exact bool_not_value hv,
        by have := hrj.value (by rw [J.ty, ← hty]; exact hv); rw [J.ty, ← hty] at this; exact this⟩)
      hlen hnd'.2 hnd'.1 hrest (by simp)
    dsimp only at hm; rw [hjs', hrec] at hm
    rw [hre] at hm
    refine reach_val hv hi ?_
    rw [fam_succ_atTy]; unfold stepAt
    exact mem_pick (w := 1) (g := fun _ => ruleRecordGet (fam n) c tx.typeOf) (by simp) (by decide) hm

/-! ### Unary operators, `has`, reads, and tags -/

theorem reach_unary (hp : ∀ p, op = .like p → p.length ≤ n)
    (ihx : ∀ {tx out}, typeOf x c env = .ok (tx, out) → ReachF (fam (G := SPMF) n) c ⟨x, tx, out⟩) :
    typeOf (.unaryApp op x) c env = .ok (tx, out) →
    ReachF (fam (G := SPMF) (n + 1)) c ⟨.unaryApp op x, tx, out⟩ := by
  intro h
  obtain ⟨rfl, t₁, ty, c₁, rfl, h₁, hop⟩ := Cedar.Thm.type_of_unary_inversion h
  have r := ihx h₁
  have hr : ofR (.unaryApp op x) (typeOfUnaryApp op t₁) = some ⟨_, .unaryApp op t₁ ty, ∅⟩ :=
    ofR_ok (by rw [← typeOf_unaryApp' h₁]; exact h)
  cases op with
  | not =>
    obtain ⟨bty, rfl, hb⟩ := hop
    refine reach_bool rfl ?_
    rw [fam_succ_bool]; step_bool
    all_goals (nth_or 9; exact hr ▸ unary_bool (fam n) (bt := .anyBool) (r.bool hb))
  | neg =>
    obtain ⟨hb, rfl⟩ := hop
    refine reach_val (by simp [TypedExpr.typeOf, valueTypes])
      (inhabited_of_ne (by simp [TypedExpr.typeOf])) ?_
    have m := r.value (by rw [J.ty, hb]; simp [valueTypes]); simp only [J.ty] at m; rw [hb] at m
    have hm := hr ▸ unary_value (fam n) (op := .neg) (by simp) m
    simp only [TypedExpr.typeOf]; rw [fam_succ_atTy]; step_at
    all_goals branch hm
  | isEmpty =>
    obtain ⟨rfl, ty₀, hb⟩ := hop
    refine reach_bool rfl ?_
    have hv := r.tyU; simp only [J.ty] at hv; rw [hb] at hv
    rcases hv with ⟨_, hv⟩ | ⟨hv, _⟩
    · cases hv
    have m := r.value (by rw [J.ty, hb]; exact hv); simp only [J.ty] at m; rw [hb] at m
    rw [fam_succ_bool]; step_bool
    all_goals (nth_or 11; exact ⟨ty₀, set_value hv, hr ▸ unary_value (fam n) (by simp) m⟩)
  | like p =>
    obtain ⟨rfl, hb⟩ := hop
    refine reach_bool rfl ?_
    have m := r.value (by rw [J.ty, hb]; simp [valueTypes]); simp only [J.ty] at m; rw [hb] at m
    rw [fam_succ_bool]; step_bool
    all_goals (nth_or 12; exact ⟨p, fam_fuel ▸ genPattern_complete n p (hp p rfl),
      hr ▸ unary_value (fam n) (by simp) m⟩)
  | is ety =>
    obtain ⟨ety₁, rfl, hb⟩ := hop
    refine reach_bool rfl ?_
    have hv := r.tyU; simp only [J.ty] at hv; rw [hb] at hv
    rcases hv with ⟨_, hv⟩ | ⟨hv, _⟩
    · cases hv
    have m := r.value (by rw [J.ty, hb]; exact hv); simp only [J.ty] at m; rw [hb] at m
    rw [fam_succ_bool]; step_bool
    all_goals (nth_or 10; exact ⟨ety, _, entity_mem_tys hv, hr ▸ unary_value (fam n) (by simp) m⟩)

theorem base_value (r : ReachF f c ⟨x, t₁, c₁⟩)
    (hbase : (∃ ety, t₁.typeOf = .entity ety) ∨ (∃ rty, t₁.typeOf = .record rty)) :
    t₁.typeOf ∈ valueTypes := by
  rcases r.tyU with ⟨_, hh⟩ | ⟨hh, _⟩
  · have hh' : t₁.typeOf = .bool _ := hh
    rcases hbase with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [hh'] at h <;> cases h
  · exact hh

theorem reach_has
    (ihx : ∀ {tx out}, typeOf x c env = .ok (tx, out) → ReachF (fam (G := SPMF) n) c ⟨x, tx, out⟩) :
    typeOf (.hasAttr x a) c env = .ok (tx, out) →
    ReachF (fam (G := SPMF) (n + 1)) c ⟨.hasAttr x a, tx, out⟩ := by
  intro h
  obtain ⟨-, t₁, c₁, h₁, -, hbase⟩ := Cedar.Thm.type_of_hasAttr_inversion h
  have r := ihx h₁
  have h' := h; rw [typeOf_hasAttr h₁] at h'
  obtain ⟨b, hb⟩ := typeOfHasAttr_bool h'
  have hm := ofR_ok (e := .hasAttr x a) h' ▸
    ruleHas_complete (fam n) (x := ⟨x, t₁, c₁⟩) (base_of_U r.tyU hbase) (r.value (base_value r hbase))
  refine reach_bool hb ?_
  rw [fam_succ_bool]; step_bool
  all_goals (nth_or 4; exact hm)

theorem reach_getReq
    (hreq : ∀ tx cx, typeOf x c env = .ok (tx, cx) → ∃ t, attrTy tx.typeOf a = some (.required t))
    (hok : TyOK c (.getAttr x a))
    (ihx : ∀ {tx out}, typeOf x c env = .ok (tx, out) → ReachF (fam (G := SPMF) n) c ⟨x, tx, out⟩) :
    typeOf (.getAttr x a) c env = .ok (tx, out) →
    ReachF (fam (G := SPMF) (n + 1)) c ⟨.getAttr x a, tx, out⟩ := by
  intro h
  obtain ⟨rfl, t₁, c₁, h₁, -, hbase⟩ := Cedar.Thm.type_of_getAttr_inversion h
  have r := ihx h₁
  have h' := h; rw [typeOf_getAttr h₁] at h'
  obtain ⟨q, hq, hty, -⟩ := getAttr_ty h'
  obtain ⟨t, ht⟩ := hreq t₁ c₁ h₁
  rw [ht] at hq; cases hq
  have hv₁ := base_value r hbase
  have hmem := mem_requiredReads (base_of_U r.tyU hbase) ht ⟨_, attrsOf_of ht⟩
  have hre := ofR_ok (e := .getAttr x a) h' ▸
    ruleRead_req (fam n) (x := ⟨x, t₁, c₁⟩) hmem (r.value hv₁)
  simp only [Qualified.getType] at hty
  rcases attr_cases hv₁ ht with hv | hb
  · simp only [Qualified.getType] at hv
    have hi : inhabited c t = true := by
      rcases hok _ _ h with ⟨b, hb⟩ | ⟨_, hi⟩
      · rw [hty] at hb; subst hb; exact absurd hv bool_not_value
      · rw [hty] at hi; exact hi
    refine reach_val (hty ▸ hv) (hty ▸ hi) ?_
    rw [hty, fam_succ_atTy]; unfold stepAt
    refine mem_pick (w := 3) (g := fun _ => ruleRead (fam n) c t) ?_ (by decide) hre
    simp [readable_of_req hmem]
  · simp only [Qualified.getType] at hb; subst hb
    refine reach_bool hty ?_
    rw [fam_succ_bool]; unfold stepBool
    refine mem_pick (w := 1) (g := fun _ => ruleRead (fam n) c (.bool .anyBool)) ?_ (by decide) hre
    simp [readable_of_req hmem]

theorem reach_getCap (hp : IsPath x) (hc : (x, Key.attr a) ∈ c) (hok : TyOK c (.getAttr x a)) :
    typeOf (.getAttr x a) c env = .ok (tx, out) →
    ReachF (fam (G := SPMF) (n + 1)) c ⟨.getAttr x a, tx, out⟩ := by
  intro h
  obtain ⟨rfl, t₁, c₁, h₁, -, hbase⟩ := Cedar.Thm.type_of_getAttr_inversion h
  have h' := h; rw [typeOf_getAttr h₁] at h'
  obtain ⟨q, hq, hty, -⟩ := getAttr_ty h'
  have hv₁ := path_value hp h₁ hbase
  have hmem := mem_capReads' hc (pathTx_complete hp h₁) hq
  have hre := ofR_ok (e := .getAttr x a) h' ▸ ruleRead_cap (fam n) hmem
  rcases attr_cases hv₁ hq with hv | hb
  · have hi : inhabited c q.getType = true := by
      rcases hok _ _ h with ⟨b, hb⟩ | ⟨_, hi⟩
      · rw [hty] at hb; rw [hb] at hv; exact absurd hv bool_not_value
      · rw [hty] at hi; exact hi
    refine reach_val (hty ▸ hv) (hty ▸ hi) ?_
    rw [hty, fam_succ_atTy]; unfold stepAt
    refine mem_pick (w := 3) (g := fun _ => ruleRead (fam n) c q.getType) ?_ (by decide) hre
    simp [readable_of_cap hmem]
  · rw [hb] at hmem hre
    refine reach_bool (hty.trans hb) ?_
    rw [fam_succ_bool]; unfold stepBool
    refine mem_pick (w := 1) (g := fun _ => ruleRead (fam n) c (.bool .anyBool)) ?_ (by decide) hre
    simp [readable_of_cap hmem]

theorem reach_getTag (hx : IsPath x) (ht : IsPath t) :
    typeOf (.binaryApp .getTag x t) c env = .ok (r, out) →
    ReachF (fam (G := SPMF) (n + 1)) c ⟨.binaryApp .getTag x t, r, out⟩ := by
  intro h
  obtain ⟨tx, cx, tt, ct, h₁, h₂, -⟩ := Cedar.Thm.type_of_binaryApp_inversion h
  have h' := h; rw [typeOf_binaryApp h₁ h₂] at h'
  obtain ⟨ety, he, hs, htags, hc, hr⟩ := getTag_inv h'
  have hmem := mem_tagReads' hc (pathTx_complete hx h₁) (pathTx_complete ht h₂) he hs htags
  have hre := ofR_ok (e := .binaryApp .getTag x t) h'
  refine reach_val (by rw [hr]; simp [valueTypes]) (by rw [hr]; exact inhabited_of_ne (by simp)) ?_
  have hne : (tagReads c).isEmpty = false := by
    cases hl : tagReads c with
    | nil => rw [hl] at hmem; cases hmem
    | cons => rfl
  have hm : ofR (.binaryApp .getTag x t) (typeOfBinaryApp .getTag tx tt x t c env) ∈
      (ruleTagRead (G := SPMF) c).support := by
    rw [SPMF.mem_support_iff_may, ruleTagRead]
    split
    · rename_i heq; rw [heq] at hmem; cases hmem
    · rename_i heq; walk; exact ⟨(x, tx, t, tt), heq ▸ hmem, rfl⟩
  rw [hre] at hm
  rw [hr, fam_succ_atTy]; unfold stepAt construct
  exact mem_pick (w := 2) (g := fun _ => ruleTagRead c) (by simp [hne]) (by decide) hm

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
  | unaryApp hp _ ihx => exact reach_unary hp ihx
  | binaryApp hop _ _ iha ihb => exact reach_binary hop iha ihb
  | getTag hx ht => exact reach_getTag hx ht
  | hasAttr _ ihx => exact reach_has ihx
  | hasAttr_rec hl hnd _ ih => exact reach_hasRec hl hnd ih
  | getAttr _ hreq hok ihx => exact reach_getReq hreq hok ihx
  | getAttr_cap hp hc hok => exact reach_getCap hp hc hok
  | getAttr_rec hl hnd _ hok ih => exact reach_getRec hl hnd ih hok
  | extHasAttr hne hl _ ihx => exact reach_extHas hne hl ihx
  | set hne hl _ hok ih => exact reach_set hne hl ih hok
  | call _ ih => exact reach_call ih

/-- A boolean fragment expression at fuel `n` under no capabilities, with the judgment `typeOf`
gives it. -/
def InScope (n : Nat) : Option J → Prop
  | none => False
  | some j => Scope [] j.e n ∧ typeOf j.e [] env = .ok (j.tx, j.out) ∧ ∃ b, j.ty = .bool b

/-- **Completeness of `genS`.** At every fuel `n`, every boolean expression of the fragment at fuel
`n` that the real typechecker accepts under no capabilities is generated, with exactly the judgment
`typeOf` gives it. -/
theorem genS_complete (n : Nat) : IsCompleteFor (genS (G := SPMF) n) (InScope n) := by
  rintro (_ | j) h
  · exact h.elim
  · obtain ⟨hs, ht, b, hb⟩ := h
    exact (reach hs ht).bool hb

end CedarGen
