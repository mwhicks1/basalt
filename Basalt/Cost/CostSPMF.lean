import Basalt.SPMF
import Basalt.RandomChoice

open RandomChoice

abbrev CostSPMF (α : Type) : Type := SPMF (α × Nat)

namespace CostSPMF

instance instInhabited : Inhabited (CostSPMF α) where
  default := @Bot.bot (SPMF (α × Nat)) _

noncomputable instance instMonad : Monad CostSPMF where
  pure a := (pure (a, 0) : SPMF _)
  bind m f :=
    Bind.bind (m := SPMF) m fun pair =>
      Bind.bind (f pair.1) fun pair2 =>
        pure (pair2.1, pair.2 + pair2.2)

section CCPO

open Lean.Order

instance instPartialOrder : Lean.Order.PartialOrder (CostSPMF α) where
  rel p q := @PartialOrder.rel (SPMF (α × Nat)) _ p q
  rel_refl := @PartialOrder.rel_refl (SPMF (α × Nat)) _
  rel_trans := @PartialOrder.rel_trans (SPMF (α × Nat)) _
  rel_antisymm := @PartialOrder.rel_antisymm (SPMF (α × Nat)) _

instance instCCPO : CCPO (CostSPMF α) where
  has_csup := by
    intros c hc
    exact @CCPO.has_csup (SPMF (α × Nat)) _ c hc

instance instMonoBind : MonoBind CostSPMF where
  bind_mono_left {α β} {m₁ m₂ : CostSPMF α} {f : α → CostSPMF β} (h : m₁ ⊑ m₂) := by
    intro pair
    simp only [Bind.bind, bind]
    unfold SPMF.bind
    apply ENNReal.tsum_le_tsum
    intro ⟨a, n₁⟩
    simp only [Lean.Order.PartialOrder.rel] at h
    gcongr
    exact h (a, n₁)
  bind_mono_right {α β} {m : CostSPMF α} {f₁ f₂ : α → CostSPMF β} (h : ∀ a, f₁ a ⊑ f₂ a) := by
    intro pair
    simp only [Bind.bind, bind]
    unfold SPMF.bind
    simp only [Lean.Order.PartialOrder.rel] at h ⊢
    apply ENNReal.tsum_le_tsum
    intro ⟨a, n₁⟩
    gcongr ?_ * ?_
    apply ENNReal.tsum_le_tsum
    intro i
    gcongr ?_ * ?_
    apply h

end CCPO

noncomputable instance instRandomChoice : RandomChoice CostSPMF where
  choose lo hi h :=
    SPMF.bind (@RandomChoice.choose SPMF _ lo hi h) fun n => SPMF.pure (n, 1)

noncomputable def charge (n : Nat) : CostSPMF Unit := SPMF.pure ((), n)

instance : LE (CostSPMF α) where
  le p q :=
    ∃ (coupling : SPMF ((α × ℕ) × (α × ℕ))),
      (·.1) <$> coupling = p ∧
      (·.2) <$> coupling = q ∧
      ∀ x ∈ coupling.support, x.1.1 = x.2.1 ∧ x.1.2 ≤ x.2.2

private lemma map_fst_tsum {α β : Type} (c : SPMF (α × β)) (p : SPMF α)
    (h : (·.1) <$> c = p) (a : α) : ∑' b : β, c (a, b) = p a := by
  have key := congr_fun (congrArg Subtype.val h) a
  simp only [Functor.map, SPMF.bind, DFunLike.coe, Function.comp_apply, SPMF.pure] at key
  rw [ENNReal.tsum_prod', tsum_eq_single a (by intro a₁ ha₁; simp [if_neg (Ne.symm ha₁)])] at key
  simpa using key

private lemma map_snd_tsum {α β : Type} (c : SPMF (α × β)) (p : SPMF β)
    (h : (·.2) <$> c = p) (b : β) : ∑' a : α, c (a, b) = p b := by
  have key := congr_fun (congrArg Subtype.val h) b
  simp only [Functor.map, SPMF.bind, DFunLike.coe, Function.comp_apply, SPMF.pure] at key
  rw [ENNReal.tsum_prod'] at key
  conv_lhs at key =>
    arg 1; ext a₁
    rw [tsum_eq_single b (by intro a₂ ha₂; simp [if_neg (Ne.symm ha₂)])]
  simpa using key

instance : Preorder (CostSPMF α) where
  le_refl x := by
    exists (x >>= fun a => pure (a, a))
    refine ⟨?_, ?_, ?_⟩ <;> simp
    grind
  le_trans x y z hxy hyz := by
    have ⟨couplingXY, hxy₁, hxy₂, hxy₃⟩ := hxy
    have ⟨couplingYZ, hyz₁, hyz₂, hyz₃⟩ := hyz
    have hXY_left := map_fst_tsum couplingXY x hxy₁
    have hXY_marg := map_snd_tsum couplingXY y hxy₂
    have hYZ_marg := map_fst_tsum couplingYZ y hyz₁
    have hYZ_right := map_snd_tsum couplingYZ z hyz₂
    have hy_ne_top b : y b ≠ ⊤ :=
      ne_top_of_lt ((ENNReal.le_tsum b).trans y.property |>.trans_lt ENNReal.one_lt_top)
    exists SPMF.composeCouplings y couplingXY couplingYZ hXY_marg hYZ_marg
    refine ⟨?left_marginal, ?right_marginal, ?cost_refinement⟩
    case left_marginal =>
      apply DFunLike.ext; intro a
      simp only [Functor.map, SPMF.bind, DFunLike.coe, Function.comp_apply, SPMF.pure,
                 SPMF.composeCouplings]
      rw [ENNReal.tsum_prod', tsum_eq_single a (by intro a₁ ha₁; simp [if_neg (Ne.symm ha₁)])]
      simp only [ite_true, mul_one]
      rw [ENNReal.tsum_comm]
      have key : ∀ b, ∑' c, couplingXY (a, b) * couplingYZ (b, c) / y b = couplingXY (a, b) := by
        intro b
        simp_rw [ENNReal.div_eq_inv_mul, ← mul_assoc, ENNReal.tsum_mul_left, hYZ_marg b]
        rcases eq_or_ne (y b) 0 with h | h
        . simp [ENNReal.tsum_eq_zero.mp ((hXY_marg b).trans h) a, h]
        . rw [mul_right_comm, ENNReal.inv_mul_cancel h (hy_ne_top b), one_mul]
      show ∑' b, ∑' a_1, couplingXY (a, b) * couplingYZ (b, a_1) / y b = x a
      simp_rw [key]
      exact hXY_left a
    case right_marginal =>
      apply DFunLike.ext; intro c
      simp only [Functor.map, SPMF.bind, DFunLike.coe, Function.comp_apply, SPMF.pure,
                 SPMF.composeCouplings]
      rw [ENNReal.tsum_prod']
      conv_lhs =>
        arg 1; ext a
        rw [tsum_eq_single c (by intro c' hc'; simp [if_neg (Ne.symm hc')])]
      simp only [ite_true, mul_one]
      rw [ENNReal.tsum_comm]
      have key : ∀ b, ∑' a, couplingXY (a, b) * couplingYZ (b, c) / y b = couplingYZ (b, c) := by
        intro b
        simp_rw [mul_div_assoc, ENNReal.tsum_mul_right, hXY_marg b]
        rcases eq_or_ne (y b) 0 with h | h
        . simp [ENNReal.tsum_eq_zero.mp ((hYZ_marg b).trans h) c, h]
        . exact ENNReal.mul_div_cancel h (hy_ne_top b)
      show ∑' b, ∑' a, couplingXY (a, b) * couplingYZ (b, c) / y b = z c
      simp_rw [key]
      exact hYZ_right c
    case cost_refinement =>
      intro ⟨a, c⟩ hmem
      rw [SPMF.mem_support_iff] at hmem
      simp only [SPMF.composeCouplings, DFunLike.coe] at hmem
      have ⟨b, hb⟩ : ∃ b, couplingXY (a, b) * couplingYZ (b, c) / y b ≠ 0 := by
        by_contra hall
        push_neg at hall
        exact hmem (ENNReal.tsum_eq_zero.mpr hall)
      have hprod : couplingXY (a, b) * couplingYZ (b, c) ≠ 0 := by
        intro h; simp [h] at hb
      have hab_ne : couplingXY (a, b) ≠ 0 := left_ne_zero_of_mul hprod
      have hbc_ne : couplingYZ (b, c) ≠ 0 := right_ne_zero_of_mul hprod
      have hab := hxy₃ (a, b) ((SPMF.mem_support_iff _ _).mpr hab_ne)
      have hbc := hyz₃ (b, c) ((SPMF.mem_support_iff _ _).mpr hbc_ne)
      exact ⟨hab.1.trans hbc.1, hab.2.trans hbc.2⟩

theorem bind_mono_left
    {x y : CostSPMF α}
    {f : α → CostSPMF β}
    (hxy : x ≤ y) :
    x >>= f ≤ y >>= f := by
  have ⟨c, hcx, hcy, hc_cost⟩ := hxy
  exists do
    let ((a, ca), (_, ca')) ← c
    let (b, cb) ← f a
    return ((b, cb + ca), (b, cb + ca'))
  refine ⟨?left_marginal, ?right_marginal, ?cost_refinement⟩
  case left_marginal =>
    simp only [Functor.map] at *
    rw [← hcx]
    simp +arith [bind, pure, SPMF.bind_assoc, SPMF.pure_bind]
  case right_marginal =>
    simp only [Functor.map] at *
    rw [← hcy]
    simp only [bind, pure, SPMF.bind_assoc, SPMF.pure_bind, Function.comp_apply]
    apply SPMF.bind_congr_support
    intro a ha
    simp +arith [(hc_cost a ha).1]
  case cost_refinement =>
    grind only [SPMF.support_bind, usr Set.mem_setOf_eq, SPMF.support_pure, = Set.mem_singleton_iff]

theorem bind_mono_right
    {f g : α → CostSPMF β}
    (hfg : ∀ a, f a ≤ g a) :
    x >>= f ≤ x >>= g := by
  exists do
    let (a, ca) ← x
    let ((b, cb), (_, cb')) ← Classical.choose (hfg a)
    return ((b, ca + cb), (b, ca + cb'))
  refine ⟨?left_marginal, ?right_marginal, ?cost_refinement⟩
  case left_marginal =>
    simp only [Functor.map, bind, Prod.forall, pure, SPMF.bind_assoc, SPMF.pure_bind, Function.comp_apply]
    grind only [SPMF.bind_congr_support, Classical.choose_spec, usr Exists.choose_spec, SPMF.bind_assoc, SPMF.pure_bind]
  case right_marginal =>
    simp only [Functor.map, bind, Prod.forall, pure, SPMF.bind_assoc, SPMF.pure_bind, Function.comp_apply]
    grind only [SPMF.bind_congr_support, Classical.choose_spec, usr Exists.choose_spec, SPMF.bind_assoc, SPMF.pure_bind]
  case cost_refinement =>
    intro p hp
    simp only [Prod.forall, bind_pure_comp, SPMF.support_bind, SPMF.support_map, Prod.exists, Set.mem_setOf_eq] at hp
    grind

noncomputable def noCharge (x : CostSPMF α) : CostSPMF α := Bind.bind (m := SPMF) (x : SPMF (α × Nat)) (fun (a, _) => pure (a, 0))

@[simp]
theorem noCharge_pure : noCharge (pure a) = pure a := by
  simp [bind, pure, noCharge, SPMF.pure_bind]

@[simp]
theorem noCharge_bind : noCharge (x >>= f) = noCharge x >>= noCharge ∘ f := by
  simp [bind, pure, noCharge, SPMF.bind_assoc, SPMF.pure_bind]

@[simp]
theorem noCharge_charge : noCharge (charge n) = pure () := by
  simp [noCharge, charge, pure, bind, SPMF.pure_bind]

@[simp]
theorem noCharge_choose : noCharge (choose lo hi h) = Bind.bind (m := SPMF) (choose lo hi h : CostSPMF Nat) fun (a, _) => pure (a, 0) := by
  simp [noCharge]

section support

@[simp] theorem mem_support_pure_iff {a b : α} {n : Nat} :
    (b, n) ∈ (pure a : CostSPMF α).support ↔ b = a ∧ n = 0 := by
  have : (pure a : CostSPMF α) = (SPMF.pure (a, 0) : SPMF _) := rfl
  simp [this, SPMF.mem_support_pure_iff, Prod.mk.injEq]

@[simp] theorem mem_support_bind_iff
    {m : CostSPMF α} {f : α → CostSPMF β} {b : β} {n : Nat} :
    (b, n) ∈ (m >>= f).support ↔
    ∃ a n1 n2, (a, n1) ∈ m.support ∧ (b, n2) ∈ (f a).support ∧ n = n1 + n2 := by
  have : (m >>= f : CostSPMF β) =
      SPMF.bind m fun pair =>
        SPMF.bind (f pair.1) fun pair2 =>
          (SPMF.pure (pair2.1, pair.2 + pair2.2) : SPMF _) := rfl
  rw [this]
  simp only [SPMF.mem_support_bind_iff, SPMF.mem_support_pure_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨a, n1⟩, hmem1, ⟨b', n2⟩, hmem2, rfl, h_n⟩
    exact ⟨a, n1, n2, hmem1, hmem2, h_n⟩
  · rintro ⟨a, n1, n2, hmem1, hmem2, rfl⟩
    exact ⟨⟨a, n1⟩, hmem1, ⟨b, n2⟩, hmem2, rfl, rfl⟩

@[simp] theorem mem_support_choose_iff
    {lo hi : Nat} {h : lo ≤ hi} {n c : Nat} :
    (n, c) ∈ (choose lo hi h : CostSPMF Nat).support ↔ lo ≤ n ∧ n ≤ hi ∧ c = 1 := by
  have : (choose lo hi h : CostSPMF Nat) =
      SPMF.bind (choose lo hi h : SPMF Nat) fun k => (SPMF.pure (k, 1) : SPMF _) := rfl
  rw [this]
  simp only [SPMF.mem_support_bind_iff, SPMF.support_choose, Set.mem_setOf_eq,
             SPMF.mem_support_pure_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨k, ⟨h1, h2⟩, rfl, rfl⟩
    exact ⟨h1, h2, rfl⟩
  · rintro ⟨h1, h2, rfl⟩
    exact ⟨n, ⟨h1, h2⟩, rfl, rfl⟩

end support

end CostSPMF

open CostSPMF

def IsBounded (x : CostSPMF α) (f : α → Nat) : Prop :=
  x ≤ (noCharge x >>= fun a => do charge (f a); pure a)

theorem IsBounded_iff {x : CostSPMF α} {f : α → Nat} :
    IsBounded x f ↔
    ∀ p ∈ SPMF.support x, p.2 ≤ f p.1 := by
  constructor
  . simp only [bind, noCharge, charge, pure, SPMF.pure_bind, add_zero, SPMF.bind_assoc, zero_add, IsBounded, Prod.forall]
    intro h a n hsupport
    have ⟨c, h₁, h₂, h₃⟩ := h
    have : ((a, n), (a, f a)) ∈ c.support := by
      clear h
      simp only [Functor.map, Function.comp_def] at *
      rw [← h₁] at h₂
      simp only [SPMF.bind_assoc, SPMF.pure_bind] at *
      rw [← h₁] at hsupport
      simp only [SPMF.mem_support_bind_iff, SPMF.mem_support_pure_iff] at hsupport
      have ⟨(a', n'), h, heq⟩ := hsupport
      cases heq
      have hn' : n' = (a, f a) := by
        have hmem : n' ∈ (c.bind fun x => SPMF.pure x.2).support := by
          grind only [SPMF.mem_support_bind_iff, SPMF.mem_support_pure_iff]
        grind only [SPMF.mem_support_bind_iff, Prod.snd_eq_iff, SPMF.mem_support_pure_iff]
      subst hn'
      exact h
    grind
  . intro h
    simp only [IsBounded, bind, noCharge, pure, charge, SPMF.pure_bind, add_zero, SPMF.bind_assoc, zero_add]
    exists do
      let (a, n) ← x
      pure ((a, n), (a, f a))
    refine ⟨?left_marginal, ?right_marginal, ?cost_refinement⟩
    case left_marginal =>
      simp [Functor.map, SPMF.bind_assoc, Function.comp_def, SPMF.pure_bind, SPMF.bind_pure]
    case right_marginal =>
      simp [Functor.map, SPMF.bind_assoc, Function.comp_def, SPMF.pure_bind]
    case cost_refinement =>
      simp_all

theorem IsBounded_pure : IsBounded (pure a) (fun _ => 0) := by
  simp +arith [IsBounded, noCharge, charge, pure, bind, SPMF.pure_bind]

theorem IsBounded_choose : IsBounded (choose lo hi h) (fun _ => 1) := by
  simp +arith [IsBounded, noCharge, charge, pure, bind, SPMF.pure_bind, choose, SPMF.bind_assoc]

theorem IsBounded_bind
    {cx : α → Nat}
    {cf : α → β → Nat}
    {c : β → Nat}
    (hx : IsBounded x cx)
    (hf : ∀ a, IsBounded (f a) (cf a))
    (hg : ∀ p ∈ x.support, ∀ q ∈ (f p.1).support, cx p.1 + cf p.1 q.1 ≤ c q.1) :
    IsBounded (x >>= f) c := by
  simp_all only [IsBounded_iff]
  intro (b, nb) hb
  simp only [bind, pure, SPMF.mem_support_bind_iff, SPMF.mem_support_pure_iff] at hb
  replace ⟨(a, na), ha, ⟨(b, nb), hb, h⟩⟩ := hb
  cases h
  simp_all
  grind

theorem IsBounded_mono
    (hc₁ : IsBounded x c₁)
    (h : ∀ a, c₁ a ≤ c₂ a) :
    IsBounded x c₂ := by
  simp_all only [IsBounded_iff]
  grind

open Lean.Order in
theorem admissible_IsBounded (f : α → Nat) :
    admissible (fun (x : CostSPMF α) => IsBounded x f) := by
  intro c hc ih
  simp only [IsBounded_iff] at *
  intro p hp
  rw [SPMF.mem_support_csup hc] at hp
  obtain ⟨x, hxc, hxp⟩ := hp
  exact ih x hxc p hxp

theorem IsBounded_pick
    {fx fy : Unit → CostSPMF α}
    {cx cy : α → Nat}
    (hx : IsBounded (fx ()) cx)
    (hy : IsBounded (fy ()) cy) :
    IsBounded (pick fx fy) (fun a => 1 + max (cx a) (cy a)) := by
  unfold pick
  apply IsBounded_bind (cx := fun _ => 1) (cf := fun k a => if k == 0 then cx a else cy a)
      IsBounded_choose
  · intro k
    split_ifs
    · exact hx
    · exact hy
  · intro ⟨k, _⟩ _ ⟨a, _⟩ _
    simp only
    split_ifs <;> omega
