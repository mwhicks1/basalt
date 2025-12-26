import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.Measure.Dirac
import Basalt.RandomChoice

open Lean.Order RandomChoice NNReal ENNReal MeasureTheory

/-!
# Sub-Probability Mass Functions

This file defines a type of sub-probability mass functions, similar to `PMF` from Mathlib.
-/

/-- A sub-probability mass function is similar to a PMF, but the total mass may be less than 1. -/
def SPMF.{u} (α : Type u) : Type u := {μ : α → ℝ≥0∞ // (∑' a, μ a) ≤ 1}

namespace SPMF

instance instBot : Bot (SPMF α) where
  bot := ⟨fun _ => 0, by simp⟩

instance instFunLike : FunLike (SPMF α) α ℝ≥0∞ where
  coe p a := p.1 a
  coe_injective' _ _ h := Subtype.ext h

@[ext]
protected theorem ext {p q : SPMF α} (h : ∀ x, p x = q x) : p = q :=
  DFunLike.ext p q h

@[simp]
theorem tsum_coe (p : SPMF α) : ∑' a, p a ≤ 1 := p.2

theorem tsum_coe_ne_top (p : SPMF α) : ∑' a, p a ≠ ∞ := by
  have := ENNReal.one_lt_top
  have := p.tsum_coe
  grind only

theorem tsum_coe_indicator_ne_top (p : SPMF α) (s : Set α) : ∑' a, s.indicator p a ≠ ∞ :=
  ne_of_lt (lt_of_le_of_lt
    (ENNReal.tsum_le_tsum (fun _ => Set.indicator_apply_le fun _ => le_rfl))
    (lt_of_le_of_ne le_top p.tsum_coe_ne_top))

theorem coe_le_one (p : SPMF α) (a : α) : p a ≤ 1 := by
  have h₁ := p.tsum_coe
  have h₂ := ENNReal.le_tsum (f := p) a
  grind only

theorem apply_ne_top (p : SPMF α) (a : α) : p a ≠ ∞ :=
  ne_of_lt (lt_of_le_of_lt (p.coe_le_one a) ENNReal.one_lt_top)

theorem apply_lt_top (p : SPMF α) (a : α) : p a < ∞ :=
  lt_of_le_of_ne le_top (p.apply_ne_top a)

instance : Lean.Order.PartialOrder (SPMF α) where
  rel p q := ∀ a, p a ≤ q a
  rel_refl := by grind
  rel_trans := by grind
  rel_antisymm h₁ h₂ := by ext; grind

/-- The supremum of a chain is the SPMF where each point is maximally defined. -/
noncomputable def csupFun {α : Type u} (c : Set (SPMF α)) : α → ℝ≥0∞ :=
  fun a => ⨆ f ∈ c, f a

theorem csupFun_sum_le_one
  {c : Set (SPMF α)}
  (h_chain : chain c) :
  (∑' a, csupFun c a) ≤ 1 := by
  by_cases hc : c = ∅
  case pos =>
    simp [csupFun, hc]
  case neg =>
    have h_directed : DirectedOn (· ⊑ ·) c := fun x hx y hy => by
      rcases h_chain x y hx hy with h | h
      · exact ⟨y, hy, h, PartialOrder.rel_refl⟩
      · exact ⟨x, hx, PartialOrder.rel_refl, h⟩
    have h_directed_le : DirectedOn (fun f g => ∀ a, f a ≤ g a) c := fun x hx y hy => by
      rcases h_directed x hx y hy with ⟨z, hz, hxz, hyz⟩
      exact ⟨z, hz, hxz, hyz⟩
    calc ∑' a, csupFun c a
      _ = ⨆ s : Finset α, ∑ a ∈ s, csupFun c a := ENNReal.tsum_eq_iSup_sum
      _ = ⨆ s : Finset α, ∑ a ∈ s, ⨆ f ∈ c, f a := rfl
      _ ≤ ⨆ s : Finset α, ⨆ f ∈ c, ∑ a ∈ s, f a := by
          apply iSup_mono
          intro s
          simp_rw [iSup_subtype']
          rw [ENNReal.finsetSum_iSup]
          intro ⟨f, hf⟩ ⟨g, hg⟩
          rcases h_directed_le f hf g hg with ⟨k, hk, hfk, hgk⟩
          exact ⟨⟨k, hk⟩, fun a => ⟨hfk a, hgk a⟩⟩
      _ = ⨆ f ∈ c, ⨆ s : Finset α, ∑ a ∈ s, f a := by
          rw [iSup_comm]
          congr 1
          ext f
          rw [iSup_comm]
      _ = ⨆ f ∈ c, ∑' a, f a := by
          congr 1; ext f; congr 1; ext _
          exact ENNReal.tsum_eq_iSup_sum.symm
      _ ≤ 1 := by simp

noncomputable instance : CCPO (SPMF α) where
  has_csup := by
    intros c hc
    exists ?sup
    case sup => exact ⟨csupFun c, csupFun_sum_le_one hc⟩
    intro x
    constructor
    · intro h_csup_le y hy a
      exact Trans.trans (le_iSup₂_of_le y hy le_rfl) (h_csup_le a)
    · intro h_ub a
      unfold csupFun
      apply iSup₂_le
      intro y hy
      exact h_ub y hy a

section operations

open Classical in
/-- A dirac distribution; all of the mass is on `a`. -/
noncomputable def pure (a : α) : SPMF α :=
  ⟨fun a' => if a' = a then 1 else 0, by simp⟩

/-- The standard Giry monad approach to PMF composition. -/
noncomputable def bind (p : SPMF α) (f : α → SPMF β) : SPMF β := by
  refine ⟨fun b => ∑' a, p a * f a b, ?pf⟩
  have p_prop := p.tsum_coe
  have : ∑' (b : β) (a : α), p a * f a b ≤ ∑' (a : α), p a := by
    simp [ENNReal.tsum_comm, ENNReal.tsum_mul_left, ENNReal.tsum_le_tsum, mul_le_of_le_one_right']
  grind only

noncomputable instance : Monad SPMF where
  pure a := pure a
  bind p f := p.bind f

instance : MonoBind SPMF where
  bind_mono_left {_ _} {p₁ p₂ f} h b := by
    simp only [Bind.bind, bind]
    apply ENNReal.tsum_le_tsum
    intro a
    exact mul_le_mul_left (h a) _
  bind_mono_right {_ _} {p f₁ f₂} h b := by
    simp only [Bind.bind, bind]
    apply ENNReal.tsum_le_tsum
    intro a
    exact mul_le_mul_right (h a b) _

/-- The bottom element is minimally defined; the mass sums to 0. -/
instance : Inhabited (SPMF α) where
  default := Bot.bot

noncomputable instance : RandomChoice SPMF where
  choose lo hi h := by
    let n : ℕ := hi - lo + 1
    refine ⟨fun a => if lo ≤ a ∧ a ≤ hi then 1 / n else 0, ?pf⟩
    have hn : n ≠ 0 := Nat.add_one_ne_zero _
    have hsupp : ∀ a, a ∉ Finset.Icc lo hi → (if lo ≤ a ∧ a ≤ hi then (1 : ℝ≥0∞) / n else 0) = 0 := by
      intro a ha
      simp only [Finset.mem_Icc, not_and, not_le] at ha
      by_cases hlo : lo ≤ a
      · have := ha hlo; simp [hlo, Nat.not_le.mpr this]
      · simp [hlo]
    calc ∑' a, if lo ≤ a ∧ a ≤ hi then (1 : ℝ≥0∞) / n else 0
      _ = ∑ a ∈ Finset.Icc lo hi, if lo ≤ a ∧ a ≤ hi then (1 : ℝ≥0∞) / n else 0 :=
          tsum_eq_sum hsupp
      _ = ∑ _a ∈ Finset.Icc lo hi, (1 : ℝ≥0∞) / n :=
          Finset.sum_congr rfl (fun x hx => by simp [Finset.mem_Icc.mp hx])
      _ = (Finset.Icc lo hi).card • (1 / n : ℝ≥0∞) :=
          Finset.sum_const _
      _ = n * (1 / n) := by
          simp only [Nat.card_Icc, nsmul_eq_mul]
          congr 1
          have heq : hi + 1 - lo = hi - lo + 1 := by omega
          exact congrArg Nat.cast heq
      _ = 1 := ENNReal.mul_div_cancel (Nat.cast_ne_zero.mpr hn) (ENNReal.natCast_ne_top n)
      _ ≤ 1 := le_rfl

end operations

section operation_uses

-- TODO: Should we have these "_apply" lemmas for every operation? Or is that redundant with `mass`
-- below? We should figure this out based on usages in the `Examples` directory.

theorem pick_apply {x y : SPMF α} (a : α) :
    (pick (fun () => x) (fun () => y)) a =
    (1/2 : ℝ≥0∞) * x a + (1/2 : ℝ≥0∞) * y a := by
  simp only [pick, Bind.bind, bind]
  show ∑' n, (choose 0 1 pick._proof_1 : SPMF Nat) n *
       (if (n == 0) = true then x else y : SPMF α) a = _
  have h_supp : ∀ n ∉ Finset.Icc 0 1,
      (choose 0 1 pick._proof_1 : SPMF Nat) n *
      (if (n == 0) = true then x else y : SPMF α) a = 0 := by
    intro n hn
    simp only [Finset.mem_Icc, not_and, not_le] at hn
    have hn' : ¬(0 ≤ n ∧ n ≤ 1) := by push_neg; intro _; omega
    have hzero : (choose 0 1 pick._proof_1 : SPMF Nat) n = 0 := by
      simp only [RandomChoice.choose, instFunLike]
      simp only [hn', ite_false]
    simp only [hzero, zero_mul]
  rw [tsum_eq_sum h_supp]
  have hIcc : Finset.Icc 0 1 = ({0, 1} : Finset Nat) := by decide
  rw [hIcc, Finset.sum_pair (by simp : (0 : Nat) ≠ 1)]
  have h0 : (choose 0 1 pick._proof_1 : SPMF Nat) 0 = 1 / 2 := by
    simp only [RandomChoice.choose, instFunLike]
    norm_num
  have h1 : (choose 0 1 pick._proof_1 : SPMF Nat) 1 = 1 / 2 := by
    simp only [RandomChoice.choose, instFunLike]
    norm_num
  simp only [h0, h1, beq_self_eq_true, ite_true, one_ne_zero, beq_iff_eq, ite_false]

@[simp]
theorem bot_apply (a : α) : Bot.bot (α := SPMF α) a = 0 := rfl

end operation_uses

section equations

theorem pure_bind (a : α) (f : α → SPMF β) : bind (pure a) f = f a := by
  ext b
  simp only [bind, pure, instFunLike]
  rw [tsum_eq_single a]
  · simp
  · intro b' hb; simp [hb]

theorem bind_pure (p : SPMF α) : bind p pure = p := by
  ext b
  simp only [bind, pure, instFunLike]
  rw [tsum_eq_single b]
  · simp
  · intro b' hb
    simp [Ne.symm hb]

theorem bind_assoc (m : SPMF α) (f : α → SPMF β) (g : β → SPMF γ) :
    bind (bind m f) g = bind m (fun x => bind (f x) g) := by
  ext c
  simp only [bind, instFunLike]
  trans ∑' (b : β) (a : α), m a * f a b * g b c
  · congr; ext b
    rw [ENNReal.tsum_mul_right]
    rfl
  rw [ENNReal.tsum_comm]
  congr; ext a
  rw [← ENNReal.tsum_mul_left]
  congr; ext b
  rw [mul_assoc]
  rfl

instance instLawfulMonadSPMF : LawfulMonad SPMF where
  bind_pure_comp := by intros; rfl
  bind_map := by intros; rfl
  pure_bind := pure_bind
  bind_assoc := bind_assoc
  map_const := by intros; rfl
  id_map := bind_pure
  seqLeft_eq := by
    intros
    simp only [SeqLeft.seqLeft, Seq.seq, Functor.map]
    unfold Function.comp Function.const
    rw [bind_assoc]
    simp [pure_bind]
  seqRight_eq := by
    intros
    simp only [SeqRight.seqRight, Seq.seq, Functor.map]
    unfold Function.comp Function.const id
    rw [bind_assoc]
    simp [pure_bind, bind_pure]
  pure_seq := by
    intros
    simp only [Seq.seq, Functor.map, Pure.pure]
    unfold Function.comp
    simp [pure_bind]

theorem bind_pick {α β} (x y : SPMF α) (f : α → SPMF β) :
    (pick (fun () => x) (fun () => y) >>= f) = pick (fun _ => x >>= f) (fun _ => y >>= f) := by
  apply SPMF.ext
  intro b
  simp only [pick_apply, bind, SPMF.bind, Bind.bind]
  simp only [ENNReal.tsum_add, add_mul, ENNReal.tsum_mul_left, mul_assoc]
  rfl

theorem tsum_pick {x y : SPMF α} :
    ∑' a, (pick (fun () => x) (fun () => y)) a = (1/2 : ℝ≥0∞) * (∑' a, x a) + (1/2 : ℝ≥0∞) * (∑' a, y a) := by
  simp_rw [pick_apply]
  rw [ENNReal.tsum_add]
  congr 1 <;> rw [ENNReal.tsum_mul_left]

@[simp]
theorem bot_bind (f : α → SPMF β) : (Bot.bot (α := SPMF α) >>= f) = Bot.bot := by
  ext b
  simp only [Bind.bind, bind, bot_apply, zero_mul, tsum_zero]
  rfl

end equations

section support

def support (p : SPMF α) : Set α := Function.support p

theorem mem_support_iff (p : SPMF α) (a : α) : a ∈ p.support ↔ p a ≠ 0 := Iff.rfl

@[simp]
theorem support_countable (p : SPMF α) : p.support.Countable :=
  Summable.countable_support_ennreal (tsum_coe_ne_top p)

theorem apply_eq_zero_iff (p : SPMF α) (a : α) : p a = 0 ↔ a ∉ p.support := by
  rw [mem_support_iff, Classical.not_not]

theorem apply_pos_iff (p : SPMF α) (a : α) : 0 < p a ↔ a ∈ p.support :=
  pos_iff_ne_zero.trans (p.mem_support_iff a).symm

@[simp]
theorem support_bind
    {x : SPMF α}
    {f : α → SPMF β} :
    (x >>= f).support = {b | ∃ a, a ∈ x.support ∧ b ∈ (f a).support} := by
  ext b
  simp only [support, Function.mem_support, Set.mem_setOf_eq]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have hzero : ∀ a, x a * f a b = 0 := fun a => by
      by_cases ha : x a = 0
      · simp [ha]
      · simp [hc a ha]
    apply h
    change (∑' a, x a * f a b) = 0
    simp only [hzero, tsum_zero]
  · intro ⟨a, ha, hb⟩
    apply ne_of_gt
    change 0 < (∑' a', x a' * f a' b)
    calc 0 < x a * f a b := ENNReal.mul_pos ha hb
      _ ≤ ∑' a, x a * f a b := ENNReal.le_tsum a

@[simp]
theorem support_pure :
    (Pure.pure a : SPMF _).support = {a} := by
  classical
  ext x
  simp only [support, Function.mem_support, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hne
    apply h
    show (if x = a then (1 : ℝ≥0∞) else 0) = 0
    simp [hne]
  · intro h
    show (if x = a then (1 : ℝ≥0∞) else 0) ≠ 0
    simp [h]

@[simp]
theorem support_map
    {x : SPMF α}
    {f : α → β} :
    (f <$> x).support = {b | ∃ a, a ∈ x.support ∧ b = f a} := by
  rw [← LawfulMonad.bind_pure_comp]
  simp only [support_bind, support_pure]
  grind

@[simp]
theorem support_choose :
    (choose lo hi h : SPMF _).support = {a | lo ≤ a ∧ a ≤ hi} := by
  ext a
  rw [support, Function.mem_support, Set.mem_setOf_eq]
  simp only [RandomChoice.choose, DFunLike.coe]
  constructor
  · intro ha
    by_contra hc
    push_neg at hc
    apply ha
    by_cases hlo : lo ≤ a
    · simp [hlo, Nat.not_le.mpr (hc hlo)]
    · simp [hlo]
  · intro ⟨hlo, hhi⟩
    simp only [hlo, hhi, and_self, ↓reduceIte, ne_eq, one_div]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)

@[simp]
theorem support_pick
    {x y : SPMF α} :
    (pick (fun () => x) (fun () => y)).support = x.support ∪ y.support := by
  simp only [pick, support_bind, support_choose]
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_union]
  constructor
  · intro ⟨n, ⟨_, hn1⟩, ha⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn1 with rfl | rfl
    · left; simpa using ha
    · right; simpa using ha
  · intro h
    cases h with
    | inl hx =>
      refine ⟨0, ⟨Nat.zero_le _, Nat.zero_le _⟩, ?_⟩
      simpa using hx
    | inr hy =>
      refine ⟨1, ⟨Nat.zero_le _, le_refl _⟩, ?_⟩
      simpa using hy

end support

section mass

/-- The total mass of an SPMF. Always ≤ 1 by definition. -/
noncomputable def mass (p : SPMF α) : ℝ≥0∞ := ∑' a, p a

theorem mass_eq_zero_of_support_empty {p : SPMF α} (h : p.support = ∅) : p.mass = 0 := by
  unfold mass
  rw [ENNReal.tsum_eq_zero]
  intro a
  rw [apply_eq_zero_iff]
  exact Set.eq_empty_iff_forall_notMem.mp h a

theorem mass_pick {x y : SPMF α} :
    (pick (fun () => x) (fun () => y)).mass = (1/2 : ℝ≥0∞) * x.mass + (1/2 : ℝ≥0∞) * y.mass := tsum_pick

@[simp]
theorem mass_bot : Bot.bot (α := SPMF α).mass = 0 := by
  simp [mass]

theorem mass_eq_zero_iff {x : SPMF α} : x.mass = 0 ↔ x = Bot.bot := by
  constructor
  · intro h
    ext a
    simp only [bot_apply]
    have : ∑' a, x a = 0 := h
    exact (ENNReal.tsum_eq_zero.mp this) a
  · intro h
    simp [h]

theorem mass_pure (a : α) : (Pure.pure a : SPMF α).mass = 1 := by
  unfold mass
  simp only [Pure.pure, pure, DFunLike.coe]
  rw [tsum_eq_single a]
  · simp
  · intro a' ha'
    simp [ha']

theorem mass_choose (lo hi : Nat) (h : lo ≤ hi) : (choose lo hi h : SPMF Nat).mass = 1 := by
  unfold mass
  apply le_antisymm
  · exact (choose lo hi h : SPMF Nat).tsum_coe
  · let n : ℕ := hi - lo + 1
    have hn : n ≠ 0 := Nat.add_one_ne_zero _
    have hsupp : ∀ a, a ∉ Finset.Icc lo hi →
        ((choose lo hi h : SPMF Nat) a) = 0 := by
      intro a ha
      simp only [RandomChoice.choose, instFunLike]
      simp only [Finset.mem_Icc, not_and, not_le] at ha
      by_cases hlo : lo ≤ a
      · have := ha hlo; simp [hlo, Nat.not_le.mpr this]
      · simp [hlo]
    have card_eq : (Finset.Icc lo hi).card = n := by
      simp only [Nat.card_Icc]
      omega
    have eq1 : (1 : ℝ≥0∞) = ∑' a, (choose lo hi h : SPMF Nat) a := by
      calc (1 : ℝ≥0∞)
        _ = (n : ℝ≥0∞) * (1 / (n : ℝ≥0∞)) := by
            rw [ENNReal.mul_div_cancel (Nat.cast_ne_zero.mpr hn) (ENNReal.natCast_ne_top n)]
        _ = (Finset.Icc lo hi).card • (1 / (n : ℝ≥0∞)) := by
            simp only [nsmul_eq_mul, card_eq]
        _ = ∑ _a ∈ Finset.Icc lo hi, (1 : ℝ≥0∞) / (n : ℝ≥0∞) :=
            (Finset.sum_const _).symm
        _ = ∑ a ∈ Finset.Icc lo hi, (choose lo hi h : SPMF Nat) a := by
            apply Finset.sum_congr rfl
            intro x hx
            simp only [RandomChoice.choose, instFunLike]
            have n_eq : (n : ℝ≥0∞) = ↑hi - ↑lo + 1 := by
              simp only [n]
              norm_cast
            simp [Finset.mem_Icc.mp hx, n_eq]
        _ = ∑' a, (choose lo hi h : SPMF Nat) a :=
            (tsum_eq_sum hsupp).symm
    exact le_of_eq eq1

-- TODO: Change to mass_map
theorem mass_bind_pure {x : SPMF α} {f : α → β} :
    (x >>= fun a => Pure.pure (f a)).mass = x.mass := by
  classical
  unfold mass
  simp only [Bind.bind, bind, Pure.pure, pure, DFunLike.coe]
  rw [ENNReal.tsum_comm]
  congr 1
  ext a
  rw [tsum_eq_single (f a)]
  · simp
  · intro b hb
    simp only [mul_ite, mul_one, mul_zero]
    split_ifs with heq
    · simp_all
    · rfl

-- TODO: There are a lot of bind lemmas here; we should try to generalize them if possible. Also,

theorem mass_bind_const {x : SPMF α} {y : SPMF β} :
    (x >>= fun _ => y).mass = x.mass * y.mass := by
  unfold mass
  simp only [Bind.bind, bind, DFunLike.coe]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_mul_right]

theorem mass_bind_of_const_mass {x : SPMF α} {f : α → SPMF β} {c : ℝ≥0∞}
    (hx : x.mass = 1) (hf : ∀ a, (f a).mass = c) :
    (x >>= f).mass = c := by
  unfold mass at *
  simp only [Bind.bind, bind, DFunLike.coe]
  rw [ENNReal.tsum_comm]
  calc ∑' a, ∑' b, x a * (f a) b
    _ = ∑' a, x a * (∑' b, (f a) b) := by simp_rw [ENNReal.tsum_mul_left]
    _ = ∑' a, x a * c := by simp_rw [hf]
    _ = c * ∑' a, x a := by rw [ENNReal.tsum_mul_right]; ring
    _ = c * 1 := by rw [hx]
    _ = c := by ring

theorem mass_bind {x : SPMF α} {f : α → SPMF β} (hf : ∀ a, (f a).mass = 1) :
    (x >>= f).mass = x.mass := by
  unfold mass at *
  simp only [Bind.bind, bind, DFunLike.coe]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]
  calc ∑' a, x a * ∑' b, (f a) b
    _ = ∑' a, x a * 1 := by simp_rw [hf]
    _ = ∑' a, x a := by simp

theorem mass_bind_ge_of_ge {x : SPMF α} {f : α → SPMF β} {c : ℝ≥0∞}
    (hx : x.mass = 1) (hf : ∀ a, (f a).mass ≥ c) :
    (x >>= f).mass ≥ c := by
  unfold mass at *
  simp only [Bind.bind, bind, DFunLike.coe]
  rw [ENNReal.tsum_comm]
  calc ∑' a, ∑' b, x a * (f a) b
    _ = ∑' a, x a * (∑' b, (f a) b) := by simp_rw [ENNReal.tsum_mul_left]
    _ ≥ ∑' a, x a * c := by
        apply ENNReal.tsum_le_tsum
        intro a
        gcongr
        exact hf a
    _ = c * ∑' a, x a := by rw [ENNReal.tsum_mul_right]; ring
    _ = c * 1 := by rw [hx]
    _ = c := by ring

theorem mass_eq_one_of_half_plus_half_self {p : SPMF α}
    (h : p.mass = 1/2 + 1/2 * p.mass) : p.mass = 1 := by
  have hle : p.mass ≤ 1 := p.tsum_coe
  have hne_top : p.mass ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)
  have h2ne0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2netop : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have h12 : (1/2 : ℝ≥0∞) * 2 = 1 := ENNReal.div_mul_cancel h2ne0 h2netop
  have hmul : 2 * p.mass = 1 + p.mass := by
    conv_lhs => rw [h]
    calc 2 * (1/2 + 1/2 * p.mass)
      _ = 2 * (1/2) + 2 * (1/2 * p.mass) := by rw [mul_add]
      _ = 2 * (1/2) + 2 * (1/2) * p.mass := by rw [mul_assoc]
      _ = 1 + 1 * p.mass := by rw [mul_comm 2 (1/2), h12]
      _ = 1 + p.mass := by rw [one_mul]
  have hsub : 2 * p.mass - p.mass = 1 := by
    rw [hmul]
    exact ENNReal.add_sub_cancel_right hne_top
  have hlhs : 2 * p.mass - p.mass = p.mass := by
    have : (2 : ℝ≥0∞) * p.mass = p.mass + p.mass := by ring
    rw [this]
    exact ENNReal.add_sub_cancel_left hne_top
  rw [hlhs] at hsub
  exact hsub

end mass

section is_pmf

/-- An SPMF is a PMF if the mass sums to exactly 1.

We conjecture that, this means that the probability of non-termination is vanishingly small, and
therefore that the generator almost-surely terminates. -/
def IsPMF (p : SPMF α) : Prop := p.mass = 1

theorem IsPMF_pick {x y : SPMF α} (hx : IsPMF x) (hy : IsPMF y) : IsPMF (pick (fun () => x) (fun () => y)) := by
  unfold IsPMF mass at *
  rw [tsum_pick, hx, hy]
  simp only [mul_one]
  exact ENNReal.add_halves 1

theorem IsPMF_pure (a : α) : IsPMF (Pure.pure a : SPMF α) := mass_pure a

theorem IsPMF_choose (lo hi : Nat) (h : lo ≤ hi) : IsPMF (choose lo hi h : SPMF Nat) :=
  mass_choose lo hi h

theorem IsPMF_bind_pure {x : SPMF α} {f : α → β} (hx : IsPMF x) :
    IsPMF (x >>= fun a => Pure.pure (f a)) := by
  unfold IsPMF
  rw [mass_bind_pure, hx]

theorem IsPMF_bind {x : SPMF α} {f : α → SPMF β} (hx : IsPMF x) (hf : ∀ a, IsPMF (f a)) :
    IsPMF (x >>= f) := by
  unfold IsPMF
  rw [mass_bind hf, hx]

-- TODO: This is pretty specific. Can we generalize?
theorem IsPMF_pick_pure_of_mass_eq {a : α} {body : SPMF α} {full : SPMF α}
    (h_eq : full = pick (fun () => Pure.pure a) (fun () => body))
    (h_mass : body.mass = full.mass) : IsPMF full := by
  unfold IsPMF
  apply mass_eq_one_of_half_plus_half_self
  calc full.mass
    _ = (pick (fun () => Pure.pure a) (fun () => body)).mass := by rw [h_eq]
    _ = 1/2 * (Pure.pure a : SPMF α).mass + 1/2 * body.mass := mass_pick
    _ = 1/2 * 1 + 1/2 * body.mass := by rw [mass_pure]
    _ = 1/2 + 1/2 * full.mass := by rw [h_mass]; ring

-- TODO: This is also too specific. This should be true for weights `w` and `1 - w`, right?
theorem IsPMF_of_half_plus_half_weighted_avg
    {ι : Type*} {α : Type*} [Nonempty ι]
    (g : ι → SPMF α)
    (body_mass : ι → ℝ≥0∞)
    (h_body_ge : ∀ i, body_mass i ≥ ⨅ j, (g j).mass)
    (h_rec : ∀ i, (g i).mass = 1/2 + 1/2 * body_mass i) :
    ∀ i, IsPMF (g i) := by
  intro i
  unfold IsPMF
  apply le_antisymm
  · exact (g i).tsum_coe
  · let c := ⨅ j, (g j).mass
    have hc_le : c ≤ (g i).mass := iInf_le _ i
    have hc_ge_one : c ≥ 1 := by
      have h_lower : ∀ j, (g j).mass ≥ 1/2 + 1/2 * c := fun j => by
        have hbody : body_mass j ≥ c := h_body_ge j
        calc (g j).mass
          _ = 1/2 + 1/2 * body_mass j := h_rec j
          _ ≥ 1/2 + 1/2 * c := by
              gcongr
      have hiInf_lower : c ≥ 1/2 + 1/2 * c := le_ciInf (fun j => h_lower j)
      have hne_top : c ≠ ⊤ := by
        apply ne_of_lt
        calc c ≤ (g i).mass := hc_le
          _ ≤ 1 := (g i).tsum_coe
          _ < ⊤ := ENNReal.one_lt_top
      have h2ne0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
      have h2netop : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
      have h12 : (1/2 : ℝ≥0∞) * 2 = 1 := ENNReal.div_mul_cancel h2ne0 h2netop
      have hmul : 2 * c ≥ 1 + c := by
        have h1 : 2 * c ≥ 2 * (1/2 + 1/2 * c) := by
          gcongr
        calc 2 * c
          _ ≥ 2 * (1/2 + 1/2 * c) := h1
          _ = 2 * (1/2) + 2 * (1/2) * c := by ring
          _ = 1 + 1 * c := by rw [mul_comm 2 (1/2), h12]
          _ = 1 + c := by ring
      have h2c_eq : 2 * c = c + c := by ring
      rw [h2c_eq] at hmul
      have hmul' : c + 1 ≤ c + c := by rw [add_comm 1 c] at hmul; exact hmul
      rwa [ENNReal.add_le_add_iff_left hne_top] at hmul'
    exact le_trans hc_ge_one hc_le

end is_pmf

end SPMF
