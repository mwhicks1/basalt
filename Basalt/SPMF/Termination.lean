/-
Copyright (c) 2025 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.SPMF.Support

open Lean.Order RandomChoice NNReal ENNReal MeasureTheory

/-!
# SPMF Mass and Termination

<TODO: summarize>

## Main Definitions

- `SPMF.mass` — <fill in>
- `SPMF.IsPMF` — <fill in>

## Main Theorems

- `IsPMF_of_positive_termination_prob` — <fill in>
- `IsPMF_of_mass_fixpoint` — <fill in>
- `ENNReal.eq_one_of_fixed_ineq` — <fill in>
-/

namespace SPMF

section mass

/-- The total mass of an SPMF. Always ≤ 1 by definition. -/
noncomputable def mass (p : SPMF α) : ℝ≥0∞ := ∑' a, p a

/-- TODO: document -/
theorem mass_eq_zero_of_support_empty {p : SPMF α} (h : p.support = ∅) : p.mass = 0 := by
  unfold mass
  rw [ENNReal.tsum_eq_zero]
  intro a
  rw [apply_eq_zero_iff]
  exact Set.eq_empty_iff_forall_notMem.mp h a

/-- TODO: document -/
theorem mass_pick {x y : SPMF α} :
    (pick (fun () => x) (fun () => y)).mass = (1/2 : ℝ≥0∞) * x.mass + (1/2 : ℝ≥0∞) * y.mass := tsum_pick

/-- TODO: document -/
@[simp]
theorem mass_bot : Bot.bot (α := SPMF α).mass = 0 := by
  simp only [mass, ENNReal.tsum_eq_zero]
  solve_by_elim

/-- TODO: document -/
theorem mass_eq_zero_iff {x : SPMF α} : x.mass = 0 ↔ x = Bot.bot := by
  constructor
  · intro h
    ext a
    have : ∑' a, x a = 0 := h
    exact (ENNReal.tsum_eq_zero.mp this) a
  · intro h
    simp [h]

/-- TODO: document -/
theorem mass_pure (a : α) : (Pure.pure a : SPMF α).mass = 1 := by
  unfold mass
  simp only [Pure.pure, pure, DFunLike.coe]
  rw [tsum_eq_single a]
  · simp
  · intro a' ha'
    simp [ha']

/-- TODO: document -/
theorem mass_choose (lo hi : Nat) (h : lo ≤ hi) : (choose lo hi h : SPMF Nat).mass = 1 := by
  unfold mass
  apply le_antisymm
  · exact (choose lo hi h : SPMF Nat).tsum_coe
  · let n : ℕ := hi - lo + 1
    have hn : n ≠ 0 := Nat.add_one_ne_zero _
    have hsupp : ∀ a, a ∉ Finset.Icc lo hi →
        ((choose lo hi h : SPMF Nat) a) = 0 := by
      intro a ha
      simp only [RandomChoice.choose, DFunLike.coe]
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
            simp only [RandomChoice.choose, DFunLike.coe]
            have n_eq : (n : ℝ≥0∞) = ↑hi - ↑lo + 1 := by
              simp only [n]
              norm_cast
            simp [Finset.mem_Icc.mp hx, n_eq]
        _ = ∑' a, (choose lo hi h : SPMF Nat) a :=
            (tsum_eq_sum hsupp).symm
    exact le_of_eq eq1

/-- TODO: document -/
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

/-- TODO: document -/
theorem mass_map {x : SPMF α} {f : α → β} :
    (f <$> x).mass = x.mass := by
  classical
  unfold mass
  simp only [Functor.map, bind, pure, DFunLike.coe, Function.comp_apply]
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

/-- TODO: document -/
theorem mass_bind_const {x : SPMF α} {y : SPMF β} :
    (x >>= fun _ => y).mass = x.mass * y.mass := by
  unfold mass
  simp only [Bind.bind, bind, DFunLike.coe]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_mul_right]

/-- TODO: document -/
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

/-- TODO: document -/
theorem mass_bind {x : SPMF α} {f : α → SPMF β} (hf : ∀ a, (f a).mass = 1) :
    (x >>= f).mass = x.mass := by
  unfold mass at *
  simp only [Bind.bind, bind, DFunLike.coe]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]
  calc ∑' a, x a * ∑' b, (f a) b
    _ = ∑' a, x a * 1 := by simp_rw [hf]
    _ = ∑' a, x a := by simp

/-- TODO: document -/
theorem mass_bind_ge_mul {x : SPMF α} {f : α → SPMF β} {c d : ℝ≥0∞}
    (hx : x.mass ≥ c) (hf : ∀ a, (f a).mass ≥ d) : (x >>= f).mass ≥ c * d := by
  have h : (x >>= f).mass ≥ x.mass * d := by
    simp only [mass, Bind.bind, bind, DFunLike.coe]
    rw [ENNReal.tsum_comm]
    simp [ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
    gcongr with a; exact hf a
  calc (x >>= f).mass ≥ x.mass * d := h
    _ ≥ c * d := by gcongr

end mass

section is_pmf

/-- An SPMF is a PMF if the mass sums to exactly 1.

We conjecture that, this means that the probability of non-termination is vanishingly small, and
therefore that the generator almost-surely terminates. -/
def IsPMF (p : SPMF α) : Prop := p.mass = 1

/-- TODO: document -/
theorem IsPMF_pick {x y : SPMF α} (hx : IsPMF x) (hy : IsPMF y) : IsPMF (pick (fun () => x) (fun () => y)) := by
  unfold IsPMF mass at *
  rw [tsum_pick, hx, hy]
  simp only [mul_one]
  exact ENNReal.add_halves 1

/-- TODO: document -/
theorem IsPMF_pure (a : α) : IsPMF (Pure.pure a : SPMF α) := mass_pure a

/-- TODO: document -/
theorem IsPMF_choose (lo hi : Nat) (h : lo ≤ hi) : IsPMF (choose lo hi h : SPMF Nat) :=
  mass_choose lo hi h

/-- TODO: document -/
theorem IsPMF_bind_pure {x : SPMF α} {f : α → β} (hx : IsPMF x) :
    IsPMF (x >>= fun a => Pure.pure (f a)) := by
  unfold IsPMF
  rw [mass_bind_pure, hx]

/-- TODO: document -/
theorem IsPMF_bind {x : SPMF α} {f : α → SPMF β} (hx : IsPMF x) (hf : ∀ a, IsPMF (f a)) :
    IsPMF (x >>= f) := by
  unfold IsPMF
  rw [mass_bind hf, hx]

/-- TODO: document -/
lemma weighted_avg_mono_ennreal {t p x : ℝ≥0∞}
    (htp : t ≥ p) (hx_le_one : x ≤ 1) (ht_le_one : t ≤ 1) (hp_le_one : p ≤ 1) :
    t + (1 - t) * x ≥ p + (1 - p) * x := by
  have ht_ne_top : t ≠ ⊤ := ne_of_lt (lt_of_le_of_lt ht_le_one ENNReal.one_lt_top)
  have hp_ne_top : p ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hp_le_one ENNReal.one_lt_top)
  have hx_ne_top : x ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hx_le_one ENNReal.one_lt_top)
  have h1mt_ne_top : (1 - t) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have h1mp_ne_top : (1 - p) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have heq_t : t + (1 - t) * x = t * (1 - x) + x := by
    calc t + (1 - t) * x
      _ = t * 1 + (1 - t) * x := by rw [mul_one]
      _ = t * ((1 - x) + x) + (1 - t) * x := by rw [tsub_add_cancel_of_le hx_le_one]
      _ = t * (1 - x) + t * x + (1 - t) * x := by rw [mul_add]
      _ = t * (1 - x) + (t * x + (1 - t) * x) := by rw [add_assoc]
      _ = t * (1 - x) + (t + (1 - t)) * x := by rw [add_mul]
      _ = t * (1 - x) + 1 * x := by rw [add_tsub_cancel_of_le ht_le_one]
      _ = t * (1 - x) + x := by rw [one_mul]
  have heq_p : p + (1 - p) * x = p * (1 - x) + x := by
    calc p + (1 - p) * x
      _ = p * 1 + (1 - p) * x := by rw [mul_one]
      _ = p * ((1 - x) + x) + (1 - p) * x := by rw [tsub_add_cancel_of_le hx_le_one]
      _ = p * (1 - x) + p * x + (1 - p) * x := by rw [mul_add]
      _ = p * (1 - x) + (p * x + (1 - p) * x) := by rw [add_assoc]
      _ = p * (1 - x) + (p + (1 - p)) * x := by rw [add_mul]
      _ = p * (1 - x) + 1 * x := by rw [add_tsub_cancel_of_le hp_le_one]
      _ = p * (1 - x) + x := by rw [one_mul]
  have h1 : t * (1 - x) + x ≥ p * (1 - x) + x := by
    have : t * (1 - x) ≥ p * (1 - x) := mul_le_mul_left htp (1 - x)
    exact add_le_add this (le_refl x)
  rw [heq_t, heq_p]
  exact h1

/-- TODO: document -/
theorem IsPMF_of_positive_termination_prob
    {ι : Type*} {α : Type*} [Nonempty ι]
    (g : ι → SPMF α)
    (p : ℝ≥0∞)
    (hp_pos : p > 0)
    (hp_le_one : p ≤ 1)
    (term_prob : ι → ℝ≥0∞)
    (body_mass : ι → ℝ≥0∞)
    (h_term_ge : ∀ i, term_prob i ≥ p)
    (h_body_ge : ∀ i, body_mass i ≥ ⨅ j, (g j).mass)
    (h_rec : ∀ i, (g i).mass ≥ term_prob i + (1 - term_prob i) * body_mass i) :
    ∀ i, IsPMF (g i) := by
  intro i
  unfold IsPMF
  apply le_antisymm
  · exact (g i).tsum_coe
  · let c := ⨅ j, (g j).mass
    have hc_le : c ≤ (g i).mass := iInf_le _ i
    have hne_top : c ≠ ⊤ := by
      apply ne_of_lt
      calc c ≤ (g i).mass := hc_le
        _ ≤ 1 := (g i).tsum_coe
        _ < ⊤ := ENNReal.one_lt_top
    have hc_ge_one : c ≥ 1 := by
      have h_lower : ∀ j, (g j).mass ≥ p + (1 - p) * c := fun j => by
        have hterm : term_prob j ≥ p := h_term_ge j
        have hbody : body_mass j ≥ c := h_body_ge j
        have hterm_le_one : term_prob j ≤ 1 := by
          calc term_prob j ≤ (g j).mass := by
                have := h_rec j
                calc term_prob j ≤ term_prob j + (1 - term_prob j) * body_mass j := le_self_add
                  _ ≤ (g j).mass := this
            _ ≤ 1 := (g j).tsum_coe
        have hc_le_one : c ≤ 1 := by
          calc c ≤ (g i).mass := hc_le
            _ ≤ 1 := (g i).tsum_coe
        have h_weighted : term_prob j + (1 - term_prob j) * c ≥ p + (1 - p) * c := by
          exact weighted_avg_mono_ennreal hterm hc_le_one hterm_le_one hp_le_one
        calc (g j).mass
          _ ≥ term_prob j + (1 - term_prob j) * body_mass j := h_rec j
          _ ≥ term_prob j + (1 - term_prob j) * c := by gcongr
          _ ≥ p + (1 - p) * c := h_weighted
      have hiInf_lower : c ≥ p + (1 - p) * c := le_ciInf (fun j => h_lower j)
      by_cases hp_one : p = 1
      · calc c ≥ p + (1 - p) * c := hiInf_lower
          _ = 1 + (1 - 1) * c := by rw [hp_one]
          _ = 1 := by simp
      · have hp_lt_one : p < 1 := lt_of_le_of_ne hp_le_one hp_one
        have hp_ne_top : p ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hp_le_one ENNReal.one_lt_top)
        by_cases hc_zero : c = 0
        · exfalso
          rw [hc_zero] at hiInf_lower
          simp at hiInf_lower
          exact ne_of_gt hp_pos hiInf_lower
        · have h1mp_ne_top : (1 - p) ≠ ⊤ := by
            apply ne_of_lt
            calc 1 - p ≤ 1 := tsub_le_self
              _ < ⊤ := ENNReal.one_lt_top
          have h1mpc_ne_top : (1 - p) * c ≠ ⊤ := by
            apply ENNReal.mul_ne_top h1mp_ne_top hne_top
          have h1 : c * p ≥ p := by
            have hsub_ge : c - (1 - p) * c ≥ p := by
              calc c - (1 - p) * c ≥ (p + (1 - p) * c) - (1 - p) * c := by gcongr
                _ = p := ENNReal.add_sub_cancel_right h1mpc_ne_top
            have hsub_eq : c - (1 - p) * c = c * p := by
              rw [mul_comm (1 - p) c]
              have h1m1mp : (1 : ℝ≥0∞) - (1 - p) = p := ENNReal.sub_sub_cancel ENNReal.one_ne_top hp_le_one
              have hmul_sub : c * (1 - (1 - p)) = c * 1 - c * (1 - p) := by
                rw [ENNReal.mul_sub]
                intro h1mp_pos h1mp_lt_one
                exact hne_top
              rw [h1m1mp] at hmul_sub
              rw [mul_one] at hmul_sub
              exact hmul_sub.symm
            rw [← hsub_eq]
            exact hsub_ge
          have hc_ge_one' : c ≥ 1 := by
            have hdiv : c * p / p ≥ p / p := by gcongr
            rw [ENNReal.mul_div_cancel_right _ hp_ne_top] at hdiv
            rw [ENNReal.div_self (ne_of_gt hp_pos) hp_ne_top] at hdiv
            exact hdiv
            exact ne_of_gt hp_pos
          exact hc_ge_one'
    calc (g i).mass ≥ c := hc_le
      _ ≥ 1 := hc_ge_one

/-- A general fixpoint principle for proving almost-sure termination.

If the mass of each generator satisfies `mass ≥ F(inf mass)` and `F` is such that
`c ≤ 1 ∧ c ≥ F c → c = 1`, then all generators are PMFs. -/
theorem IsPMF_of_mass_fixpoint {ι : Type*} {α : Type*} [Nonempty ι]
    (g : ι → SPMF α) (F : ℝ≥0∞ → ℝ≥0∞)
    (hF : ∀ c : ℝ≥0∞, c ≤ 1 → c ≥ F c → c = 1)
    (h_step : ∀ i, (⨅ j, (g j).mass) ≤ 1 → (g i).mass ≥ F (⨅ j, (g j).mass)) :
    ∀ i, IsPMF (g i) := by
  intro i
  unfold IsPMF
  apply le_antisymm (g i).tsum_coe
  have hc_le : (⨅ j, (g j).mass) ≤ 1 := (iInf_le _ i).trans (g i).tsum_coe
  have hc_ge_F : (⨅ j, (g j).mass) ≥ F (⨅ j, (g j).mass) := le_iInf (fun j => h_step j hc_le)
  calc (1 : ℝ≥0∞) = ⨅ j, (g j).mass := (hF _ hc_le hc_ge_F).symm
    _ ≤ (g i).mass := iInf_le _ i

end is_pmf

end SPMF

/-- If `c ≤ 1`, `v ≠ ⊤`, `c ≥ v`, and real arithmetic shows `x ≥ v.toReal ∧ x ≤ 1 → x = 1`,
then `c = 1`. Used to close the `bounds` case of `IsPMF_of_mass_fixpoint` proofs. -/
lemma ENNReal.eq_one_of_fixed_ineq {c v : ENNReal}
    (hle : c ≤ 1) (hv_ne : v ≠ ⊤) (hge : c ≥ v)
    (hf_one : c.toReal ≥ v.toReal → c.toReal ≤ 1 → c.toReal = 1) : c = 1 := by
  have hc_ne : c ≠ ⊤ := ne_top_of_le_ne_top one_ne_top hle
  have hle' : c.toReal ≤ 1 := (toReal_le_toReal hc_ne one_ne_top).mpr hle
  have hmono := (toReal_le_toReal hv_ne hc_ne).mpr hge
  rw [← ofReal_toReal hc_ne, hf_one hmono hle', ofReal_one]
