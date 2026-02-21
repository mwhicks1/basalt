import Basalt.SPMF
import Basalt.RandomChoice

open Lean.Order RandomChoice

abbrev Counter (α : Type) : Type := SPMF (α × Nat)

namespace Counter

instance instPartialOrder : Lean.Order.PartialOrder (Counter α) where
  rel p q := @PartialOrder.rel (SPMF (α × Nat)) _ p q
  rel_refl := @PartialOrder.rel_refl (SPMF (α × Nat)) _
  rel_trans := @PartialOrder.rel_trans (SPMF (α × Nat)) _
  rel_antisymm := @PartialOrder.rel_antisymm (SPMF (α × Nat)) _

instance instCCPO : CCPO (Counter α) where
  has_csup := by
    intros c hc
    exact @CCPO.has_csup (SPMF (α × Nat)) _ c hc

instance instInhabited : Inhabited (Counter α) where
  default := @Bot.bot (SPMF (α × Nat)) _

noncomputable def pure (a : α) : Counter α :=
  SPMF.pure (a, 0)

noncomputable def bind (m : Counter α) (f : α → Counter β) : Counter β :=
  SPMF.bind m fun pair =>
    SPMF.bind (f pair.1) fun pair2 =>
      SPMF.pure (pair2.1, pair.2 + pair2.2)

noncomputable instance instMonad : Monad Counter where
  pure := pure
  bind := bind

instance instMonoBind : MonoBind Counter where
  bind_mono_left {α β} {m₁ m₂ : Counter α} {f : α → Counter β} (h : m₁ ⊑ m₂) := by
    intro pair
    simp only [Bind.bind, bind]
    unfold SPMF.bind
    apply ENNReal.tsum_le_tsum
    intro ⟨a, n₁⟩
    simp only [Lean.Order.PartialOrder.rel] at h
    gcongr
    exact h (a, n₁)
  bind_mono_right {α β} {m : Counter α} {f₁ f₂ : α → Counter β} (h : ∀ a, f₁ a ⊑ f₂ a) := by
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

noncomputable instance instRandomChoice : RandomChoice Counter where
  choose lo hi h :=
    SPMF.bind (@RandomChoice.choose SPMF _ lo hi h) fun n => SPMF.pure (n, 1)

end Counter
