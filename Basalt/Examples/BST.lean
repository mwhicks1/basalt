import Basalt
import Basalt.Cost.CostSPMF

open RandomChoice

namespace TreeExample

inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α
deriving Repr

def Tree.size : Tree α → Nat
  | leaf => 0
  | node l _ r => l.size + r.size + 1

def Tree.isBST (lo hi : Nat) : Tree Nat → Prop
  | leaf => true
  | node l x r =>
    lo ≤ x ∧ x ≤ hi ∧
    isBST lo (x - 1) l ∧
    isBST (x + 1) hi r

def Tree.genBST [Gen G] (lo hi : Nat) : G (Tree Nat) := do
  if h : lo > hi then
    return leaf
  else
    pick
      (fun () => pure leaf)
      (fun () => do
        let x ← choose lo hi (by omega)
        let l ← Tree.genBST lo (x - 1)
        let r ← Tree.genBST (x + 1) hi
        return node l x r)
partial_fixpoint

/-- `genBST` produces the correct set of inputs. -/
theorem Tree.genBST_support :
    SPMF.support (Tree.genBST lo hi) = {t | Tree.isBST lo hi t} := by
  refine (Set.ext ?_)
  intro t
  simp
  fun_induction Tree.isBST
    <;> rw [Tree.genBST]
    <;> split
    <;> simp
    <;> grind

/-- `genBST` terminates with probability 1. -/
theorem Tree.genBST_terminates : SPMF.IsPMF (Tree.genBST lo hi) := by
  haveI : Nonempty (Nat × Nat) := ⟨(0, 0)⟩
  refine (SPMF.IsPMF_of_mass_fixpoint
      (g := fun (lo, hi) => (Tree.genBST lo hi : SPMF (Tree Nat)))
      (F := fun c => 1 / 2 + 1 / 2 * c ^ 2)
      ?bounds ?mass) (lo, hi)
  case bounds =>
    intro c hc_le h
    have hc_ne  : c ≠ ⊤     := ne_top_of_le_ne_top ENNReal.one_ne_top hc_le
    have hc2_ne : c ^ 2 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (pow_le_one₀ (zero_le _) hc_le)
    have hle : c.toReal ≤ 1 := by simpa using (ENNReal.toReal_le_toReal hc_ne ENNReal.one_ne_top).mpr hc_le
    have hge : c.toReal ≥ 1 / 2 + 1 / 2 * c.toReal ^ 2 := by
      have h2ne : (1 / 2 + 1 / 2 * c ^ 2 : ENNReal) ≠ ⊤ :=
        ENNReal.add_ne_top.mpr ⟨by norm_num, ENNReal.mul_ne_top (by norm_num) hc2_ne⟩
      have hmono := (ENNReal.toReal_le_toReal h2ne hc_ne).mpr h
      rw [ENNReal.toReal_add (by norm_num) (ENNReal.mul_ne_top (by norm_num) hc2_ne),
          ENNReal.toReal_mul, ENNReal.toReal_pow] at hmono
      norm_num at hmono
      linarith
    have hone : c.toReal = 1 := by nlinarith
    rw [← ENNReal.ofReal_toReal hc_ne, hone, ENNReal.ofReal_one]
  case mass =>
    intro ⟨lo', hi'⟩ hc_le
    dsimp only
    by_cases hlt : lo' > hi'
    · rw [Tree.genBST, dif_pos hlt, SPMF.mass_pure]
      calc (1 : ENNReal) = 1 / 2 + 1 / 2 := (ENNReal.add_halves 1).symm
        _ ≥ 1 / 2 + 1 / 2 * (⨅ p : Nat × Nat, (Tree.genBST p.1 p.2 : SPMF (Tree Nat)).mass) ^ 2 := by
            gcongr
            exact mul_le_of_le_one_right (zero_le _) (pow_le_one₀ (zero_le _) hc_le)
    · push_neg at hlt
      conv_lhs => rw [Tree.genBST, dif_neg (show ¬lo' > hi' by omega)]
      rw [SPMF.mass_pick, SPMF.mass_pure, mul_one]
      gcongr
      simpa [one_mul] using SPMF.mass_bind_ge_mul
          (SPMF.IsPMF_choose lo' hi' hlt).symm.le
          (fun x => by
            rw [sq]
            apply SPMF.mass_bind_ge_mul (iInf_le _ (lo', x - 1))
            intro l
            exact le_trans (iInf_le _ (x + 1, hi')) SPMF.mass_bind_pure.symm.le)

/-- `genBST` makes a linear number of choices in the size of the tree it generates (no backtracking choices). -/
theorem Tree.genBST_cost :
    ∃ m b, IsBounded (Tree.genBST lo hi) (fun t => m * t.size + b) := by
  open Lean.Order in
  exists 3; exists 1
  delta genBST
  apply (fix_induct (motive := fun (g : Nat → Nat → CostSPMF (Tree Nat)) => ∀ lo hi, IsBounded (g lo hi) (fun t => 3 * t.size + 1)) _ ?admissible ?step)
  case admissible =>
    exact admissible_pi_apply _ fun _ => admissible_pi_apply _ fun _ => admissible_IsBounded _
  case step =>
    intro genBST_rec ih lo hi
    simp [IsBounded_iff] at *
    intro t n hn
    split at hn
    · simp_all
    · grind only [
        pick,
        size,
        CostSPMF.mem_support_bind_iff,
        CostSPMF.mem_support_choose_iff,
        CostSPMF.mem_support_pure_iff
      ]

/- `genBST` can be run in `IO`. -/
#guard_msgs(drop info) in
#eval (for _ in [0:20] do
  IO.println <| repr (← Tree.genBST 0 10) : IO Unit)

end TreeExample
