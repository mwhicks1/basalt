import Basalt

open RandomChoice

namespace BST

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
    t ∈ SPMF.support (Tree.genBST lo hi) ↔ t ∈ {t | Tree.isBST lo hi t} := by
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
    intro c hle hge
    apply ENNReal.eq_one_of_fixed_ineq hle _ hge
    . intro hmono hle'
      rw [ENNReal.toReal_add (by norm_num) (by aesop), ENNReal.toReal_mul] at hmono
      norm_num at hmono
      nlinarith
    . aesop
  case mass =>
    intro ⟨lo, hi⟩ hc_le
    dsimp only
    by_cases hlt : lo > hi
    · rw [Tree.genBST, dif_pos hlt, SPMF.mass_pure]
      conv_lhs => rw [← ENNReal.add_halves 1]
      simp [mul_le_of_le_one_right, zero_le, pow_le_one₀, hc_le]
    · push_neg at hlt
      conv_lhs => rw [Tree.genBST, dif_neg (by omega)]
      rw [SPMF.mass_pick, SPMF.mass_pure, mul_one]
      gcongr
      rw [sq]
      apply le_trans (Eq.le (one_mul _).symm)
      apply SPMF.mass_bind_ge_mul (SPMF.IsPMF_choose lo hi hlt).symm.le
      intro x
      apply SPMF.mass_bind_ge_mul (iInf_le _ (lo, x - 1))
      intro l
      exact le_trans (iInf_le _ (x + 1, hi)) SPMF.mass_bind_pure.symm.le

/-- `genBST` makes a linear number of choices in the size of the tree it generates (no backtracking choices). -/
theorem Tree.genBST_cost :
    IsBounded (Tree.genBST lo hi) (fun t => 3 * t.size + 1) := by
  open Lean.Order in
  delta genBST
  apply (fix_induct (motive := fun (g : Nat → Nat → SPMF.Cost (Tree Nat)) => ∀ lo hi, IsBounded (g lo hi) (fun t => 3 * t.size + 1)) _ ?admissible ?step)
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
        SPMF.Cost.mem_support_bind_iff,
        SPMF.Cost.mem_support_choose_iff,
        SPMF.Cost.mem_support_pure_iff
      ]

instance {lo hi : Nat} : LawfulGenerator (Tree.genBST lo hi) (Tree.isBST lo hi) (fun t => 3 * t.size + 1) where
  is_correct := Tree.genBST_support
  is_ast := Tree.genBST_terminates
  is_cost_bounded := Tree.genBST_cost

/- `genBST` can be run in `IO`. -/
#guard_msgs(drop info) in
#eval (for _ in [0:20] do
  IO.println <| repr (← Tree.genBST 0 10) : IO Unit)

end BST
