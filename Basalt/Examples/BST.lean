import Basalt

open RandomChoice

namespace TreeExample

inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α
deriving Repr

def Tree.isBST (lo hi : Nat) : Tree Nat → Prop
  | leaf => true
  | node l x r =>
    lo ≤ x ∧ x ≤ hi ∧
    isBST lo (x - 1) l ∧
    isBST (x + 1) hi r

def Tree.genBST (lo hi : Nat) : Gen (Tree Nat) := do
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

#guard_msgs(drop info) in
#eval (for _ in [0:20] do
  IO.println <| repr (← Gen.runIO (Tree.genBST 0 10)) : IO Unit)


end TreeExample
