import Basalt

open RandomChoice

namespace NatListExample

def Nat.arbitrary : Gen Nat := do
  pick
    (fun () => pure 0)
    (fun () => do
      let n ← Nat.arbitrary
      pure (n + 1))
partial_fixpoint

theorem Nat.arbitrary_support : n ∈ SPMF.support Nat.arbitrary := by
  induction n <;> rw [Nat.arbitrary] <;> simp [*]

def List.arbitrary : Gen (List Nat) := do
  pick
    (fun () => pure [])
    (fun () => do
      let x ← Nat.arbitrary
      let xs ← List.arbitrary
      return x :: xs)
partial_fixpoint

theorem List.arbitrary_support : SPMF.support List.arbitrary = Set.univ := by
  refine (Set.ext ?_)
  intro xs
  induction xs <;> rw [List.arbitrary]
  case _ => simp
  case _ x xs ih => simp [ih, Nat.arbitrary_support]

def List.genSorted (m : Nat) : Gen (List Nat) := do
  pick
    (fun () => pure [])
    (fun () => do
      let delta ← Nat.arbitrary
      let x := m + delta
      let xs ← List.genSorted x
      return x :: xs)
partial_fixpoint

def List.diverge : Gen (List Nat) := do
  let x ← RandomChoice.choose 0 10 (by simp)
  let xs ← List.diverge
  return x :: xs
partial_fixpoint

example : SPMF.support List.diverge = ∅ := by
  refine (Set.ext ?_)
  intro xs
  induction xs <;> rw [List.diverge] <;> simp [*]

inductive ListF (α β : Type) where
  | nilStep : ListF α β
  | consStep : α → β → ListF α β

def List.unfold (coalg : β → Gen (ListF α β)) (b : β) : Gen (List α) := do
  match ← coalg b with
  | .nilStep => return []
  | .consStep x b' => return x :: (← List.unfold coalg b')
partial_fixpoint

def List.genSorted' (m : Nat) : Gen (List Nat) :=
  List.unfold (fun m =>
    pick
      (fun () => pure .nilStep)
      (fun () => do
        let delta ← Nat.arbitrary
        let x := m + delta
        return .consStep x x))
    m

example : (List.genSorted m : SPMF _) = List.genSorted' m := by
  apply SPMF.ext
  intro xs
  induction xs generalizing m with
  | nil =>
    rw [List.genSorted, List.genSorted', List.unfold]
    rw [SPMF.bind_pick]
    simp only [SPMF.pick_apply]
    simp only [Bind.bind, Pure.pure, SPMF.pure, SPMF.bind, DFunLike.coe]
    simp
    nth_rewrite 1 [← add_zero (2⁻¹ : ENNReal)]
    congr 1
    symm
    rw [mul_eq_zero]
    right
    rw [ENNReal.tsum_eq_zero]
    intro a
    cases a with
    | nilStep => simp
    | consStep x b' => simp
  | cons x xs ih =>
    rw [List.genSorted, List.genSorted', List.unfold]
    rw [SPMF.bind_pick]
    simp only [SPMF.pick_apply]
    conv_rhs =>
      enter [1, 2]
      rw [pure_bind]
    conv_rhs =>
      enter [2, 2]
      rw [bind_assoc]
      enter [1, 2]
      intro x
      rw [pure_bind]
      dsimp
    dsimp [Pure.pure, SPMF.pure]
    congr 1
    refine congr_arg (HMul.hMul (1/2 : ENNReal)) ?_
    simp only [Bind.bind, SPMF.bind, DFunLike.coe]
    apply tsum_congr
    intro delta
    congr 1
    dsimp [Bind.bind, SPMF.bind, SPMF.instFunLike]
    apply tsum_congr
    intro l
    by_cases h : l = xs
    · subst h
      simp
      split
      · exact ih
      · rfl
    · have : x :: xs ≠ (m + delta) :: l := by
        intro c; injection c with _ h'; subst h'; contradiction
      simp [this]

#guard_msgs(drop info) in
#eval (for _ in [0:20] do
  IO.println <| repr (← Gen.runIO List.arbitrary) : IO Unit)

end NatListExample
