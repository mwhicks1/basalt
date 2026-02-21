import Basalt.Counter
import Basalt.Gen

open RandomChoice

def genOneOrTwo : Gen Nat := do
  if (← choose 0 1 (by simp)) == 0 then
    pure 1
  else
    pure 2

example : (1, 1) ∈ (genOneOrTwo : Counter Nat).support := by
  unfold genOneOrTwo
  simp [bind, pure, Counter.bind, Counter.pure, choose, SPMF.support, SPMF.pure, SPMF.bind, DFunLike.coe]
  exists 0
  simp

example : (a, count) ∈ (genOneOrTwo : Counter Nat).support → count = 1 := by
  intro h
  unfold genOneOrTwo at h
  simp [bind, pure, Counter.bind, Counter.pure, choose, SPMF.support, SPMF.pure, SPMF.bind, DFunLike.coe] at h
  grind

def Nat.arbitrary : Gen Nat := do
  pick
    (fun () => pure 0)
    (fun () => do
      let n ← Nat.arbitrary
      pure (n + 1))
partial_fixpoint

example : (n, count) ∈ (Nat.arbitrary : Counter Nat).support → count = n + 1 := by
  intro h
  induction n generalizing count with
  | zero =>
    unfold Nat.arbitrary at h
    simp [bind, pure, Counter.bind, Counter.pure, pick, choose, SPMF.support, SPMF.pure, SPMF.bind, DFunLike.coe] at h
    aesop
  | succ n' ih =>
    unfold Nat.arbitrary at h
    simp [bind, pure, Counter.bind, Counter.pure, pick, choose, SPMF.support, SPMF.pure, SPMF.bind, DFunLike.coe] at h
    aesop (config := {warnOnNonterminal := false})
    have := ih (by aesop)
    grind
