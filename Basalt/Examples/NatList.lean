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
  induction n <;> rw [Nat.arbitrary] <;> simp
  grind

def List.arbitrary : Gen (List Nat) := do
  pick
    (fun () => pure [])
    (fun () => do
      let x ← Nat.arbitrary
      let xs ← List.arbitrary
      return x :: xs)
partial_fixpoint

def List.genSorted (m : Nat) : Gen (List Nat) := do
  pick
    (fun () => pure [])
    (fun () => do
      let delta ← Nat.arbitrary
      let x := m + delta
      let xs ← List.genSorted x
      return x :: xs)
partial_fixpoint

theorem List.arbitrary_support : SPMF.support List.arbitrary = ⊤ := by
  simp
  refine (Set.ext ?_)
  intro xs
  induction xs <;> simp_all <;> rw [List.arbitrary] <;> simp_all
  apply Nat.arbitrary_support

def List.diverge : Gen (List Nat) := do
  let x ← RandomChoice.choose 0 10 (by simp)
  let xs ← List.diverge
  return x :: xs
partial_fixpoint

example : SPMF.support List.diverge = ∅ := by
  refine (Set.ext ?_)
  intro xs
  induction xs <;> rw [List.diverge] <;> simp
  grind

#guard_msgs(drop info) in
#eval (for _ in [0:20] do
  IO.println <| repr (← Gen.runIO List.arbitrary) : IO Unit)

end NatListExample
