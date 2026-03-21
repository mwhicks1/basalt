import Basalt

open RandomChoice

namespace ArbNat

def Nat.arbitrary [Gen G] : G Nat := do
  pick
    (fun () => pure 0)
    (fun () => do
      let n ← Nat.arbitrary
      pure (n + 1))
partial_fixpoint

theorem Nat.arbitrary_support : n ∈ SPMF.support Nat.arbitrary := by
  induction n <;> rw [Nat.arbitrary] <;> simp [*]

-- TODO: Termination and efficiency

#guard_msgs(drop info) in
#eval (for _ in [0:20] do
  IO.println <| repr (← Nat.arbitrary) : IO Unit)

end ArbNat
