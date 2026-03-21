import Basalt
import Basalt.Examples.ArbNat

open RandomChoice ArbNat

namespace ArbList

def List.arbitrary [Gen G] : G (List Nat) := do
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

-- TODO: Termination and efficiency

#guard_msgs(drop info) in
#eval (for _ in [0:20] do
  IO.println <| repr (← List.arbitrary) : IO Unit)

end ArbList
