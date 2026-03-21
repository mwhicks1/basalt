import Basalt
import Basalt.Examples.ArbNat

open RandomChoice ArbNat

namespace SortedList

def List.genSorted [Gen G] (m : Nat) : G (List Nat) := do
  pick
    (fun () => pure [])
    (fun () => do
      let delta ← Nat.arbitrary
      let x := m + delta
      let xs ← List.genSorted x
      return x :: xs)
partial_fixpoint

-- TODO: All theorems

end SortedList
