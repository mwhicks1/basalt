import Basalt

open RandomChoice

namespace NatListExample

def Nat.arbitrary [Gen G] : G Nat := do
  pick
    (fun () => pure 0)
    (fun () => do
      let n ← Nat.arbitrary
      pure (n + 1))
partial_fixpoint

theorem Nat.arbitrary_support : n ∈ SPMF.support Nat.arbitrary := by
  induction n <;> rw [Nat.arbitrary] <;> simp [*]

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

def List.genSorted [Gen G] (m : Nat) : G (List Nat) := do
  pick
    (fun () => pure [])
    (fun () => do
      let delta ← Nat.arbitrary
      let x := m + delta
      let xs ← List.genSorted x
      return x :: xs)
partial_fixpoint

def List.diverge [Gen G] : G (List Nat) := do
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

def List.unfold [Gen G] (coalg : β → G (ListF α β)) (b : β) : G (List α) := do
  match ← coalg b with
  | .nilStep => return []
  | .consStep x b' => return x :: (← List.unfold coalg b')
partial_fixpoint

def List.genSorted' [Gen G] (m : Nat) : G (List Nat) :=
  List.unfold (fun m =>
    pick
      (fun () => pure .nilStep)
      (fun () => do
        let delta ← Nat.arbitrary
        let x := m + delta
        return .consStep x x))
    m

#guard_msgs(drop info) in
#eval (for _ in [0:20] do
  IO.println <| repr (← List.arbitrary) : IO Unit)

end NatListExample
