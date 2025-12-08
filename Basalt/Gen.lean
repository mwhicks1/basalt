import Basalt.RandomChoice

open Lean.Order

def Gen (α : Type) :=
  ∀ {m : Type → Type}
    [∀ α, Inhabited (m α)]
    [∀ α, CCPO (m α)]
    [Monad m]
    [MonoBind m]
    [RandomChoice m],
    m α
