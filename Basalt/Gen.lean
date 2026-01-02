import Basalt.RandomChoice

open Lean.Order

def Gen (α : Type) :=
  ∀ {m : Type → Type}
    [∀ α, Inhabited (m α)]
    [Monad m]
    [RandomChoice m]
    [∀ α, CCPO (m α)]
    [MonoBind m],
    m α
