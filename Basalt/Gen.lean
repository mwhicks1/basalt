/-
Copyright (c) 2025 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.RandomChoice

open Lean.Order

/-!
# Generator Typeclass

<TODO: summarize>

## Main Definitions

- `Gen` — <fill in>

## Main Theorems

- <fill in>
-/

/-- TODO: document -/
class Gen (g : Type → Type) where
  instInhabited : ∀ α, Inhabited (g α)
  instMonad : Monad g
  instRandomChoice : RandomChoice g
  instCCPO : ∀ α, CCPO (g α)
  instMonoBind : MonoBind g

instance [m : Gen g] : ∀ α, Inhabited (g α) := m.instInhabited
instance [m : Gen g] : Monad g := m.instMonad
instance [m : Gen g] : RandomChoice g := m.instRandomChoice
instance [m : Gen g] : ∀ α, CCPO (g α) := m.instCCPO
instance [m : Gen g] : MonoBind g := m.instMonoBind

instance
    [∀ α, Inhabited (g α)]
    [Monad g]
    [RandomChoice g]
    [∀ α, CCPO (g α)]
    [MonoBind g] : Gen g where
  instInhabited := inferInstance
  instMonad := inferInstance
  instRandomChoice := inferInstance
  instCCPO := inferInstance
  instMonoBind := inferInstance
