/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.RandomChoice

/-!
# Generator Typeclass

`Gen` collects everything a generator monad needs: a monad, a random choice operator, and the
order-theoretic structure that lets it represent potentially non-terminating computations (via
`partial_fixpoint`).
-/

open Lean.Order

/-- `RandomChoice.span` is monotone: `partial_fixpoint` asks it of anything a recursive call sits
under. Every interpretation that leaves `span` the identity has it by `MonoSpan.ofId`. -/
class MonoSpan (g : Type u → Type v) [RandomChoice g] [∀ α, CCPO (g α)] : Prop where
  monotone_span : ∀ {α : Type u} (l : UInt64), monotone (RandomChoice.span (m := g) (α := α) l)

/-- `MonoSpan` for an interpretation whose `span` is the identity. -/
theorem MonoSpan.ofId {g : Type u → Type v} [RandomChoice g] [∀ α, CCPO (g α)]
    (h : ∀ {α : Type u} (l : UInt64) (x : g α), RandomChoice.span l x = x) : MonoSpan g where
  monotone_span l := by
    intro x y hxy
    rw [h, h]
    exact hxy

/-- A type constructor `g` is a `Gen` if it has all of the operations necessary for (potentially
diverging) random monadic programming. -/
class Gen (g : Type u → Type v) where
  instInhabited : ∀ α, Inhabited (g α)
  instMonad : Monad g
  instRandomChoice : RandomChoice g
  instCCPO : ∀ α, CCPO (g α)
  instMonoBind : MonoBind g
  instMonoSpan : MonoSpan g

instance [m : Gen g] : ∀ α, Inhabited (g α) := m.instInhabited
instance [m : Gen g] : Monad g := m.instMonad
instance [m : Gen g] : RandomChoice g := m.instRandomChoice
instance [m : Gen g] : ∀ α, CCPO (g α) := m.instCCPO
instance [m : Gen g] : MonoBind g := m.instMonoBind
instance [m : Gen g] : MonoSpan g := m.instMonoSpan

instance
    [∀ α, Inhabited (g α)]
    [Monad g]
    [RandomChoice g]
    [∀ α, CCPO (g α)]
    [MonoBind g]
    [MonoSpan g] : Gen g where
  instInhabited := inferInstance
  instMonad := inferInstance
  instRandomChoice := inferInstance
  instCCPO := inferInstance
  instMonoBind := inferInstance
  instMonoSpan := inferInstance

/-- `span` sits over recursive calls: monotone in what it wraps. -/
@[partial_fixpoint_monotone]
theorem monotone_span [Gen g] {α : Type u} {γ : Sort w} [PartialOrder γ] (l : UInt64)
    (f : γ → g α) (hf : monotone f) : monotone (fun x => RandomChoice.span l (f x)) :=
  monotone_compose hf (MonoSpan.monotone_span l)
