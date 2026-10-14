/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
/-!
# Abstracting Over Random Choices

This file defines a type class and associated operations for random choices.
-/

/-- What a draw is for, as a choice-sequence fuzzer sees it. Semantically every kind is `choose`. -/
inductive ChoiceKind where
  | nat | int | index | branch | bool | more | length
  deriving Inhabited, DecidableEq, Repr

class RandomChoice (m : Type u → Type v) where
  /-- An inclusive choice over a nonempty range of natural numbers. -/
  choose : (lo hi : Nat) → (h : lo ≤ hi) → m (ULift {x : Nat // lo ≤ x ∧ x ≤ hi})
  /-- `choose`, tagged with what the draw is for. Only a choice-sequence fuzzer overrides it; an
  observation sends it to `choose` (`Obs.map_chooseAs`). -/
  chooseAs : ChoiceKind → (lo hi : Nat) → (h : lo ≤ hi) → m (ULift {x : Nat // lo ≤ x ∧ x ≤ hi}) :=
    fun _ => choose

/-- A weighted binary choice. -/
def RandomChoice.coin [Monad m] [RandomChoice m] (r : Rat) : m Bool := do
  if (ULift.down (← chooseAs .bool 0 (r.den - 1) (by simp))).val < r.num then pure true
  else pure false
