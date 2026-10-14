/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.RandomChoice

/-!
# Observations

An `Obs G W` is a `choose`-preserving monad morphism from a generator monad `G` into a specification
monad `W`.
-/

open RandomChoice

/-- A `choose`-preserving monad morphism. -/
structure Obs (G : Type u → Type v) (W : Type u → Type w)
    [Monad G] [RandomChoice G] [Monad W] [RandomChoice W] where
  spec : ∀ {α}, G α → W α
  map_pure : ∀ {α} (a : α), spec (Pure.pure a) = Pure.pure a
  map_bind : ∀ {α β} (x : G α) (k : α → G β), spec (x >>= k) = spec x >>= fun a => spec (k a)
  map_choose : ∀ lo hi h, spec (choose lo hi h) = choose lo hi h
  /-- An observed monad does not tell draws' kinds apart (`RandomChoice.chooseAs`)… -/
  chooseAs_gen : ∀ k lo hi h, (chooseAs k lo hi h : G _) = choose lo hi h := by intros; rfl
  /-- …and nor does the specification monad. -/
  chooseAs_spec : ∀ k lo hi h, (chooseAs k lo hi h : W _) = choose lo hi h := by intros; rfl

namespace Obs

variable {G : Type u → Type v} {W : Type u → Type w}
  [Monad G] [RandomChoice G] [Monad W] [RandomChoice W] (O : Obs G W)

/-- An observation forgets what a draw is for. -/
theorem map_chooseAs (k : ChoiceKind) (lo hi : Nat) (h : lo ≤ hi) :
    O.spec (chooseAs k lo hi h) = choose lo hi h := by
  rw [O.chooseAs_gen, O.map_choose]

theorem map_ite (p : Prop) [Decidable p] (x y : G α) :
    O.spec (if p then x else y) = if p then O.spec x else O.spec y := by
  split <;> rfl

theorem map_map [LawfulMonad G] [LawfulMonad W] (f : α → β) (x : G α) :
    O.spec (f <$> x) = f <$> O.spec x := by
  rw [← bind_pure_comp, O.map_bind, ← bind_pure_comp]
  simp only [O.map_pure]

theorem map_coin {G : Type → Type v} {W : Type → Type w}
    [Monad G] [RandomChoice G] [Monad W] [RandomChoice W] (O : Obs G W) (r : Rat) :
    O.spec (coin r) = coin r := by
  simp only [coin, O.map_bind, O.map_chooseAs, O.map_ite, O.map_pure, O.chooseAs_spec]

end Obs
