/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Basalt.PBT.Property
import BasaltFuzz.MiniCedar.Gen
import BasaltFuzz.MiniCedar.Optimize

/-!
# MiniCedar: properties

Each property takes the expression generator as an argument, so one statement is run against every
generation strategy; the environment always comes from `genEntities`/`genRequest`.
-/

namespace MiniCedar

open Basalt.PBT

/-- The optimizer's contract: the optimized expression evaluates to the same value, or fails with
the same error. No precondition — it must hold for ill-typed expressions too. -/
def prop_optimize_sound [Gen G] (rules : List Rule) (genE : G Expr) : PropM G Unit := do
  let es ← generate genEntities
  let req ← generate genRequest
  let e ← generate genE
  let e' := optimize rules e
  let want := evaluate req es e
  let got := evaluate req es e'
  check (got == want)
    s!"typed={(typeOf schema e).isSome}\n  e={reprStr e}\n  optimized={reprStr e'}\n  \
       want={reprStr want}\n  got={reprStr got}\n  req={reprStr req}\n  es={reprStr es}"

/-- The typechecker's contract: a well-typed expression raises neither `typeError` nor
`attrDoesNotExist` against a conforming environment. -/
def prop_typecheck_sound [Gen G] (genE : G Expr) : PropM G Unit := do
  let es ← generate genEntities
  let req ← generate genRequest
  let e ← generate genE
  assume (typeOf schema e).isSome
  let r := evaluate req es e
  check (r != .error .typeError && r != .error .attrDoesNotExist)
    s!"e={reprStr e}\n  result={reprStr r}\n  req={reprStr req}\n  es={reprStr es}"

/-- The optimizer preserves typing: a well-typed expression optimizes to one of the same type. -/
def prop_optimize_preserves_type [Gen G] (rules : List Rule) (genE : G Expr) : PropM G Unit := do
  let e ← generate genE
  let τ? := typeOf schema e
  assume τ?.isSome
  let e' := optimize rules e
  check (typeOf schema e' == τ?) s!"e={reprStr e}\n  optimized={reprStr e'}"

end MiniCedar
