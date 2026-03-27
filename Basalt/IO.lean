/-
Copyright (c) 2025 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.RandomChoice
import Basalt.Gen

open RandomChoice

/-!
# IO Interpretation

<TODO: summarize>

## Main Definitions

- `RandomChoice IO` — <fill in>

## Main Theorems

- <fill in>
-/

/-- `IO` interpretation of `RandomChoice` using `IO.rand`. -/
instance : RandomChoice IO where
  choose lo hi _ := IO.rand lo hi
