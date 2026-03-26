import Basalt.Gen
import Basalt.SPMF
import Basalt.SPMF.Cost

class IsSoundAndComplete (g : SPMF α) (P : α → Prop) where
  is_correct : a ∈ SPMF.support g ↔ P a

class IsAlmostSurelyTerminating (g : SPMF α) where
  is_ast : SPMF.IsPMF g

class IsCostBounded (g : SPMF.Cost α) (f : α → Nat) where
  is_cost_bounded : IsBounded g f

class LawfulGenerator (g : ∀ {G : Type → Type} [Gen G], G α) (P : α → Prop) (f : α → Nat) extends IsSoundAndComplete g P, IsAlmostSurelyTerminating g, IsCostBounded g f
