/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/

/-!
# MiniCedar: syntax, values, and the data the evaluator reads

An *untyped* fragment of `Cedar.Spec` (`cedar-lean/Cedar/Spec/{Expr,Value,Entities,Request}.lean`)
large enough that ill-typed terms evaluate somewhere interesting: sets, records, entities, and
`Int64` arithmetic. Sets and records are lists kept in Cedar's canonical form (`Set.make`,
`Map.make`), which is what makes `Value` equality structural.
-/

namespace MiniCedar

/-! ## Values -/

/-- As `Cedar.Spec.EntityUID`, with the type name flattened to a string. -/
structure EntityUID where
  ty : String
  eid : String
  deriving DecidableEq, Repr, Inhabited, Hashable

def EntityUID.lt (a b : EntityUID) : Bool :=
  decide (a.ty < b.ty) || (a.ty == b.ty && decide (a.eid < b.eid))

/-- As `Cedar.Spec.Prim`. -/
inductive Prim where
  | bool (b : Bool)
  | int (i : Int64)
  | string (s : String)
  | entityUID (uid : EntityUID)
  deriving DecidableEq, Repr, Inhabited

/-- As `Cedar.Spec.Prim.lt`: within a constructor by value, across constructors by declaration
order. -/
def Prim.lt : Prim → Prim → Bool
  | .bool b₁, .bool b₂ => !b₁ && b₂
  | .int i₁, .int i₂ => decide (i₁ < i₂)
  | .string s₁, .string s₂ => decide (s₁ < s₂)
  | .entityUID u₁, .entityUID u₂ => u₁.lt u₂
  | .bool _, .int _ | .bool _, .string _ | .bool _, .entityUID _ => true
  | .int _, .string _ | .int _, .entityUID _ => true
  | .string _, .entityUID _ => true
  | _, _ => false

/-- As `Cedar.Spec.Value`, without extension values. A `set` is sorted by `Value.lt` without
duplicates and a `record` is sorted by key without duplicates; the evaluator builds both through
`Set.make`/`Map.make`, and every other constructor of them must too. -/
inductive Value where
  | prim (p : Prim)
  | set (vs : List Value)
  | record (fields : List (String × Value))
  deriving BEq, Repr, Inhabited

mutual
/-- As `Cedar.Spec.Value.lt`. -/
def Value.lt : Value → Value → Bool
  | .prim p₁, .prim p₂ => p₁.lt p₂
  | .set vs₁, .set vs₂ => Values.lt vs₁ vs₂
  | .record fs₁, .record fs₂ => Fields.lt fs₁ fs₂
  | .prim _, _ => true
  | .set _, .record _ => true
  | _, _ => false

def Values.lt : List Value → List Value → Bool
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | v₁ :: vs₁, v₂ :: vs₂ => Value.lt v₁ v₂ || (v₁ == v₂ && Values.lt vs₁ vs₂)

def Fields.lt : List (String × Value) → List (String × Value) → Bool
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | (a₁, v₁) :: fs₁, (a₂, v₂) :: fs₂ =>
    decide (a₁ < a₂) || (a₁ == a₂ && Value.lt v₁ v₂) || (a₁ == a₂ && v₁ == v₂ && Fields.lt fs₁ fs₂)
end

/-! ## Canonical sets and maps (as `Cedar.Data.List.canonicalize`) -/

/-- As `Cedar.Data.List.insertCanonical`: an element whose key equals an existing one *replaces*
it. -/
def insertCanonical (lt : β → β → Bool) (f : α → β) (x : α) : List α → List α
  | [] => [x]
  | hd :: tl =>
    if lt (f x) (f hd) then x :: hd :: tl
    else if lt (f hd) (f x) then hd :: insertCanonical lt f x tl
    else x :: tl

/-- As `Cedar.Data.List.canonicalize`. It inserts right to left, so of two equal keys the *first*
in the input survives. -/
def canonicalize (lt : β → β → Bool) (f : α → β) : List α → List α
  | [] => []
  | hd :: tl => insertCanonical lt f hd (canonicalize lt f tl)

/-- As `Cedar.Data.Set.make`. -/
def Set.make (vs : List Value) : List Value := canonicalize Value.lt id vs

/-- As `Cedar.Data.Map.make`. -/
def Map.make (kvs : List (String × β)) : List (String × β) :=
  canonicalize (fun a b => decide (a < b)) Prod.fst kvs

/-- As `Cedar.Data.Map.find?`. -/
def Map.find? (m : List (String × β)) (k : String) : Option β :=
  (m.find? (·.1 == k)).map (·.2)

/-! ## Errors and results -/

/-- As `Cedar.Spec.Error`, without the tag and extension errors this fragment cannot raise. -/
inductive Error where
  | entityDoesNotExist
  | attrDoesNotExist
  | typeError
  | arithBoundsError
  deriving DecidableEq, Repr, Inhabited

/-- As `Cedar.Spec.Result`. -/
abbrev Result (α) := Except Error α

instance [BEq α] : BEq (Result α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

/-! ## Expressions (as `Cedar.Spec.Expr`) -/

inductive Var where
  | principal
  | action
  | resource
  | context
  deriving DecidableEq, Repr, Inhabited

inductive UnaryOp where
  | not
  | neg
  | isEmpty
  | is (ety : String)
  deriving DecidableEq, Repr, Inhabited

inductive BinaryOp where
  | eq
  | less
  | lessEq
  | add
  | sub
  | mul
  | contains
  | containsAll
  | containsAny
  | mem
  deriving DecidableEq, Repr, Inhabited

/-- As `Cedar.Spec.Expr`, without `like`, tags, `extHasAttr`, and extension calls. -/
inductive Expr where
  | lit (p : Prim)
  | var (v : Var)
  | ite (cond thenExpr elseExpr : Expr)
  | and (a b : Expr)
  | or (a b : Expr)
  | unaryApp (op : UnaryOp) (e : Expr)
  | binaryApp (op : BinaryOp) (a b : Expr)
  | hasAttr (e : Expr) (attr : String)
  | getAttr (e : Expr) (attr : String)
  | set (xs : List Expr)
  | record (fields : List (String × Expr))
  deriving BEq, Repr, Inhabited

mutual
/-- The number of nodes. -/
def Expr.size : Expr → Nat
  | .lit _ | .var _ => 1
  | .ite c t e => 1 + c.size + t.size + e.size
  | .and a b | .or a b | .binaryApp _ a b => 1 + a.size + b.size
  | .unaryApp _ e | .hasAttr e _ | .getAttr e _ => 1 + e.size
  | .set xs => 1 + Expr.sizeList xs
  | .record fs => 1 + Expr.sizeFields fs

def Expr.sizeList : List Expr → Nat
  | [] => 0
  | x :: xs => x.size + Expr.sizeList xs

def Expr.sizeFields : List (String × Expr) → Nat
  | [] => 0
  | (_, x) :: fs => x.size + Expr.sizeFields fs
end

/-! ## Requests and entities -/

/-- As `Cedar.Spec.EntityData`, without tags. -/
structure EntityData where
  attrs : List (String × Value)
  ancestors : List EntityUID
  deriving BEq, Repr, Inhabited

/-- As `Cedar.Spec.Entities`. Ancestor lists are transitively closed, as Cedar's are. -/
abbrev Entities := List (EntityUID × EntityData)

def Entities.find? (es : Entities) (uid : EntityUID) : Option EntityData :=
  (List.find? (·.1 == uid) es).map (·.2)

/-- As `Cedar.Spec.Entities.attrs`. -/
def Entities.attrs (es : Entities) (uid : EntityUID) : Result (List (String × Value)) :=
  match es.find? uid with
  | some d => .ok d.attrs
  | none => .error .entityDoesNotExist

def Entities.attrsOrEmpty (es : Entities) (uid : EntityUID) : List (String × Value) :=
  (es.find? uid).elim [] (·.attrs)

def Entities.ancestorsOrEmpty (es : Entities) (uid : EntityUID) : List EntityUID :=
  (es.find? uid).elim [] (·.ancestors)

/-- As `Cedar.Spec.Request`. -/
structure Request where
  principal : EntityUID
  action : EntityUID
  resource : EntityUID
  context : List (String × Value)
  deriving BEq, Repr, Inhabited

end MiniCedar
