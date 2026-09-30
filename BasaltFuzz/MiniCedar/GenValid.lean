/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import BasaltFuzz.MiniCedar.Gen

/-!
# MiniCedar: a type-directed generator of well-typed expressions

`genTyped τ` generates expressions that `typeOf schema` assigns type `τ`, following the recipe of
`CedarLite.genExpr` (`BasaltFuzz/Cedar.lean`): each branch builds a term of the requested type from
subterms of types it chooses. Soundness is pinned against `typeOf` by `BasaltTest/MiniCedar.lean`,
not proved. Well-typed terms can still fail at runtime, and the generator produces the ingredients
for that on purpose: extreme integer literals, references to entities an environment may lack,
and record literals with repeated keys.
-/

namespace MiniCedar

open RandomChoice

/-- The types a subterm is drawn at when a branch is free to choose one (an `==` operand, a set
element). Sets of sets and records are left out to keep terms small. -/
abbrev elemTypes : List CType :=
  [.bool, .int, .string, .entity "User", .entity "Doc", .entity "Group"]

abbrev entityTypes : List String := ["User", "Doc", "Group"]

/-- Keys of generated record literals; few, so that keys repeat. -/
abbrev recordKeys : List String := ["a", "b", "c"]

/-- The attributes of type `τ` in `schema`, as (entity type, attribute). -/
def entityAttrsOfType (τ : CType) : List (String × String) :=
  schema.entityTypes.flatMap fun (ety, as) =>
    as.filterMap fun (a, τ') => if τ' == τ then some (ety, a) else none

/-- The context attributes of type `τ`. -/
def contextAttrsOfType (τ : CType) : List String :=
  schema.request.context.filterMap fun (a, τ') => if τ' == τ then some a else none

/-- The pool's entities of type `ety`. -/
def uidsOfType (ety : String) : List EntityUID :=
  (users ++ groups ++ docs ++ [actionView]).filter (·.ty == ety)

/-- A variable of entity type `ety`, if there is one. -/
def varOfType (ety : String) : Option Var :=
  if ety == schema.request.principal then some .principal
  else if ety == schema.request.resource then some .resource
  else if ety == schema.request.action.ty then some .action
  else none

def genElemType [Gen G] : G CType := elements elemTypes

/-- A literal or variable of entity type `ety`. -/
def genEntityLeaf [Gen G] (ety : String) : G Expr := do
  let lits := (uidsOfType ety).map (Expr.lit ∘ .entityUID)
  let leaves := lits ++ ((varOfType ety).map Expr.var).toList
  if h : leaves ≠ [] then elements leaves h else pure (.lit (.entityUID ⟨ety, "none"⟩))

/-- Leaf weight against each recursive branch's weight of `1`, keeping the branching subcritical. -/
private abbrev leafW : Nat := 8

mutual
/-- A well-typed expression of type `τ`. -/
def genTyped [Gen G] (τ : CType) : G Expr :=
  frequency! [
    (leafW, fun _ => genLeaf τ),
    (1, fun _ => do return .ite (← genTyped .bool) (← genTyped τ) (← genTyped τ)),
    (1, fun _ => genAccess τ),
    (2, fun _ => genOp τ)
  ] (by simp)
partial_fixpoint

/-- A term of type `τ` with no recursive structure beyond what the type itself demands. -/
def genLeaf [Gen G] (τ : CType) : G Expr :=
  match τ with
  | .bool => (Expr.lit ∘ .bool) <$> genBool
  | .int => (Expr.lit ∘ .int) <$> genInt64
  | .string => (Expr.lit ∘ .string) <$> genString
  | .entity ety => genEntityLeaf ety
  | .set τ' => do
    let n ← chooseNat 1 3
    return .set (← vectorOf n (genLeaf τ'))
  | .record fs =>
    if fs == schema.request.context then pure (.var .context)
    else do return .record (← genFields fs)
partial_fixpoint

/-- A record literal's fields at the given types. -/
def genFields [Gen G] (fs : List (String × CType)) : G (List (String × Expr)) :=
  match fs with
  | [] => pure []
  | (a, τ) :: rest => do
    let e ← genTyped τ
    let es ← genFields rest
    return (a, e) :: es
partial_fixpoint

/-- A field of a record literal at an arbitrary element type. -/
def genAnyField [Gen G] : G (String × Expr) := do
  let k ← elements recordKeys
  let τ ← genElemType
  return (k, ← genTyped τ)
partial_fixpoint

/-- An attribute access of type `τ`: of an entity, of the context, or of a record literal. The
literal puts the accessed field first among those with its key, which is the one `Map.make` keeps,
and may repeat the key later and add unrelated fields that fail at runtime. -/
def genAccess [Gen G] (τ : CType) : G Expr := do
  match ← chooseNat 0 2 with
  | 0 =>
    if h : entityAttrsOfType τ ≠ [] then do
      let (ety, a) ← elements (entityAttrsOfType τ) h
      return .getAttr (← genTyped (.entity ety)) a
    else genRecordAccess τ
  | 1 =>
    if h : contextAttrsOfType τ ≠ [] then do
      let a ← elements (contextAttrsOfType τ) h
      return .getAttr (← genTyped (.record schema.request.context)) a
    else genRecordAccess τ
  | _ => genRecordAccess τ
partial_fixpoint

def genRecordAccess [Gen G] (τ : CType) : G Expr := do
  let k ← elements recordKeys
  let pre ← listOfMaxLength 2 genAnyField
  let e ← genTyped τ
  let post ← listOfMaxLength 2 genAnyField
  return .getAttr (.record (pre.filter (·.1 != k) ++ [(k, e)] ++ post)) k
partial_fixpoint

/-- The operators whose result has type `τ`; a type with none falls back to a leaf. -/
def genOp [Gen G] (τ : CType) : G Expr :=
  match τ with
  | .bool =>
    frequency! [
      (2, fun _ => do return .and (← genTyped .bool) (← genTyped .bool)),
      (2, fun _ => do return .or (← genTyped .bool) (← genTyped .bool)),
      (1, fun _ => do return .unaryApp .not (← genTyped .bool)),
      (1, fun _ => do return .binaryApp .less (← genTyped .int) (← genTyped .int)),
      (1, fun _ => do return .binaryApp .lessEq (← genTyped .int) (← genTyped .int)),
      (2, fun _ => do
        let τ' ← genElemType
        return .binaryApp .eq (← genTyped τ') (← genTyped τ')),
      (1, fun _ => do
        let e₁ ← elements entityTypes
        let e₂ ← elements entityTypes
        return .binaryApp .eq (← genTyped (.entity e₁)) (← genTyped (.entity e₂))),
      (1, fun _ => do
        let τ' ← genElemType
        return .binaryApp .contains (← genTyped (.set τ')) (← genTyped τ')),
      (1, fun _ => do
        let τ' ← genElemType
        return .binaryApp .containsAll (← genTyped (.set τ')) (← genTyped (.set τ'))),
      (1, fun _ => do
        let τ' ← genElemType
        return .binaryApp .containsAny (← genTyped (.set τ')) (← genTyped (.set τ'))),
      (1, fun _ => do
        let e₁ ← elements entityTypes
        let e₂ ← elements entityTypes
        return .binaryApp .mem (← genTyped (.entity e₁)) (← genTyped (.entity e₂))),
      (1, fun _ => do
        let e₁ ← elements entityTypes
        let e₂ ← elements entityTypes
        return .binaryApp .mem (← genTyped (.entity e₁)) (← genTyped (.set (.entity e₂)))),
      (1, fun _ => do
        let e₁ ← elements entityTypes
        return .unaryApp (.is (← elements entityTypeNames)) (← genTyped (.entity e₁))),
      (1, fun _ => do
        let τ' ← genElemType
        return .unaryApp .isEmpty (← genTyped (.set τ'))),
      (1, fun _ => do
        let e₁ ← elements entityTypes
        return .hasAttr (← genTyped (.entity e₁)) (← elements attrNames))
    ] (by simp)
  | .int =>
    frequency! [
      (1, fun _ => do return .unaryApp .neg (← genTyped .int)),
      (1, fun _ => do return .binaryApp .add (← genTyped .int) (← genTyped .int)),
      (1, fun _ => do return .binaryApp .sub (← genTyped .int) (← genTyped .int)),
      (1, fun _ => do return .binaryApp .mul (← genTyped .int) (← genTyped .int))
    ] (by simp)
  | .set τ' => do
    let n ← chooseNat 1 3
    return .set (← vectorOf n (genTyped τ'))
  | .record fs => do return .record (← genFields fs)
  | τ => genLeaf τ
partial_fixpoint
end

/-- A well-typed boolean expression: the shape of a policy condition. -/
def genValidExpr [Gen G] : G Expr := genTyped .bool

end MiniCedar
