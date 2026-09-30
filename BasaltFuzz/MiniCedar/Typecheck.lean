/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import BasaltFuzz.MiniCedar.Syntax

/-!
# MiniCedar: schemas and the typechecker

A simplified `Cedar.Validation.typeOf` (`cedar-lean/Cedar/Validation/Typechecker.lean`): every
attribute is required, so there are no capabilities, and there are no singleton boolean types. Its
contract, which `prop_typecheck_sound` tests, is Cedar's: a well-typed expression evaluated against
a conforming request and entities raises neither `typeError` nor `attrDoesNotExist`.
-/

namespace MiniCedar

inductive CType where
  | bool
  | int
  | string
  | entity (ty : String)
  | set (τ : CType)
  | record (fields : List (String × CType))
  deriving BEq, Repr, Inhabited

/-- One request shape (Cedar allows one per action). -/
structure RequestType where
  principal : String
  action : EntityUID
  resource : String
  context : List (String × CType)
  deriving Repr, Inhabited

/-- Entity types and their attributes, and the request shape. The action's type has no attributes
and need not be listed. -/
structure Schema where
  entityTypes : List (String × List (String × CType))
  request : RequestType
  deriving Repr, Inhabited

def Schema.attrsOf? (s : Schema) (ety : String) : Option (List (String × CType)) :=
  (s.entityTypes.find? (·.1 == ety)).map (·.2) <|>
    if ety == s.request.action.ty then some [] else none

def CType.isEntity : CType → Bool
  | .entity _ => true
  | _ => false

/-- The operands of `==`, `contains` and friends must agree; two entity types always do, as in
Cedar, where `principal == resource` is well typed (at `False`) across entity types. -/
def CType.compatible (τ₁ τ₂ : CType) : Bool :=
  τ₁ == τ₂ || (τ₁.isEntity && τ₂.isEntity)

def typeOfPrim (s : Schema) : Prim → Option CType
  | .bool _ => some .bool
  | .int _ => some .int
  | .string _ => some .string
  | .entityUID uid => (s.attrsOf? uid.ty).map fun _ => .entity uid.ty

def typeOfUnary : UnaryOp → CType → Option CType
  | .not, .bool => some .bool
  | .neg, .int => some .int
  | .isEmpty, .set _ => some .bool
  | .is _, .entity _ => some .bool
  | _, _ => none

def typeOfBinary : BinaryOp → CType → CType → Option CType
  | .eq, τ₁, τ₂ => if τ₁.compatible τ₂ then some .bool else none
  | .less, .int, .int | .lessEq, .int, .int => some .bool
  | .add, .int, .int | .sub, .int, .int | .mul, .int, .int => some .int
  | .contains, .set τ₁, τ₂ => if τ₁.compatible τ₂ then some .bool else none
  | .containsAll, .set τ₁, .set τ₂ | .containsAny, .set τ₁, .set τ₂ =>
    if τ₁.compatible τ₂ then some .bool else none
  | .mem, .entity _, .entity _ => some .bool
  | .mem, .entity _, .set (.entity _) => some .bool
  | _, _, _ => none

mutual
def typeOf (s : Schema) : Expr → Option CType
  | .lit p => typeOfPrim s p
  | .var .principal => some (.entity s.request.principal)
  | .var .action => some (.entity s.request.action.ty)
  | .var .resource => some (.entity s.request.resource)
  | .var .context => some (.record s.request.context)
  | .ite c t e => do
    guard ((← typeOf s c) == .bool)
    let τ ← typeOf s t
    guard ((← typeOf s e) == τ)
    pure τ
  | .and a b | .or a b => do
    guard ((← typeOf s a) == .bool)
    guard ((← typeOf s b) == .bool)
    pure .bool
  | .unaryApp op e => do typeOfUnary op (← typeOf s e)
  | .binaryApp op a b => do typeOfBinary op (← typeOf s a) (← typeOf s b)
  | .hasAttr e _ => do
    match ← typeOf s e with
    | .entity _ | .record _ => pure .bool
    | _ => none
  | .getAttr e a => do
    match ← typeOf s e with
    | .entity ety => Map.find? (← s.attrsOf? ety) a
    | .record fs => Map.find? fs a
    | _ => none
  | .set xs => do
    match ← typeOfList s xs with
    | [] => none
    | τ :: τs => if τs.all (· == τ) then pure (.set τ) else none
  | .record fs => do pure (.record (Map.make (← typeOfFields s fs)))

def typeOfList (s : Schema) : List Expr → Option (List CType)
  | [] => some []
  | x :: xs => do pure ((← typeOf s x) :: (← typeOfList s xs))

def typeOfFields (s : Schema) : List (String × Expr) → Option (List (String × CType))
  | [] => some []
  | (a, x) :: fs => do pure ((a, ← typeOf s x) :: (← typeOfFields s fs))
end

/-! ## Conformance of runtime data to a schema -/

mutual
def Value.hasType (s : Schema) : Value → CType → Bool
  | .prim p, τ => typeOfPrim s p == some τ
  | .set vs, .set τ => Value.allHaveType s vs τ
  | .record fs, .record τs => Value.fieldsHaveTypes s fs (Map.make τs)
  | _, _ => false

def Value.allHaveType (s : Schema) : List Value → CType → Bool
  | [], _ => true
  | v :: vs, τ => Value.hasType s v τ && Value.allHaveType s vs τ

/-- Exactly the declared fields, in order: both lists are canonical (the caller makes the type's). -/
def Value.fieldsHaveTypes (s : Schema) : List (String × Value) → List (String × CType) → Bool
  | [], [] => true
  | (a, v) :: fs, (b, τ) :: τs => a == b && Value.hasType s v τ && Value.fieldsHaveTypes s fs τs
  | _, _ => false
end

def Request.conforms (s : Schema) (r : Request) : Bool :=
  r.principal.ty == s.request.principal && r.action == s.request.action &&
    r.resource.ty == s.request.resource &&
    Value.hasType s (.record r.context) (.record s.request.context)

/-- Every entity has a declared type and exactly its declared attributes. Ancestors are not
checked: Cedar's schema would constrain their types, and nothing here depends on it. -/
def Entities.conform (s : Schema) (es : Entities) : Bool :=
  es.all fun (uid, d) =>
    match s.attrsOf? uid.ty with
    | some τs => Value.hasType s (.record d.attrs) (.record τs)
    | none => false

end MiniCedar
