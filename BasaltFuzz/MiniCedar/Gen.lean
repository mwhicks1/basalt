/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Basalt.Combinators
import BasaltFuzz.MiniCedar.Typecheck

/-!
# MiniCedar: a fixed schema, its environments, and an unconstrained expression generator

The environment generators produce requests and entities that conform to `schema`, with some of
the pool's entities absent so that `entityDoesNotExist` is reachable. `genAnyExpr` has every
`Expr` in its support and knows nothing of types: it is the baseline the guided generators are
compared against.
-/

namespace MiniCedar

open RandomChoice

/-! ## The schema and the entity pool -/

def actionView : EntityUID := ⟨"Action", "view"⟩

def schema : Schema where
  entityTypes := [
    ("User", [("age", .int), ("name", .string), ("manager", .entity "User")]),
    ("Group", []),
    ("Doc", [("owner", .entity "User"), ("public", .bool), ("level", .int),
             ("tags", .set .string)])]
  request := {
    principal := "User", action := actionView, resource := "Doc",
    context := [("authenticated", .bool), ("count", .int)] }

abbrev users : List EntityUID := [⟨"User", "alice"⟩, ⟨"User", "bob"⟩, ⟨"User", "carol"⟩]
abbrev groups : List EntityUID := [⟨"Group", "admins"⟩, ⟨"Group", "staff"⟩]
abbrev docs : List EntityUID := [⟨"Doc", "d1"⟩, ⟨"Doc", "d2"⟩]

/-- Attribute names the unconstrained generator draws from: the schema's, and one it lacks. -/
abbrev attrNames : List String :=
  ["age", "name", "manager", "owner", "public", "level", "tags", "authenticated", "count", "bogus"]

abbrev entityTypeNames : List String := ["User", "Group", "Doc", "Action", "Nope"]

abbrev strings : List String := ["", "alice", "admin", "x"]

/-! ## Primitive values -/

/-- Mostly small, sometimes an extreme: the `Int64` boundary is where arithmetic errors live. -/
def genInt64 [Gen G] : G Int64 :=
  frequency! [
    (6, fun _ => Int64.ofInt <$> chooseInt (-3) 3),
    (1, fun _ => elements [Int64.minValue, Int64.maxValue, Int64.minValue + 1, Int64.maxValue - 1])
  ] (by simp)

def genBool [Gen G] : G Bool := elements [true, false]

def genString [Gen G] : G String := elements strings

def genUid [Gen G] : G EntityUID := elements (users ++ groups ++ docs ++ [actionView])

def genPrim [Gen G] : G Prim :=
  oneOf! [
    fun _ => .bool <$> genBool,
    fun _ => .int <$> genInt64,
    fun _ => .string <$> genString,
    fun _ => .entityUID <$> genUid
  ]

/-! ## Environments conforming to `schema` -/

/-- A value of the given schema attribute type. -/
def genAttrValue [Gen G] : CType → G Value
  | .bool => (.prim ∘ .bool) <$> genBool
  | .int => (.prim ∘ .int) <$> genInt64
  | .string => (.prim ∘ .string) <$> genString
  | .entity "User" => (.prim ∘ .entityUID) <$> elements users
  | .entity "Doc" => (.prim ∘ .entityUID) <$> elements docs
  | .entity _ => (.prim ∘ .entityUID) <$> elements groups
  | .set .string => (fun ss => .set (Set.make (ss.map (.prim ∘ .string)))) <$>
      listOfMaxLength 3 genString
  | _ => pure (.set [])

def genAttrs [Gen G] : List (String × CType) → G (List (String × Value))
  | [] => pure []
  | (a, τ) :: τs => do
    let v ← genAttrValue τ
    let vs ← genAttrs τs
    pure ((a, v) :: vs)

/-- Each pool entity is present with probability 3/4, with conforming attributes; users are in a
random subset of the groups, which have no parents, so every ancestor list is closed. -/
def genEntities [Gen G] : G Entities := do
  let mut es : Entities := []
  for uid in users ++ groups ++ docs do
    let present ← chooseNat 0 3
    if present == 0 then continue
    let τs := ((schema.attrsOf? uid.ty).getD [])
    let attrs ← genAttrs τs
    let ancestors ← if uid.ty == "User" then groups.filterM fun _ => genBool else pure []
    es := es ++ [(uid, { attrs := Map.make attrs, ancestors })]
  return es

def genRequest [Gen G] : G Request := do
  let principal ← elements users
  let resource ← elements docs
  let context ← genAttrs schema.request.context
  return { principal, action := actionView, resource, context := Map.make context }

/-! ## The unconstrained generator -/

def genVar [Gen G] : G Var := elements [.principal, .action, .resource, .context]

def genUnaryOp [Gen G] : G UnaryOp :=
  oneOf! [
    fun _ => pure .not, fun _ => pure .neg, fun _ => pure .isEmpty,
    fun _ => .is <$> elements entityTypeNames
  ]

def genBinaryOp [Gen G] : G BinaryOp :=
  elements [.eq, .less, .lessEq, .add, .sub, .mul, .contains, .containsAll, .containsAny, .mem]

def genAttrName [Gen G] : G String := elements attrNames

/-- Every `Expr` over the pools, with leaves weighted so the branching process is subcritical. -/
def genAnyExpr [Gen G] : G Expr :=
  frequency! [
    (6, fun _ => .lit <$> genPrim),
    (3, fun _ => .var <$> genVar),
    (1, fun _ => do return .ite (← genAnyExpr) (← genAnyExpr) (← genAnyExpr)),
    (1, fun _ => do return .and (← genAnyExpr) (← genAnyExpr)),
    (1, fun _ => do return .or (← genAnyExpr) (← genAnyExpr)),
    (1, fun _ => do return .unaryApp (← genUnaryOp) (← genAnyExpr)),
    (2, fun _ => do return .binaryApp (← genBinaryOp) (← genAnyExpr) (← genAnyExpr)),
    (1, fun _ => do return .hasAttr (← genAnyExpr) (← genAttrName)),
    (1, fun _ => do return .getAttr (← genAnyExpr) (← genAttrName)),
    (1, fun _ => do return .set (← listOfMaxLength 3 genAnyExpr)),
    (1, fun _ => do
      return .record (← listOfMaxLength 3 (do return ((← genAttrName), (← genAnyExpr)))))
  ] (by simp)
partial_fixpoint

end MiniCedar
