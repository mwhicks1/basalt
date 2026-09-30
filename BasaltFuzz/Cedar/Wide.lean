/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import BasaltFuzz.Cedar.Typed

/-!
# A wide generator for Cedar's typing judgment

`CedarTyped` restricted to a fragment so it could be proved complete; this module widens it to most
of Cedar's expression language — entity and action literals, `in` over an entity hierarchy, tags,
sets and the set operators, record literals, `like`, the multi-attribute `has`, and the extension
functions — over a schema with a two-level hierarchy on each side of the request. It keeps
`CedarTyped`'s architecture (a branch per typing rule, every candidate finished by the real `typeOf`,
drawn fuel), so it is sound by construction; it has no completeness proof.

It has its own schema, not `CedarTyped`'s, because that module's completeness proof enumerates its
schema's attribute types, and a set- or entity-typed attribute would falsify it.
-/

namespace CedarWide

open Basalt.PBT RandomChoice
open Cedar Cedar.Data Cedar.Spec Cedar.Validation
open CedarTyped (genInt64 genString genChar genBool isExcusedError)

/-! ## Schema -/

def userT : EntityType := ⟨"User", []⟩
def groupT : EntityType := ⟨"Group", []⟩
def photoT : EntityType := ⟨"Photo", []⟩
def albumT : EntityType := ⟨"Album", []⟩
def actionT : EntityType := ⟨"Action", []⟩
def view : EntityUID := ⟨actionT, "view"⟩
def read : EntityUID := ⟨actionT, "read"⟩

def addrTy : RecordType := Map.make [
  ("city", .optional .string),
  ("zip",  .required .int)]

def userAttrs : RecordType := Map.make [
  ("name",    .required .string),
  ("age",     .optional .int),
  ("addr",    .optional (.record addrTy)),
  ("roles",   .required (.set .string)),
  ("manager", .optional (.entity userT))]

def groupAttrs : RecordType := Map.make [("level", .required .int)]

def photoAttrs : RecordType := Map.make [
  ("owner",   .required (.entity userT)),
  ("private", .required (.bool .anyBool)),
  ("labels",  .required (.set .string))]

def ctxTy : RecordType := Map.make [
  ("authenticated", .required (.bool .anyBool)),
  ("ip",            .optional (.ext .ipAddr)),
  ("when",          .optional (.ext .datetime)),
  ("count",         .optional .int)]

def actEntry (anc : List EntityUID) : ActionSchemaEntry :=
  { appliesToPrincipal := Set.make [userT], appliesToResource := Set.make [photoT],
    ancestors := Set.make anc, context := ctxTy }

def env : TypeEnv := {
  ets := Map.make [
    (userT,  .standard ⟨Set.make [groupT], userAttrs, some .string⟩),
    (groupT, .standard ⟨Set.empty, groupAttrs, none⟩),
    (photoT, .standard ⟨Set.make [albumT], photoAttrs, none⟩),
    (albumT, .standard ⟨Set.empty, Map.empty, none⟩)],
  acts := Map.make [(view, actEntry [read]), (read, actEntry [])],
  reqty := { principal := userT, action := view, resource := photoT, context := ctxTy } }

/-! ## The vocabulary -/

def entityTypes : List EntityType := [userT, groupT, photoT, albumT, actionT]

/-- Non-boolean target types. -/
def valueTypes : List CedarType :=
  [.int, .string, .entity userT, .entity groupT, .entity photoT, .entity albumT, .entity actionT,
   .set .string, .set .int, .set (.entity groupT), .set (.entity albumT), .set (.entity userT),
   .record ctxTy, .record addrTy, .ext .ipAddr, .ext .decimal, .ext .datetime, .ext .duration]

/-- Types with attributes, which `has` and `.` apply to. -/
def baseTypes : List CedarType :=
  [.entity userT, .entity groupT, .entity photoT, .entity albumT, .entity actionT,
   .record ctxTy, .record addrTy]

def knownAttrs : List Attr :=
  ["name", "age", "addr", "roles", "manager", "city", "zip", "level", "owner", "private", "labels",
   "authenticated", "ip", "when", "count", "zzz"]

def eids : List String := ["alice", "bob", "admins", "staff", "p1", "p2", "a1", "view", "read"]

def genAttr [Gen G] : G Attr :=
  frequency! [(8, fun _ => elements knownAttrs (by decide)), (1, fun _ => genString)] (by simp)

def genTag [Gen G] : G String :=
  frequency! [(4, fun _ => elements ["t", "team", "x"] (by decide)), (1, fun _ => genString)]
    (by simp)

def genEntityUID [Gen G] : G EntityUID := do
  let t ← elements entityTypes (by decide)
  let e ← elements eids (by decide)
  return ⟨t, e⟩

def genPrim [Gen G] : G Prim :=
  oneOf! [
    fun _ => (Prim.bool ·) <$> genBool,
    fun _ => (Prim.int ·) <$> genInt64,
    fun _ => (Prim.string ·) <$> genString,
    fun _ => (Prim.entityUID ·) <$> genEntityUID]

/-- A `like` pattern: a few literal characters and `*`s. -/
def genPattern [Gen G] : G Pattern := do
  let n ← chooseNat 0 3
  let mut p : Pattern := []
  for _ in [0:n] do
    p := p ++ [← oneOf! [fun _ => pure PatElem.star, fun _ => PatElem.justChar <$> genChar]]
  return p

/-- String arguments for the extension constructors: mostly valid, some not (which `typeOf` rejects
with `extensionErr`, so the finisher discards them). -/
def ctorArgs : ExtFun → List String
  | .ip => ["10.0.0.1", "192.168.0.0/16", "::1", "127.0.0.1", "not-an-ip"]
  | .decimal => ["1.23", "-0.5", "12.3456", "0.0", "1.2.3"]
  | .datetime => ["2024-01-01", "2024-01-01T12:00:00Z", "2024-02-30", "nope"]
  | .duration => ["1h", "2d30m", "-1s", "90m", "q"]
  | _ => [""]

/-! ## Reads the typechecker accepts (as `CedarTyped`, over this schema) -/

def attrsOf : CedarType → List (Attr × QualifiedType)
  | .entity ety => ((env.ets.attrs? ety).map Map.toList).getD []
  | .record rty => rty.toList
  | _ => []

def getOut (caps : Capabilities) (x : Spec.Expr) (a : Attr) : Option CedarType :=
  match typeOf x caps env with
  | .ok (tx, _) =>
    let fromRecord (rty : RecordType) : Option CedarType :=
      match getAttrInRecord tx.typeOf rty x a caps with
      | .ok (ty, _) => some ty
      | .error _ => none
    match tx.typeOf with
    | .record rty => fromRecord rty
    | .entity ety => (env.ets.attrs? ety).bind fromRecord
    | _ => none
  | .error _ => none

def capReads (caps : Capabilities) (p : CedarType → Bool) : List Spec.Expr :=
  caps.filterMap fun
    | (x, .attr a) => match getOut caps x a with
      | some ty => if p ty then some (.getAttr x a) else none
      | none => none
    | _ => none

/-- Tag reads the capabilities in scope justify: `x.getTag(t)` for each `(x, .tag t) ∈ caps`. -/
def tagReads (caps : Capabilities) : List Spec.Expr :=
  caps.filterMap fun
    | (x, .tag t) => some (.binaryApp .getTag x t)
    | _ => none

def requiredAttrs (p : CedarType → Bool) : List (CedarType × Attr) :=
  baseTypes.flatMap fun bt =>
    (attrsOf bt).filterMap fun
      | (a, .required t) => if p t then some (bt, a) else none
      | _ => none

def isBool : CedarType → Bool
  | .bool _ => true
  | _ => false

/-! ## The finishers -/

def finishS (caps : Capabilities) (e : Spec.Expr) : Option (Spec.Expr × BoolType × Capabilities) :=
  match typeOf e caps env with
  | .ok (tx, c) =>
    match tx.typeOf with
    | .bool b => some (e, b, c)
    | _ => none
  | .error _ => none

def finishC (caps : Capabilities) (ty : CedarType) (e : Spec.Expr) :
    Option (Spec.Expr × Capabilities) :=
  match typeOf e caps env with
  | .ok (tx, c) => if tx.typeOf = ty then some (e, c) else none
  | .error _ => none

/-- Any well-typed expression, with its type: for operands whose type is not fixed in advance. -/
def finishAny (caps : Capabilities) (e : Spec.Expr) : Option (Spec.Expr × CedarType) :=
  match typeOf e caps env with
  | .ok (tx, _) => some (e, tx.typeOf)
  | .error _ => none

/-! ## The generators

Structural recursion on the fuel, as a *family*: the generators at fuel `d + 1` are built from the
family at fuel `d`, and each typing rule is its own small definition taking that family as an
argument. (One `mutual` `partial_fixpoint` block holding all of these rules exceeds 4M heartbeats in
its monotonicity check; this generator is sound by its finisher and has no completeness proof, so it
does not need to be a fixpoint.) A sub-generator's fuel is the level below, which includes the leaves.
-/

/-- The generators at one fuel level. -/
structure Fam (G : Type → Type) where
  /-- Boolean candidates. -/
  s : Capabilities → G (Option Spec.Expr)
  /-- Candidates at a non-boolean type. -/
  c : Capabilities → CedarType → G (Option Spec.Expr)
  /-- Anything, for dead branches. -/
  any : G Spec.Expr

section
variable [Gen G] (f : Fam G) (caps : Capabilities)

/-- Leaves at a non-boolean type: literals, variables, entity literals, extension constructors. -/
def leaf (ty : CedarType) : G (Option Spec.Expr) :=
  match ty with
  | .int => do return some (.lit (.int (← genInt64)))
  | .string => do return some (.lit (.string (← genString)))
  | .entity ety => do
    let e ← elements eids (by decide)
    let lit : Spec.Expr := .lit (.entityUID ⟨ety, e⟩)
    if ety == userT then oneOf! [fun _ => pure (some (.var .principal)), fun _ => pure (some lit)]
    else if ety == photoT then oneOf! [fun _ => pure (some (.var .resource)), fun _ => pure (some lit)]
    else if ety == actionT then
      oneOf! [fun _ => pure (some (.var .action)),
              fun _ => do return some (.lit (.entityUID (← elements [view, read] (by decide))))]
    else return some lit
  | .record rty => if rty == ctxTy then return some (.var .context) else return none
  | .set elt => do
    -- a singleton set of a leaf, so that set types are inhabited at fuel `0`
    let x ← match elt with
      | .int => pure (Spec.Expr.lit (.int (← genInt64)))
      | .string => pure (Spec.Expr.lit (.string (← genString)))
      | .entity ety => pure (Spec.Expr.lit (.entityUID ⟨ety, ← elements eids (by decide)⟩))
      | _ => pure (Spec.Expr.lit (.bool true))
    return some (.set [x])
  | .ext xt =>
    let fn : ExtFun := match xt with
      | .ipAddr => .ip | .decimal => .decimal | .datetime => .datetime | .duration => .duration
    match ctorArgs fn with
    | [] => return none
    | a :: as => do return some (.call fn [.lit (.string (← elements (a :: as) (by simp)))])
  | _ => return none

/-- A boolean sub-judgment. A candidate `typeOf` rejects, or a rule that could not complete, falls
back to a literal: failures compound through every rule with several operands, and without the
fallback three draws in four came back empty. -/
def subS (caps : Capabilities) : G (Option (Spec.Expr × BoolType × Capabilities)) := do
  match (← f.s caps).bind (finishS caps) with
  | some r => return some r
  | none => return finishS caps (.lit (.bool (← genBool)))

/-- A sub-judgment at `ty`, falling back to a leaf of that type as `subS` does. -/
def subC (caps : Capabilities) (ty : CedarType) : G (Option (Spec.Expr × Capabilities)) := do
  match (← f.c caps ty).bind (finishC caps ty) with
  | some r => return some r
  | none => return (← leaf ty).bind (finishC caps ty)

def ruleAnd : G (Option Spec.Expr) := do
  match (← subS f caps) with
  | none => return none
  | some a =>
    match a.2.1 with
    | .ff => return some (.and a.1 (← f.any))
    | _ =>
      match (← subS f (caps ∪ a.2.2)) with
      | none => return none
      | some b => return some (.and a.1 b.1)

def ruleOr : G (Option Spec.Expr) := do
  match (← subS f caps) with
  | none => return none
  | some a =>
    match a.2.1 with
    | .tt => return some (.or a.1 (← f.any))
    | _ =>
      match (← subS f caps) with
      | none => return none
      | some b => return some (.or a.1 b.1)

/-- `if g then t else e`, with `branch caps` generating a branch; the guard's capabilities reach the
*then* branch only, and a singleton guard leaves the other branch untyped. -/
def ruleIte (branch : Capabilities → G (Option Spec.Expr)) : G (Option Spec.Expr) := do
  match (← subS f caps) with
  | none => return none
  | some g =>
    match g.2.1 with
    | .tt =>
      match (← branch (caps ∪ g.2.2)) with
      | none => return none
      | some t => return some (.ite g.1 t (← f.any))
    | .ff =>
      match (← branch caps) with
      | none => return none
      | some e => return some (.ite g.1 (← f.any) e)
    | .anyBool =>
      match (← branch (caps ∪ g.2.2)) with
      | none => return none
      | some t =>
        match (← branch caps) with
        | none => return none
        | some e => return some (.ite g.1 t e)

/-- A base for `has`/`.`: a generated expression of a type with attributes. -/
def base : G (Option Spec.Expr) := do
  let bt ← elements baseTypes (by decide)
  return (← subC f caps bt).map (·.1)

def ruleHas : G (Option Spec.Expr) := do
  match (← base f caps) with
  | none => return none
  | some x => return some (.hasAttr x (← genAttr))

def ruleExtHas : G (Option Spec.Expr) := do
  match (← base f caps) with
  | none => return none
  | some x => return some (.extHasAttr x (← genAttr) [← genAttr])

def ruleHasTag : G (Option Spec.Expr) := do
  let et ← elements entityTypes (by decide)
  match (← subC f caps (.entity et)) with
  | none => return none
  | some x => return some (.binaryApp .hasTag x.1 (.lit (.string (← genTag))))

/-- An attribute read at a type satisfying `p`: justified by a capability, or a required attribute
of a generated base. -/
def ruleRead (p : CedarType → Bool) : G (Option Spec.Expr) :=
  oneOf! [
    fun _ =>
      match capReads caps p with
      | [] => return none
      | r :: rs => some <$> elements (r :: rs) (by simp),
    fun _ =>
      match requiredAttrs p with
      | [] => return none
      | r :: rs => do
        let q ← elements (r :: rs) (by simp)
        return (← subC f caps q.1).map fun x => .getAttr x.1 q.2]

/-- Two operands at one type, combined by `mk`. -/
def binary (ty₁ ty₂ : CedarType) (mk : Spec.Expr → Spec.Expr → Spec.Expr) : G (Option Spec.Expr) := do
  match (← subC f caps ty₁) with
  | none => return none
  | some a =>
    match (← subC f caps ty₂) with
    | none => return none
    | some b => return some (mk a.1 b.1)

/-- A record literal of one to three fields, each a well-typed expression of some value type. -/
def record : G (Option Spec.Expr) := do
  let n ← chooseNat 1 3
  let field : G (Option (Attr × Spec.Expr)) := do
    let a ← genAttr
    let ty ← elements valueTypes (by decide)
    return (← subC f caps ty).map fun x => (a, x.1)
  let f₁ ← field
  let f₂ ← field
  let f₃ ← field
  let fs := ([f₁, f₂, f₃].take n).filterMap id
  -- a record literal's attribute names must be distinct
  return some (.record (fs.foldl (fun acc x => if acc.any (·.1 == x.1) then acc else acc ++ [x]) []))

def stepS : G (Option Spec.Expr) :=
  frequency! [
    (2, fun _ => do return some (.lit (.bool (← genBool)))),
    (4, fun _ => ruleAnd f caps),
    (2, fun _ => ruleOr f caps),
    (2, fun _ => ruleIte f caps fun c => do return (← subS f c).map (·.1)),
    (4, fun _ => ruleHas f caps),
    (1, fun _ => ruleExtHas f caps),
    (2, fun _ => ruleHasTag f caps),
    (1, fun _ => ruleRead f caps isBool),
    (1, fun _ => do return (← subS f caps).map fun a => .unaryApp .not a.1),
    (1, fun _ => do
          let bt ← elements entityTypes (by decide)
          let ety ← elements entityTypes (by decide)
          return (← subC f caps (.entity bt)).map fun x => .unaryApp (.is ety) x.1),
    (2, fun _ => do
          let op ← elements [BinaryOp.less, BinaryOp.lessEq] (by decide)
          let ty ← elements [CedarType.int, .ext .datetime, .ext .duration] (by decide)
          binary f caps ty ty (.binaryApp op)),
    (2, fun _ => do
          let ty ← elements valueTypes (by decide)
          binary f caps ty ty (.binaryApp .eq)),
    (1, fun _ => do
          match (← subS f caps) with
          | none => return none
          | some a => return (← subS f caps).map fun b => .binaryApp .eq a.1 b.1),
    (1, fun _ => do return some (.binaryApp .eq (.lit (← genPrim)) (.lit (← genPrim)))),
    (3, fun _ => do
          let t₁ ← elements entityTypes (by decide)
          let t₂ ← elements entityTypes (by decide)
          let rhs ← elements [CedarType.entity t₂, .set (.entity t₂)] (by simp)
          binary f caps (.entity t₁) rhs (.binaryApp .mem)),
    (2, fun _ => do
          let ty ← elements [CedarType.string, .int, .entity groupT, .entity albumT] (by decide)
          binary f caps (.set ty) ty (.binaryApp .contains)),
    (2, fun _ => do
          let ty ← elements [CedarType.string, .int, .entity groupT, .entity albumT] (by decide)
          let op ← elements [BinaryOp.containsAll, BinaryOp.containsAny] (by decide)
          binary f caps (.set ty) (.set ty) (.binaryApp op)),
    (1, fun _ => do
          let ty ← elements [CedarType.string, .int, .entity groupT] (by decide)
          return (← subC f caps (.set ty)).map fun x => .unaryApp .isEmpty x.1),
    (1, fun _ => do
          let p ← genPattern
          return (← subC f caps .string).map fun x => .unaryApp (.like p) x.1),
    (1, fun _ => do
          match (← record f caps) with
          | none => return none
          | some r => return some (.hasAttr r (← genAttr))),
    (2, fun _ => do
          let fn ← elements [ExtFun.isIpv4, .isIpv6, .isLoopback, .isMulticast] (by decide)
          return (← subC f caps (.ext .ipAddr)).map fun x => .call fn [x.1]),
    (1, fun _ => binary f caps (.ext .ipAddr) (.ext .ipAddr) fun x y => .call .isInRange [x, y]),
    (1, fun _ => do
          let fn ← elements [ExtFun.lessThan, .lessThanOrEqual, .greaterThan, .greaterThanOrEqual]
            (by decide)
          binary f caps (.ext .decimal) (.ext .decimal) fun x y => .call fn [x, y])
  ] (by simp)

/-- Constructions specific to a target type. -/
def construct (ty : CedarType) : G (Option Spec.Expr) :=
  match ty with
  | .int => do
    oneOf! [
      fun _ => do
        let op ← elements [BinaryOp.add, BinaryOp.sub, BinaryOp.mul] (by decide)
        binary f caps .int .int (.binaryApp op),
      fun _ => do return (← subC f caps .int).map fun a => .unaryApp .neg a.1,
      fun _ => do
        let fn ← elements [ExtFun.toMilliseconds, .toSeconds, .toMinutes, .toHours, .toDays]
          (by decide)
        return (← subC f caps (.ext .duration)).map fun x => .call fn [x.1]]
  | .string =>
    match tagReads caps with
    | r :: rs => some <$> elements (r :: rs) (by simp)
    | [] => return none
  | .set elt => do
    let n ← chooseNat 1 3
    let x₁ ← subC f caps elt
    let x₂ ← subC f caps elt
    let x₃ ← subC f caps elt
    return some (.set (([x₁, x₂, x₃].take n).filterMap (·.map (·.1))))
  | .ext .datetime =>
    oneOf! [
      fun _ => binary f caps (.ext .datetime) (.ext .duration) fun x y => .call .offset [x, y],
      fun _ => do return (← subC f caps (.ext .datetime)).map fun x => .call .toDate [x.1]]
  | .ext .duration =>
    oneOf! [
      fun _ => binary f caps (.ext .datetime) (.ext .datetime) fun x y => .call .durationSince [x, y],
      fun _ => do return (← subC f caps (.ext .datetime)).map fun x => .call .toTime [x.1]]
  | _ => return none

def stepC (ty : CedarType) : G (Option Spec.Expr) :=
  frequency! [
    (3, fun _ => leaf ty),
    (2, fun _ => ruleIte f caps fun c => do return (← subC f c ty).map (·.1)),
    (3, fun _ => ruleRead f caps (· == ty)),
    (1, fun _ => do
          match (← record f caps) with
          | none => return none
          | some r => return some (.getAttr r (← genAttr))),
    (3, fun _ => construct f caps ty)
  ] (by simp)

def stepAny : G Spec.Expr :=
  frequency! [
    (3, fun _ => oneOf! [
          fun _ => (Spec.Expr.lit ·) <$> genPrim,
          fun _ => (Spec.Expr.var ·) <$>
            elements [Var.principal, .action, .resource, .context] (by decide)]),
    (1, fun _ => do return .ite (← f.any) (← f.any) (← f.any)),
    (1, fun _ => do return .and (← f.any) (← f.any)),
    (1, fun _ => do return .or (← f.any) (← f.any)),
    (1, fun _ => do
          let op ← elements [BinaryOp.eq, .less, .add, .mem, .contains, .hasTag] (by decide)
          return .binaryApp op (← f.any) (← f.any)),
    (1, fun _ => do return .hasAttr (← f.any) (← genAttr)),
    (1, fun _ => do return .getAttr (← f.any) (← genAttr)),
    (1, fun _ => do return .set [← f.any])
  ] (by simp)

end

/-- The family at fuel `d`: leaves only at `0`, and each level's rules over the level below. -/
def fam [Gen G] : Nat → Fam G
  | 0 => { s := fun _ => do return some (.lit (.bool (← genBool))),
           c := fun _ ty => leaf ty,
           any := (Spec.Expr.lit ·) <$> genPrim }
  | d + 1 =>
    let f := fam d
    { s := stepS f, c := stepC f, any := stepAny f }

/-- Boolean expressions with the type and output capabilities `typeOf` gives them. -/
def genS [Gen G] (caps : Capabilities) (d : Nat) :
    G (Option (Spec.Expr × BoolType × Capabilities)) :=
  subS (fam d) caps

/-! ## Requests and entities conforming to the schema -/

def uid (t : EntityType) (e : String) : EntityUID := ⟨t, e⟩

def genSubset [Gen G] (xs : List α) : G (List α) := do
  let mut out := []
  for x in xs do
    if ← genBool then out := out ++ [x]
  return out

def genStrSet [Gen G] : G Value := do
  let xs ← genSubset ["admin", "dev", "x", ""]
  return .set (Set.make (xs.map fun s => Value.prim (.string s)))

def genUser [Gen G] (name : String) : G (EntityUID × EntityData) := do
  let groups ← genSubset [uid groupT "admins", uid groupT "staff"]
  let base : List (Attr × Value) := [("name", .prim (.string name)), ("roles", ← genStrSet)]
  let age : List (Attr × Value) ← do
    if ← genBool then pure [("age", .prim (.int (← genInt64)))] else pure []
  let addr : List (Attr × Value) ← do
    if ← genBool then
      let city : List (Attr × Value) ← do
        if ← genBool then pure [("city", .prim (.string (← genString)))] else pure []
      pure [("addr", .record (Map.make (city ++ [("zip", .prim (.int (← genInt64)))])))]
    else pure []
  let mgr : List (Attr × Value) ←
    if ← genBool then pure [("manager", .prim (.entityUID (uid userT (← elements ["alice", "bob"]
      (by decide)))))] else pure []
  let tags : List (Attr × Value) ← do
    if ← genBool then pure [("t", .prim (.string (← genString)))] else pure []
  return (uid userT name,
    { attrs := Map.make (base ++ age ++ addr ++ mgr), ancestors := Set.make groups,
      tags := Map.make tags })

def genPhoto [Gen G] (name : String) : G (EntityUID × EntityData) := do
  let albums ← genSubset [uid albumT "a1"]
  return (uid photoT name,
    { attrs := Map.make [("owner", .prim (.entityUID (uid userT (← elements ["alice", "bob"]
                            (by decide))))),
                         ("private", .prim (.bool (← genBool))), ("labels", ← genStrSet)],
      ancestors := Set.make albums, tags := Map.empty })

def genEntities [Gen G] : G Entities := do
  let alice ← genUser "alice"
  let bob ← genUser "bob"
  let p1 ← genPhoto "p1"
  let p2 ← genPhoto "p2"
  let group (n : String) (lvl : Int64) : EntityUID × EntityData :=
    (uid groupT n, { attrs := Map.make [("level", .prim (.int lvl))], ancestors := Set.empty,
                     tags := Map.empty })
  let admins := group "admins" (← genInt64)
  let staff := group "staff" (← genInt64)
  let a1 : EntityUID × EntityData :=
    (uid albumT "a1", { attrs := Map.empty, ancestors := Set.empty, tags := Map.empty })
  return Map.make [alice, bob, p1, p2, admins, staff, a1,
    (view, actionSchemaEntryToEntityData (actEntry [read])),
    (read, actionSchemaEntryToEntityData (actEntry []))]

def genRequest [Gen G] : G Request := do
  let principal := uid userT (← elements ["alice", "bob"] (by decide))
  let resource := uid photoT (← elements ["p1", "p2"] (by decide))
  let ip : List (Attr × Value) ← do
    if ← genBool then
      match Ext.IPAddr.ip (← elements ["10.0.0.1", "192.168.1.7", "::1"] (by decide)) with
      | some v => pure [("ip", .ext (.ipaddr v))]
      | none => pure []
    else pure []
  let wh : List (Attr × Value) ← do
    if ← genBool then
      match Ext.Datetime.parse (← elements ["2024-01-01", "2025-06-30T08:00:00Z"] (by decide)) with
      | some v => pure [("when", .ext (.datetime v))]
      | none => pure []
    else pure []
  let cnt : List (Attr × Value) ← do
    if ← genBool then pure [("count", .prim (.int (← genInt64)))] else pure []
  return { principal, action := view, resource,
           context := Map.make ([("authenticated", .prim (.bool (← genBool)))] ++ ip ++ wh ++ cnt) }

/-! ## Properties -/

def entitiesOk (es : Entities) : Bool :=
  match entitiesMatchEnvironment env es with
  | .ok _ => true
  | .error _ => false

def soundOutcome (e : Spec.Expr) (req : Request) (es : Entities) (tx : TypedExpr) : Bool :=
  match evaluate e req es with
  | .ok v => instanceOfType v tx.typeOf env.schema
  | .error err => isExcusedError err

/-- The schema is well formed, so `type_of_is_sound`'s environment hypothesis can hold. -/
def prop_env_wf {G : Type → Type} [Gen G] : PropM G Unit :=
  check (match env.validateWellFormed with | .ok _ => true | .error _ => false)
    "the wide schema is not well formed"

/-- The generated request and entities conform to the schema (the other half of the hypothesis). -/
def prop_inputs_ok [Gen G] : PropM G Unit := do
  let req ← generate genRequest
  let es ← generate genEntities
  check (requestMatchesEnvironment env req) s!"request: {reprStr req}"
  check (entitiesOk es) "entities do not match the schema"

/-- Cedar's `type_of_is_sound`, over the wide generator. -/
def prop_soundness [Gen G] : PropM G Unit := do
  -- The expression first: under `FuzzGen` draw order is byte order (see `CedarTyped.prop_soundness`).
  let r ← generate (genS ∅ 4)
  let req ← generate genRequest
  let es ← generate genEntities
  assume (requestMatchesEnvironment env req)
  assume (entitiesOk es)
  match r with
  | none => assume false
  | some (e, _, _) =>
    match typeOf e ∅ env with
    | .error _ => check false s!"ill-typed: {reprStr e}"
    | .ok (tx, _) =>
      check (soundOutcome e req es tx)
        s!"UNSOUND: {reprStr e} evaluated to {reprStr (evaluate e req es)}"

/-- `prop_soundness`, printing `BASALT_H <hash of the expression> <hash of the whole input>` to stderr
for every test, so the number of *distinct* inputs a campaign tried can be counted
(`fuzz-run/coverage-curves.py`). The print is inside `check`'s argument so it cannot be elided. -/
def prop_soundness_traced [Gen G] : PropM G Unit := do
  let r ← generate (genS ∅ 4)
  let req ← generate genRequest
  let es ← generate genEntities
  let e := match r with | some (e, _, _) => e | none => .lit (.bool true)
  let he := hash (reprStr e)
  let hi := mixHash he (mixHash (hash (reprStr req)) (hash (reprStr es.toList)))
  check (dbgTrace s!"BASALT_H {he} {hi}" fun _ => true)
  assume (requestMatchesEnvironment env req)
  assume (entitiesOk es)
  match typeOf e ∅ env with
  | .error _ => pure ()
  | .ok (tx, _) =>
    check (soundOutcome e req es tx)
      s!"UNSOUND: {reprStr e} evaluated to {reprStr (evaluate e req es)}"

end CedarWide
