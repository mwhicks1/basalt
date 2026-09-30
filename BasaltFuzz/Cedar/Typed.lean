/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Basalt.Combinators
import Basalt.PBT.Property
import Cedar.Validation

/-!
# A generator for Cedar's typing judgment, rule for rule (narrow fragment)

`genS caps d` generates `(e, bty, c')` with `typeOf e caps env = .ok (tx, c')` and
`tx.typeOf = .bool bty`; `genC caps d ty` generates `(e, c')` with the same judgment at the non-boolean
type `ty`. Each branch is one case of `Cedar.Validation.typeOf` (`Cedar/Validation/Typechecker.lean`)
run backwards, over a small schema with one required and one optional attribute on the principal and
the context, and a nested optional record (`principal.addr.city`). Every candidate is finished by the
real `typeOf`, which is what makes soundness a short lemma.

`BasaltExamples/Cedar/Typed.lean` proves the generator sound and complete for the fragment `Frag`
(literals, variables, `if`/`&&`/`||`, `!`/`-`/`is`, `==`/`<`/`<=`/`+`/`-`/`*`, `has`/`.`).
Mathlib-free, so `basalt-fuzz` links it.
-/

namespace CedarTyped

open Basalt.PBT RandomChoice
open Cedar Cedar.Data Cedar.Spec Cedar.Validation

/-! ## A schema with nested optional attributes

Shaped so `TypeEnv.validateWellFormed` succeeds — action entity types are *not* in `ets`, no `bool`
singletons appear in schema types, and `reqty.context` is exactly the action's context
(`Cedar/Validation/EnvironmentValidator.lean`). The principal's optional `addr` is itself a record with
an optional `city`, so a read of `principal.addr.city` needs *two* capabilities, the second keyed on
the non-trivial base expression `principal.addr`. -/

def pType : EntityType := ⟨"Principal", []⟩
def rType : EntityType := ⟨"Resource", []⟩
def aType : EntityType := ⟨"Action", []⟩
def act   : EntityUID  := ⟨aType, "access"⟩

def addrTy : RecordType := Map.make [
  ("city", .optional .string),
  ("zip",  .required .int)]

def pAttrs : RecordType := Map.make [
  ("req",  .required .string),
  ("opt",  .optional .string),
  ("addr", .optional (.record addrTy))]

def ctxTy : RecordType := Map.make [
  ("cReq", .required (.bool .anyBool)),
  ("cOpt", .optional .int)]

def env : TypeEnv := {
  ets := Map.make [
    (pType, .standard ⟨Set.empty, pAttrs, some .string⟩),
    (rType, .standard ⟨Set.empty, Map.empty, none⟩)],
  acts := Map.make [
    (act, { appliesToPrincipal := Set.make [pType],
            appliesToResource  := Set.make [rType],
            ancestors          := Set.empty,
            context            := ctxTy })],
  reqty := { principal := pType, action := act, resource := rType, context := ctxTy } }

/-! ## Reading the schema -/

/-- The attributes of a type, with their qualifiers: an entity's from the schema, a record's own. -/
def attrsOf : CedarType → List (Attr × QualifiedType)
  | .entity ety => ((env.ets.attrs? ety).map Map.toList).getD []
  | .record rty => rty.toList
  | _ => []

/-! ## Leaf generators -/

def genBool [Gen G] : G Bool :=
  oneOf! [fun _ => pure true, fun _ => pure false]

def genSmallInt [Gen G] : G Int64 :=
  (fun n => Int64.ofInt (n - 4)) <$> chooseNat 0 8

def genStr [Gen G] : G String :=
  elements ["John", "Jane", "", "x"] (by decide)

/-! ## A concrete request and entity store matching the schema

Cedar's `type_of_is_sound` (`Cedar/Thm/Validation/Typechecker.lean`) needs
`InstanceOfWellFormedEnvironment request entities env`, which
`Cedar/Thm/Validation/RequestEntityValidation.lean`'s `instance_of_well_formed_env` supplies from
three *executable* checks: `env.validateWellFormed`, `requestMatchesEnvironment`, and
`entitiesMatchEnvironment`. The property below establishes those by `assume`, so what it tests is
exactly the theorem's conclusion under exactly the theorem's hypotheses. -/

def pUid : EntityUID := ⟨pType, "alice"⟩
def rUid : EntityUID := ⟨rType, "photo"⟩

/-- A request whose context always has the required attribute and optionally the optional one. -/
def genRequest [Gen G] : G Request := do
  let cReq ← genBool
  let withOpt ← genBool
  let cOpt ← genSmallInt
  let ctx := if withOpt
    then Map.make [("cReq", .prim (.bool cReq)), ("cOpt", .prim (.int cOpt))]
    else Map.make [("cReq", .prim (.bool cReq))]
  return { principal := pUid, action := act, resource := rUid, context := ctx }

/-- The entity store: the principal (its required attribute always present, `opt` and `addr` — and
`addr`'s own optional `city` — each only sometimes), the resource, and, as `instanceOfSchema`'s
`HasAllActions` demands, the action entity. The optional attributes being absent at random is what
makes a capability-guarded read's guard actually decide something. -/
def genEntities [Gen G] : G Entities := do
  let req ← genStr
  let opt ← genStr
  let city ← genStr
  let zip ← genSmallInt
  let tag ← genStr
  let withOpt ← genBool
  let withAddr ← genBool
  let withCity ← genBool
  let addrV : Value := .record (Map.make
    ((if withCity then [("city", Value.prim (.string city))] else []) ++
      [("zip", Value.prim (.int zip))]))
  let pAttrsV : Map Attr Value := Map.make
    ([("req", Value.prim (.string req))] ++
      (if withOpt then [("opt", Value.prim (.string opt))] else []) ++
      (if withAddr then [("addr", addrV)] else []))
  let pData : EntityData :=
    { attrs := pAttrsV, ancestors := Set.empty, tags := Map.make [("t", Value.prim (.string tag))] }
  let rData : EntityData := { attrs := Map.empty, ancestors := Set.empty, tags := Map.empty }
  let aData : EntityData := actionSchemaEntryToEntityData
    { appliesToPrincipal := Set.make [pType], appliesToResource := Set.make [rType],
      ancestors := Set.empty, context := ctxTy }
  return Map.make [(pUid, pData), (rUid, rData), (act, aData)]

/-- The three runtime errors Cedar's `EvaluatesTo` excuses a well-typed expression for. The parameter
is spelled with its full name because `Cedar.Spec.Error` and `Cedar.Validation.TypeError` share
constructor names, and with both namespaces open a bare `.typeError` resolves to the wrong one. -/
def isExcusedError (err : Cedar.Spec.Error) : Bool :=
  match err with
  | .entityDoesNotExist | .extensionError | .arithBoundsError => true
  | _ => false

/-- Are the entities schema-conformant? The `Except`-valued check as a `Bool`. -/
def entitiesOk (es : Entities) : Bool :=
  match entitiesMatchEnvironment env es with
  | .ok _ => true
  | .error _ => false

/-- `type_of_is_sound`'s conclusion as one decidable check: evaluation yields a value of the
typechecker's type, or fails only with an error `EvaluatesTo` excuses. -/
def soundOutcome (e : Spec.Expr) (req : Request) (es : Entities) (tx : TypedExpr) : Bool :=
  match evaluate e req es with
  | .ok v => instanceOfType v tx.typeOf env.schema
  | .error err => isExcusedError err

/-! ## The fragment's vocabulary -/

/-- The entity types a well-typed fragment expression can have: those of the request variables. -/
def entityTypes : List EntityType := [pType, rType, aType]

/-- The non-boolean types a fragment expression can have. -/
def valueTypes : List CedarType :=
  [.int, .string, .entity pType, .entity rType, .entity aType, .record ctxTy, .record addrTy]

/-- The types `has` and `.`-access can be applied to. -/
def baseTypes : List CedarType :=
  [.entity pType, .entity rType, .entity aType, .record ctxTy, .record addrTy]

/-- The attribute names the schema mentions, plus one it does not. -/
def knownAttrs : List Attr := ["req", "opt", "addr", "city", "zip", "cReq", "cOpt", "zzz"]

/-! ## Leaf generators, complete over their types

Each is biased toward a handful of values so generated terms stay readable, but reaches every value:
completeness of the whole generator needs every literal, and every attribute name in a `has` (an
attribute absent from the type makes `has` typecheck at `bool ff`). -/

def genInt64 [Gen G] : G Int64 :=
  frequency! [
    (8, fun _ => (fun n => Int64.ofInt (n - 4)) <$> chooseNat 0 8),
    (1, fun _ => Int64.ofInt <$> chooseInt (-9223372036854775808) 9223372036854775807 (by omega))
  ] (by simp)

def genChar [Gen G] : G Char :=
  frequency! [
    (8, fun _ => elements ['a', 'b', ' '] (by decide)),
    (1, fun _ => Char.ofNat <$> chooseNat 0 0x10FFFF)
  ] (by simp)

/-- An arbitrary string: usually a short fixed one, otherwise any list of characters. -/
def genString [Gen G] : G String :=
  frequency! [
    (6, fun _ => elements ["", "John", "x"] (by decide)),
    (1, fun _ => String.ofList <$> listOf genChar)
  ] (by simp)

def genAttr [Gen G] : G Attr :=
  frequency! [
    (6, fun _ => elements knownAttrs (by decide)),
    (1, fun _ => genString)
  ] (by simp)

def genPrim [Gen G] : G Prim :=
  oneOf! [
    fun _ => (Prim.bool ·) <$> genBool,
    fun _ => (Prim.int ·) <$> genInt64,
    fun _ => (Prim.string ·) <$> genString]

/-! ## Attribute reads the typechecker accepts -/

/-- `typeOfGetAttr`: the type of `x.a` under `caps`, or `none` if it is a type error. Types `x` with
the real `typeOf`, so a read is offered exactly when the typechecker accepts it. -/
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

/-- The reads the capabilities in scope justify, at a type satisfying `p`: `x.a` for each
`(x, .attr a) ∈ caps` that `getOut` accepts. -/
def capReads (caps : Capabilities) (p : CedarType → Bool) : List (Spec.Expr × CedarType) :=
  caps.filterMap fun
    | (x, .attr a) => match getOut caps x a with
      | some ty => if p ty then some (.getAttr x a, ty) else none
      | none => none
    | _ => none

/-- `(base type, attribute)` pairs for required attributes of a type satisfying `p`. A required
attribute is read without a capability (`getAttrInRecord`'s `.required` case). -/
def requiredAttrs (p : CedarType → Bool) : List (CedarType × Attr × CedarType) :=
  baseTypes.flatMap fun bt =>
    (attrsOf bt).filterMap fun
      | (a, .required t) => if p t then some (bt, a, t) else none
      | _ => none

def isBool : CedarType → Bool
  | .bool _ => true
  | _ => false

/-! ## The judgment, by the typechecker

A candidate becomes a result only through `finishS`/`finishC`, which ask the real `typeOf`. So the
type and capabilities a result carries are `typeOf`'s by definition, the generator is sound whatever
its branches do, and the branches are free to be a faithful — and therefore complete — enumeration of
`typeOf`'s rules. -/

/-- A boolean candidate's judgment, if it has one. -/
def finishS (caps : Capabilities) (e : Spec.Expr) : Option (Spec.Expr × BoolType × Capabilities) :=
  match typeOf e caps env with
  | .ok (tx, c) =>
    match tx.typeOf with
    | .bool b => some (e, b, c)
    | _ => none
  | .error _ => none

/-- A candidate's judgment at the non-boolean type `ty`, if it has one. -/
def finishC (caps : Capabilities) (ty : CedarType) (e : Spec.Expr) :
    Option (Spec.Expr × Capabilities) :=
  match typeOf e caps env with
  | .ok (tx, c) => if tx.typeOf = ty then some (e, c) else none
  | .error _ => none

/-! ## The candidate generators

Mutually recursive on the fuel `d`, one branch per rule of `typeOf`. A branch generates its
subexpressions *as judgments* (through the finishers), and uses their types and capabilities exactly
where `typeOf` does: an `ff` left operand of `&&` or `tt` guard of `ite` makes the other side dead
(`genAny`, anything at all), and a guard's capabilities are added to the scope of `&&`'s right
operand and `ite`'s *then* branch. A branch that cannot proceed returns `none`.

Do not destructure a bind with a tuple pattern (`let (g, c) ← …`) inside these `frequency!` branches:
the build fails with "(kernel) deep recursion detected" reported at the `def` line. Bind and project.
-/

set_option maxHeartbeats 2000000 in
mutual

/-- Boolean candidates. -/
def candS [Gen G] (caps : Capabilities) : Nat → G (Option Spec.Expr)
  | 0 => do return some (.lit (.bool (← genBool)))
  | d + 1 =>
    frequency! [
      (2, fun _ => candS caps 0),
      -- `a && b`: an `ff` left operand leaves `b` untyped; otherwise `b` sees `caps ∪ c₁`
      (4, fun _ => do
            match (← candS caps (← chooseNat 0 d)).bind (finishS caps) with
            | none => return none
            | some a =>
              match a.2.1 with
              | .ff => return some (.and a.1 (← genAny (← chooseNat 0 d)))
              | _ =>
                match (← candS (caps ∪ a.2.2) (← chooseNat 0 d)).bind (finishS (caps ∪ a.2.2)) with
                | none => return none
                | some b => return some (.and a.1 b.1)),
      -- `a || b`: a `tt` left operand leaves `b` untyped; `b` sees `caps` alone
      (2, fun _ => do
            match (← candS caps (← chooseNat 0 d)).bind (finishS caps) with
            | none => return none
            | some a =>
              match a.2.1 with
              | .tt => return some (.or a.1 (← genAny (← chooseNat 0 d)))
              | _ =>
                match (← candS caps (← chooseNat 0 d)).bind (finishS caps) with
                | none => return none
                | some b => return some (.or a.1 b.1)),
      -- `if g then t else e`: a singleton guard leaves the other branch untyped; `t` sees `caps ∪ c₁`
      (2, fun _ => do
            match (← candS caps (← chooseNat 0 d)).bind (finishS caps) with
            | none => return none
            | some g =>
              match g.2.1 with
              | .tt =>
                match (← candS (caps ∪ g.2.2) (← chooseNat 0 d)).bind (finishS (caps ∪ g.2.2)) with
                | none => return none
                | some t => return some (.ite g.1 t.1 (← genAny (← chooseNat 0 d)))
              | .ff =>
                match (← candS caps (← chooseNat 0 d)).bind (finishS caps) with
                | none => return none
                | some e => return some (.ite g.1 (← genAny (← chooseNat 0 d)) e.1)
              | .anyBool =>
                match (← candS (caps ∪ g.2.2) (← chooseNat 0 d)).bind (finishS (caps ∪ g.2.2)) with
                | none => return none
                | some t =>
                  match (← candS caps (← chooseNat 0 d)).bind (finishS caps) with
                  | none => return none
                  | some e => return some (.ite g.1 t.1 e.1)),
      -- `x has a`, for a generated base: the source of capabilities
      (4, fun _ => do
            let bt ← elements baseTypes (by decide)
            match (← candC caps (← chooseNat 0 d) bt).bind (finishC caps bt) with
            | none => return none
            | some x => return some (.hasAttr x.1 (← genAttr))),
      (1, fun _ => do genRead caps (← chooseNat 0 d) isBool),
      (1, fun _ => do
            match (← candS caps (← chooseNat 0 d)).bind (finishS caps) with
            | none => return none
            | some a => return some (.unaryApp .not a.1)),
      (1, fun _ => do
            let bt ← elements entityTypes (by decide)
            let ety ← elements entityTypes (by decide)
            match (← candC caps (← chooseNat 0 d) (.entity bt)).bind (finishC caps (.entity bt)) with
            | none => return none
            | some x => return some (.unaryApp (.is ety) x.1)),
      (2, fun _ => do
            let op ← elements [BinaryOp.less, BinaryOp.lessEq] (by decide)
            match (← candC caps (← chooseNat 0 d) .int).bind (finishC caps .int) with
            | none => return none
            | some a =>
              match (← candC caps (← chooseNat 0 d) .int).bind (finishC caps .int) with
              | none => return none
              | some b => return some (.binaryApp op a.1 b.1)),
      -- `a == b` at one non-boolean type
      (2, fun _ => do
            let ty ← elements valueTypes (by decide)
            match (← candC caps (← chooseNat 0 d) ty).bind (finishC caps ty) with
            | none => return none
            | some a =>
              match (← candC caps (← chooseNat 0 d) ty).bind (finishC caps ty) with
              | none => return none
              | some b => return some (.binaryApp .eq a.1 b.1)),
      -- `a == b` at booleans
      (1, fun _ => do
            match (← candS caps (← chooseNat 0 d)).bind (finishS caps) with
            | none => return none
            | some a =>
              match (← candS caps (← chooseNat 0 d)).bind (finishS caps) with
              | none => return none
              | some b => return some (.binaryApp .eq a.1 b.1)),
      -- `a == b` at two entity types (statically `ff` when they differ)
      (1, fun _ => do
            let t₁ ← elements entityTypes (by decide)
            let t₂ ← elements entityTypes (by decide)
            match (← candC caps (← chooseNat 0 d) (.entity t₁)).bind (finishC caps (.entity t₁)) with
            | none => return none
            | some a =>
              match (← candC caps (← chooseNat 0 d) (.entity t₂)).bind (finishC caps (.entity t₂)) with
              | none => return none
              | some b => return some (.binaryApp .eq a.1 b.1)),
      -- `a == b` for two literals of possibly different kinds
      (1, fun _ => do return some (.binaryApp .eq (.lit (← genPrim)) (.lit (← genPrim))))
    ] (by simp)
partial_fixpoint

/-- Candidates at the non-boolean type `ty`. -/
def candC [Gen G] (caps : Capabilities) : Nat → CedarType → G (Option Spec.Expr)
  | 0, ty =>
    match ty with
    | .int => do return some (.lit (.int (← genInt64)))
    | .string => do return some (.lit (.string (← genString)))
    | .entity ety =>
      if ety == pType then return some (.var .principal)
      else if ety == rType then return some (.var .resource)
      else if ety == aType then return some (.var .action)
      else return none
    | .record rty => if rty == ctxTy then return some (.var .context) else return none
    | _ => return none
  | d + 1, ty =>
    frequency! [
      (3, fun _ => candC caps 0 ty),
      (2, fun _ => do
            match (← candS caps (← chooseNat 0 d)).bind (finishS caps) with
            | none => return none
            | some g =>
              match g.2.1 with
              | .tt =>
                match (← candC (caps ∪ g.2.2) (← chooseNat 0 d) ty).bind (finishC (caps ∪ g.2.2) ty) with
                | none => return none
                | some t => return some (.ite g.1 t.1 (← genAny (← chooseNat 0 d)))
              | .ff =>
                match (← candC caps (← chooseNat 0 d) ty).bind (finishC caps ty) with
                | none => return none
                | some e => return some (.ite g.1 (← genAny (← chooseNat 0 d)) e.1)
              | .anyBool =>
                match (← candC (caps ∪ g.2.2) (← chooseNat 0 d) ty).bind (finishC (caps ∪ g.2.2) ty) with
                | none => return none
                | some t =>
                  match (← candC caps (← chooseNat 0 d) ty).bind (finishC caps ty) with
                  | none => return none
                  | some e => return some (.ite g.1 t.1 e.1)),
      (2, fun _ => do genRead caps (← chooseNat 0 d) (· == ty)),
      (2, fun _ => do
            let op ← elements [BinaryOp.add, BinaryOp.sub, BinaryOp.mul] (by decide)
            match (← candC caps (← chooseNat 0 d) .int).bind (finishC caps .int) with
            | none => return none
            | some a =>
              match (← candC caps (← chooseNat 0 d) .int).bind (finishC caps .int) with
              | none => return none
              | some b => return some (.binaryApp op a.1 b.1)),
      (1, fun _ => do
            match (← candC caps (← chooseNat 0 d) .int).bind (finishC caps .int) with
            | none => return none
            | some a => return some (.unaryApp .neg a.1))
    ] (by simp)
partial_fixpoint

/-- An attribute read at a type satisfying `p`: one the capabilities in scope justify, or a required
attribute of a generated base. -/
def genRead [Gen G] (caps : Capabilities) (d : Nat) (p : CedarType → Bool) :
    G (Option Spec.Expr) :=
  oneOf! [
    fun _ =>
      match capReads caps p with
      | [] => return none
      | r :: rs => do return some (← elements (r :: rs) (by simp)).1,
    fun _ =>
      match requiredAttrs p with
      | [] => return none
      | r :: rs => do
        let q ← elements (r :: rs) (by simp)
        match (← candC caps d q.1).bind (finishC caps q.1) with
        | none => return none
        | some x => return some (.getAttr x.1 q.2.1)]
partial_fixpoint

/-- An arbitrary fragment expression, well-typed or not: what a dead branch may contain. -/
def genAny [Gen G] : Nat → G Spec.Expr
  | 0 =>
    oneOf! [
      fun _ => (Spec.Expr.lit ·) <$> genPrim,
      fun _ => (Spec.Expr.var ·) <$>
        elements [Var.principal, .action, .resource, .context] (by decide)]
  | d + 1 =>
    frequency! [
      (3, fun _ => genAny 0),
      (1, fun _ => do return .ite (← genAny (← chooseNat 0 d)) (← genAny (← chooseNat 0 d)) (← genAny (← chooseNat 0 d))),
      (1, fun _ => do return .and (← genAny (← chooseNat 0 d)) (← genAny (← chooseNat 0 d))),
      (1, fun _ => do return .or (← genAny (← chooseNat 0 d)) (← genAny (← chooseNat 0 d))),
      (1, fun _ => do
            let op ← elements ([UnaryOp.not, .neg] ++ entityTypes.map UnaryOp.is) (by simp)
            return .unaryApp op (← genAny (← chooseNat 0 d))),
      (1, fun _ => do
            let op ← elements [BinaryOp.eq, .less, .lessEq, .add, .sub, .mul] (by decide)
            return .binaryApp op (← genAny (← chooseNat 0 d)) (← genAny (← chooseNat 0 d))),
      (1, fun _ => do return .hasAttr (← genAny (← chooseNat 0 d)) (← genAttr)),
      (1, fun _ => do return .getAttr (← genAny (← chooseNat 0 d)) (← genAttr))
    ] (by simp)
partial_fixpoint

end

/-- Boolean expressions with the `BoolType` and output capabilities `typeOf` gives them. -/
def genS [Gen G] (caps : Capabilities) (d : Nat) :
    G (Option (Spec.Expr × BoolType × Capabilities)) := do
  return (← candS caps d).bind (finishS caps)

/-- Expressions of the non-boolean type `ty`, with the output capabilities `typeOf` gives them. -/
def genC [Gen G] (caps : Capabilities) (d : Nat) (ty : CedarType) :
    G (Option (Spec.Expr × Capabilities)) := do
  return (← candC caps d ty).bind (finishC caps ty)

/-! ## Properties -/

/-- Does `typeOf` derive exactly the judgment `genS` claims — the same `BoolType` and the same output
capabilities? Exactness is what composition relies on: a guard's claimed capabilities are what its
sibling is generated under. -/
def claimS (caps : Capabilities) (e : Spec.Expr) (bty : BoolType) (c' : Capabilities) : Bool :=
  match typeOf e caps env with
  | .ok (tx, c) => tx.typeOf == .bool bty && c == c'
  | .error _ => false

def claimC (caps : Capabilities) (e : Spec.Expr) (ty : CedarType) (c' : Capabilities) : Bool :=
  match typeOf e caps env with
  | .ok (tx, c) => tx.typeOf == ty && c == c'
  | .error _ => false

/-- Soundness of `genS`, exactly: every result is the judgment it claims. `none` is a discard. -/
def prop_genS_exact [Gen G] : PropM G Unit := do
  let r ← generate (genS ∅ 4)
  match r with
  | none => assume false
  | some (e, bty, c') =>
    check (claimS ∅ e bty c')
      s!"claimed {reprStr bty}/{reprStr c'}, typeOf says {reprStr ((typeOf e ∅ env).map fun p => (p.1.typeOf, p.2))} for {reprStr e}"

/-- Soundness of `genC`, exactly, at every non-boolean type of the fragment. -/
def prop_genC_exact [Gen G] : PropM G Unit := do
  let ty ← generate (elements valueTypes (by decide))
  let r ← generate (genC ∅ 4 ty)
  match r with
  | none => assume false
  | some (e, c') =>
    check (claimC ∅ e ty c')
      s!"claimed {reprStr ty}/{reprStr c'}, typeOf says {reprStr ((typeOf e ∅ env).map fun p => (p.1.typeOf, p.2))} for {reprStr e}"

/-- Cedar's `type_of_is_sound` on this generator's output, which now includes ill-typed dead
branches and capabilities from every kind of guard. -/
def prop_soundness [Gen G] : PropM G Unit := do
  -- The expression first: under `FuzzGen` draw order is byte order, and the entity store reads many
  -- bytes, so drawing it first leaves the expression's choices past the end of a short buffer.
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

end CedarTyped
