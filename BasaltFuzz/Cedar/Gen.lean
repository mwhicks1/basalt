/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import BasaltFuzz.Cedar.Wide

/-!
# A correct-by-construction generator for Cedar's typing judgment

Generates Cedar expressions together with the type and output capabilities Cedar's typechecker gives
them, over `CedarWide`'s schema, *without calling `typeOf`*. Each typing rule is a generator branch
that combines its sub-results with the typechecker's own per-rule helper (`typeOfAnd`, `typeOfIf`,
`typeOfBinaryApp`, `typeOfHasAttr`, …), exactly as `typeOf` itself combines them, so the generator
agrees with Cedar by construction and never retypechecks a subterm. A rule is offered only where it
applies (a read only when a capability or a required attribute justifies it, a type only when it is
inhabited), so no choice is ever rejected.

The helpers consult only their arguments' *types*, so a sub-result is carried as
`(expression, type, scope)` and handed to a helper as a stand-in `TypedExpr` of that type (`car`).
Capabilities record a base expression but not its type, which a later read needs, so the scope is a
list of *typed* capabilities; a helper's output capabilities are annotated from it (`annotate`).
Mathlib-free, so `basalt-fuzz` links it.
-/

namespace CedarGen

open Basalt.PBT RandomChoice
open Cedar Cedar.Data Cedar.Spec Cedar.Validation
open CedarTyped (genInt64 genString genChar genBool)
open CedarWide (env userT groupT photoT albumT actionT view read ctxTy addrTy entityTypes eids
  knownAttrs genAttr genTag genPattern attrsOf)

/-! ## Judgments -/

/-- A capability with its types: the base expression, the base's type, the key, and the type of the
attribute or tag it justifies reading. -/
abbrev TCap := Spec.Expr × CedarType × Key × CedarType

/-- The capabilities in scope, typed. -/
abbrev Scope := List TCap

def Scope.caps (s : Scope) : Capabilities := s.map fun (x, _, k, _) => (x, k)

/-- A helper's output capabilities, typed from a table of the capabilities that could appear in it:
every output capability is an input capability or one the rule itself introduced. -/
def annotate (tbl : Scope) (c : Capabilities) : Scope :=
  c.filterMap fun (x, k) => tbl.find? fun (y, _, k', _) => y == x && k' == k

/-- A generated judgment: the expression, its type, and its output capabilities, typed. -/
structure J where
  e : Spec.Expr
  ty : CedarType
  out : Scope

/-- A stand-in `TypedExpr` of type `ty`, for a helper that consults only its argument's type. -/
def car (ty : CedarType) : TypedExpr := .lit (.bool true) ty

/-- A sub-result as the `ResultType` a helper takes. -/
def J.res (j : J) : ResultType := .ok (car j.ty, j.out.caps)

/-- A helper's result as a judgment for `e`, its capabilities typed from `tbl`. `none` only if the
helper rejected, which the rules below never let happen. -/
def ofR (tbl : Scope) (e : Spec.Expr) (r : ResultType) : Option J :=
  match r with
  | .ok (tx, c) => some ⟨e, tx.typeOf, annotate tbl c⟩
  | .error _ => none

/-- A placeholder for a dead branch's result, which the helper receiving it ignores. -/
def dead : ResultType := .error .emptySetErr

/-! ## The type universe -/

def entityTys : List CedarType := entityTypes.map CedarType.entity

/-- Element types of the sets the generator builds. -/
def setElts : List CedarType := [.int, .string] ++ entityTys

/-- The non-boolean types. -/
def valueTypes : List CedarType :=
  [.int, .string] ++ entityTys ++ setElts.map CedarType.set ++
  [.record ctxTy, .record addrTy, .ext .ipAddr, .ext .decimal, .ext .datetime, .ext .duration]

/-- The attribute type of `a` in `bt`, if `bt` has it. -/
def attrTy (bt : CedarType) (a : Attr) : Option QualifiedType := (attrsOf bt).lookup a

/-- Reads the scope justifies at type `ty`: `(base, base type, attribute)`. -/
def capReads (s : Scope) (ty : CedarType) : List (Spec.Expr × CedarType × Attr) :=
  s.filterMap fun
    | (x, bt, .attr a, vt) => if vt == ty then some (x, bt, a) else none
    | _ => none

/-- Tag reads the scope justifies: `(base, base type, tag expression)`. -/
def tagReads (s : Scope) : List (Spec.Expr × CedarType × Spec.Expr) :=
  s.filterMap fun
    | (x, bt, .tag t, _) => some (x, bt, t)
    | _ => none

/-- Is a value of this type always constructible, whatever the scope? Every value type is, except a
schema record reachable only through an optional attribute (`addr`), which needs a capability. -/
def inhabited (s : Scope) (ty : CedarType) : Bool :=
  ty != .record addrTy || !(capReads s ty).isEmpty

/-- Base types for `has`, `.`, and `is` that are inhabited in this scope. -/
def baseTypes (s : Scope) : List CedarType :=
  entityTys ++ [.record ctxTy] ++ (if inhabited s (.record addrTy) then [.record addrTy] else [])

/-- Required attributes of type `ty` on an inhabited base: `(base type, attribute)`. -/
def requiredReads (s : Scope) (ty : CedarType) : List (CedarType × Attr) :=
  (baseTypes s).flatMap fun bt =>
    (attrsOf bt).filterMap fun
      | (a, .required t) => if t == ty then some (bt, a) else none
      | _ => none

/-! ## Leaves -/

/-- A valid argument for an extension constructor: usually one of a few, otherwise any string that
parses — an invalid draw is *repaired* to a valid one rather than rejected. -/
def genExtArg [Gen G] (xt : ExtType) : G String := do
  let valid : String → Bool := match xt with
    | .ipAddr => fun s => (Ext.IPAddr.ip s).isSome
    | .decimal => fun s => (Ext.Decimal.decimal s).isSome
    | .datetime => fun s => (Ext.Datetime.parse s).isSome
    | .duration => fun s => (Ext.Datetime.Duration.parse s).isSome
  let known : List String := match xt with
    | .ipAddr => ["10.0.0.1", "192.168.0.0/16", "::1", "127.0.0.1"]
    | .decimal => ["1.23", "-0.5", "12.3456", "0.0"]
    | .datetime => ["2024-01-01", "2024-01-01T12:00:00Z", "2025-06-30"]
    | .duration => ["1h", "2d30m", "-1s", "90m"]
  let fallback := known.headD ""
  frequency! [
    (9, fun _ => elements (fallback :: known) (by simp)),
    (1, fun _ => do let s ← genString; return if valid s then s else fallback)
  ] (by simp)

def ctorOf : ExtType → ExtFun
  | .ipAddr => .ip | .decimal => .decimal | .datetime => .datetime | .duration => .duration

/-- An entity identifier valid for the type: any `eid` for a standard entity type, an action for the
action type. -/
def genUID [Gen G] (ety : EntityType) : G EntityUID :=
  if ety == actionT then elements [view, read] (by decide)
  else do
    let e ← frequency! [(8, fun _ => elements eids (by decide)), (1, fun _ => genString)] (by simp)
    return ⟨ety, e⟩

/-- Any `EntityType` name, for `is`: usually one of the schema's. -/
def genName [Gen G] : G EntityType :=
  frequency! [(8, fun _ => elements entityTypes (by decide)),
              (1, fun _ => do return ⟨← genString, []⟩)] (by simp)

/-- A literal that typechecks: any boolean, integer, or string, or a valid entity identifier. -/
def genPrim [Gen G] : G Prim :=
  oneOf! [
    fun _ => (Prim.bool ·) <$> genBool,
    fun _ => (Prim.int ·) <$> genInt64,
    fun _ => (Prim.string ·) <$> genString,
    fun _ => do return .entityUID (← genUID (← elements entityTypes (by decide)))]

/-! ## The generators

Structural recursion on fuel as a family (`CedarWide`'s shape): the rules at fuel `d + 1` take the
family at `d`. A rule builds its expression from sub-results and gets its judgment from the helper
`typeOf` would use for that constructor. -/

structure Fam (G : Type → Type) where
  /-- Boolean judgments. -/
  bool : Scope → G (Option J)
  /-- Judgments at an inhabited non-boolean type. -/
  atTy : Scope → CedarType → G (Option J)
  /-- Anything, for dead branches. -/
  any : G Spec.Expr

section
variable [Gen G] (f : Fam G) (s : Scope)

/-- Choose among weighted alternatives, the first always applicable. -/
def pick (first : Nat × (Unit → G α)) (rest : List (Nat × (Unit → G α))) (h : 0 < first.1) : G α :=
  frequency (first :: rest) (by simp; omega)

/-- A leaf at a non-boolean type, which every inhabited type has. -/
def leaf (ty : CedarType) : G (Option J) :=
  match ty with
  | .int => do let p := Prim.int (← genInt64); return ofR s (.lit p) (typeOfLit p env)
  | .string => do let p := Prim.string (← genString); return ofR s (.lit p) (typeOfLit p env)
  | .entity ety => do
    let p := Prim.entityUID (← genUID ety)
    let var : Option Var :=
      if ety == userT then some .principal else if ety == photoT then some .resource
      else if ety == actionT then some .action else none
    match var with
    | some v => oneOf! [fun _ => pure (ofR s (.var v) (typeOfVar v env)),
                        fun _ => pure (ofR s (.lit p) (typeOfLit p env))]
    | none => return ofR s (.lit p) (typeOfLit p env)
  | .set elt => do
    match (← leaf' elt) with
    | some x => return ofR s (.set [x.e]) (typeOfSet [car x.ty])
    | none => return none
  | .record rty =>
    if rty == ctxTy then return ofR s (.var .context) (typeOfVar .context env)
    else match capReads s ty with
      | r :: rs => do
        let q ← elements (r :: rs) (by simp)
        return ofR s (.getAttr q.1 q.2.2) (typeOfGetAttr (car q.2.1) q.1 q.2.2 s.caps env)
      | [] => return none
  | .ext xt => do
    let arg := Spec.Expr.lit (.string (← genExtArg xt))
    return ofR s (.call (ctorOf xt) [arg]) (typeOfCall (ctorOf xt) [car .string] [arg])
  | _ => return none
where
  /-- A leaf at a set's element type. -/
  leaf' (elt : CedarType) : G (Option J) :=
    match elt with
    | .int => do let p := Prim.int (← genInt64); return ofR s (.lit p) (typeOfLit p env)
    | .string => do let p := Prim.string (← genString); return ofR s (.lit p) (typeOfLit p env)
    | .entity ety => do let p := Prim.entityUID (← genUID ety); return ofR s (.lit p) (typeOfLit p env)
    | _ => return none

/-- `a && b`: an `ff` left operand leaves `b` untyped; otherwise `b` is generated under
`scope ∪ out(a)`, as `typeOf` types it under `c ∪ c₁`. -/
def ruleAnd : G (Option J) := do
  match (← f.bool s) with
  | none => return none
  | some a =>
    if a.ty == .bool .ff then
      return ofR (s ++ a.out) (.and a.e (← f.any)) (typeOfAnd (car a.ty, a.out.caps) dead)
    else
      match (← f.bool (s ∪ a.out)) with
      | none => return none
      | some b => return ofR (s ++ a.out ++ b.out) (.and a.e b.e)
                    (typeOfAnd (car a.ty, a.out.caps) b.res)

/-- `a || b`: a `tt` left operand leaves `b` untyped; `b` is generated under `scope` alone. -/
def ruleOr : G (Option J) := do
  match (← f.bool s) with
  | none => return none
  | some a =>
    if a.ty == .bool .tt then
      return ofR (s ++ a.out) (.or a.e (← f.any)) (typeOfOr (car a.ty, a.out.caps) dead)
    else
      match (← f.bool s) with
      | none => return none
      | some b => return ofR (s ++ a.out ++ b.out) (.or a.e b.e) (typeOfOr (car a.ty, a.out.caps) b.res)

/-- `if g then t else e`, a branch generated by `branch`; the guard's capabilities reach the *then*
branch only, and a singleton guard leaves the other branch untyped. -/
def ruleIte (branch : Scope → G (Option J)) : G (Option J) := do
  match (← f.bool s) with
  | none => return none
  | some g =>
    let r₁ := (car g.ty, g.out.caps)
    if g.ty == .bool .tt then
      match (← branch (s ∪ g.out)) with
      | none => return none
      | some t => return ofR (s ++ g.out ++ t.out) (.ite g.e t.e (← f.any)) (typeOfIf r₁ t.res dead)
    else if g.ty == .bool .ff then
      match (← branch s) with
      | none => return none
      | some e => return ofR (s ++ e.out) (.ite g.e (← f.any) e.e) (typeOfIf r₁ dead e.res)
    else
      match (← branch (s ∪ g.out)) with
      | none => return none
      | some t =>
        match (← branch s) with
        | none => return none
        | some e => return ofR (s ++ g.out ++ t.out ++ e.out) (.ite g.e t.e e.e)
                      (typeOfIf r₁ t.res e.res)

/-- A binary application at operand types `ty₁`, `ty₂`, typed by `typeOfBinaryApp`. -/
def binary (op : BinaryOp) (ty₁ ty₂ : CedarType) : G (Option J) := do
  match (← f.atTy s ty₁) with
  | none => return none
  | some a =>
    match (← f.atTy s ty₂) with
    | none => return none
    | some b => return ofR s (.binaryApp op a.e b.e)
                  (typeOfBinaryApp op (car a.ty) (car b.ty) a.e b.e s.caps env)

/-- `x has a`: the source of attribute capabilities. The new capability is typed from the schema. -/
def ruleHas : G (Option J) := do
  let bt ← elements (baseTypes s) (by simp [baseTypes, entityTys, entityTypes])
  match (← f.atTy s bt) with
  | none => return none
  | some x =>
    let a ← genAttr
    let new : Scope := match attrTy bt a with
      | some q => [(x.e, bt, .attr a, q.getType)]
      | none => []
    return ofR (s ++ new) (.hasAttr x.e a) (typeOfHasAttr (car bt) x.e a s.caps env)

/-- `x hasTag t`: the source of tag capabilities. -/
def ruleHasTag : G (Option J) := do
  let ety ← elements entityTypes (by decide)
  match (← f.atTy s (.entity ety)) with
  | none => return none
  | some x =>
    match (← f.atTy s .string) with
    | none => return none
    | some t =>
      let new : Scope := match env.ets.tags? ety with
        | some (some tt) => [(x.e, .entity ety, .tag t.e, tt)]
        | _ => []
      return ofR (s ++ new) (.binaryApp .hasTag x.e t.e)
        (typeOfBinaryApp .hasTag (car x.ty) (car .string) x.e t.e s.caps env)

/-- A read at `ty`, from a capability in scope or a required attribute of a generated base. Offered
only when one exists (`readable`). -/
def ruleRead (ty : CedarType) : G (Option J) :=
  match capReads s ty, requiredReads s ty with
  | [], [] => return none
  | c :: cs, [] => capRead (c :: cs) (by simp)
  | [], r :: rs => reqRead (r :: rs) (by simp)
  | c :: cs, r :: rs => oneOf! [fun _ => capRead (c :: cs) (by simp), fun _ => reqRead (r :: rs) (by simp)]
where
  capRead (cs : List (Spec.Expr × CedarType × Attr)) (h : cs ≠ []) : G (Option J) := do
    let q ← elements cs h
    return ofR s (.getAttr q.1 q.2.2) (typeOfGetAttr (car q.2.1) q.1 q.2.2 s.caps env)
  reqRead (rs : List (CedarType × Attr)) (h : rs ≠ []) : G (Option J) := do
    let q ← elements rs h
    match (← f.atTy s q.1) with
    | none => return none
    | some x => return ofR s (.getAttr x.e q.2) (typeOfGetAttr (car q.1) x.e q.2 s.caps env)

def readable (ty : CedarType) : Bool := !(capReads s ty).isEmpty || !(requiredReads s ty).isEmpty

/-- A record literal of one to three fields with distinct names, each a judgment at a generated type
(booleans included). Its type is `typeOf`'s for a record literal: each field required, at its type. -/
def recordLit (need : Option (Attr × CedarType)) : G (Option (Spec.Expr × CedarType)) := do
  let n ← chooseNat 0 2
  let field (ty : CedarType) : G (Option J) :=
    match ty with
    | .bool _ => f.bool s
    | _ => f.atTy s ty
  let pickTy : G CedarType := elements (CedarType.bool .anyBool :: valueTypes.filter (inhabited s))
    (by simp)
  let mut fs : List (Attr × J) := []
  if let some (a, ty) := need then
    match (← field ty) with
    | some j => fs := [(a, j)]
    | none => return none
  for _ in [0:n] do
    let a ← genAttr
    if fs.any (·.1 == a) then continue
    match (← field (← pickTy)) with
    | some j => fs := fs ++ [(a, j)]
    | none => pure ()
  if fs.isEmpty then
    match (← field .int) with
    | some j => fs := [("f", j)]
    | none => return none
  let rty : RecordType := Map.make (fs.map fun (a, j) => (a, Qualified.required j.ty))
  return some (.record (fs.map fun (a, j) => (a, j.e)), .record rty)

/-- `{…} has a`: `a` a field of the literal (`tt`) or not (`ff`). -/
def ruleRecordHas : G (Option J) := do
  match (← recordLit f s none) with
  | none => return none
  | some (r, rty) =>
    let a ← genAttr
    return ofR s (.hasAttr r a) (typeOfHasAttr (car rty) r a s.caps env)

/-- `{…, a: v, …}.a`, reading the field built at the wanted type. -/
def ruleRecordGet (ty : CedarType) : G (Option J) := do
  let a ← genAttr
  match (← recordLit f s (some (a, ty))) with
  | none => return none
  | some (r, rty) => return ofR s (.getAttr r a) (typeOfGetAttr (car rty) r a s.caps env)

/-- `x has a.b`, the multi-attribute form, typed by Cedar's `typeOfExtHasAttr`. Continuing the chain
past `a` needs `a` to be an entity or record attribute (or absent, which short-circuits to `ff`), so
`a` is drawn from those; the capabilities the chain earns are typed from the schema. -/
def ruleExtHas : G (Option J) := do
  let bt ← elements (baseTypes s) (by simp [baseTypes, entityTys, entityTypes])
  match (← f.atTy s bt) with
  | none => return none
  | some x =>
    let viaAttrs := (attrsOf bt).filterMap fun (a, q) =>
      match q.getType with
      | .entity _ | .record _ => some a
      | _ => none
    let a ← match viaAttrs with
      | [] => pure "zzz"
      | v :: vs => frequency! [(4, fun _ => elements (v :: vs) (by simp)),
                               (1, fun _ => pure "zzz")] (by simp)
    let b ← genAttr
    let ta := (attrTy bt a).map Qualified.getType
    let new : Scope := match ta with
      | some t => [(x.e, bt, .attr a, t)] ++ (match attrTy t b with
          | some q => [(.getAttr x.e a, t, .attr b, q.getType)]
          | none => [])
      | none => []
    match typeOfExtHasAttr (car bt) x.e [a, b] s.caps env with
    | .ok (bty, c) => return some ⟨.extHasAttr x.e a [b], .bool bty, annotate (s ++ new) c⟩
    | .error _ => return none

/-- Boolean rules. Every one applies in every scope except reads, which are offered only when some
read of a boolean exists. -/
def stepBool : G (Option J) :=
  let reads : List (Nat × (Unit → G (Option J))) :=
    [.bool .anyBool].filterMap fun ty => if readable s ty then some (1, fun _ => ruleRead f s ty) else none
  pick (2, fun _ => do let p := Prim.bool (← genBool); return ofR s (.lit p) (typeOfLit p env)) (([
    (4, fun _ => ruleAnd f s),
    (2, fun _ => ruleOr f s),
    (2, fun _ => ruleIte f s fun s' => f.bool s'),
    (4, fun _ => ruleHas f s),
    (2, fun _ => ruleHasTag f s),
    (1, fun _ => do
          match (← f.bool s) with
          | none => return none
          | some a => return ofR s (.unaryApp .not a.e) (typeOfUnaryApp .not (car a.ty))),
    (1, fun _ => do
          let bt ← elements entityTys (by simp [entityTys, entityTypes])
          let ety ← genName
          match (← f.atTy s bt) with
          | none => return none
          | some x => return ofR s (.unaryApp (.is ety) x.e) (typeOfUnaryApp (.is ety) (car bt))),
    (2, fun _ => do
          let op ← elements [BinaryOp.less, BinaryOp.lessEq] (by decide)
          let ty ← elements [CedarType.int, .ext .datetime, .ext .duration] (by decide)
          binary f s op ty ty),
    (3, fun _ => do
          let ty ← elements ((valueTypes.filter (inhabited s)).headD .int :: valueTypes.filter (inhabited s))
                    (by simp)
          binary f s .eq ty ty),
    (1, fun _ => do
          match (← f.bool s) with
          | none => return none
          | some a =>
            match (← f.bool s) with
            | none => return none
            | some b => return ofR s (.binaryApp .eq a.e b.e)
                          (typeOfBinaryApp .eq (car a.ty) (car b.ty) a.e b.e s.caps env)),
    (1, fun _ => do
          let t₁ ← elements entityTys (by simp [entityTys, entityTypes])
          let t₂ ← elements entityTys (by simp [entityTys, entityTypes])
          binary f s .eq t₁ t₂),
    (1, fun _ => do
          let p₁ := Spec.Expr.lit (← genPrim)
          let p₂ := Spec.Expr.lit (← genPrim)
          let ty (p : Spec.Expr) : CedarType := match p with
            | .lit (.bool _) => .bool .anyBool | .lit (.int _) => .int | .lit (.string _) => .string
            | .lit (.entityUID u) => .entity u.ty | _ => .int
          return ofR s (.binaryApp .eq p₁ p₂) (typeOfBinaryApp .eq (car (ty p₁)) (car (ty p₂)) p₁ p₂ s.caps env)),
    (3, fun _ => do
          let t₁ ← elements entityTys (by simp [entityTys, entityTypes])
          let t₂ ← elements entityTys (by simp [entityTys, entityTypes])
          let rhs ← elements [t₂, .set t₂] (by simp)
          binary f s .mem t₁ rhs),
    (2, fun _ => do
          let ty ← elements setElts (by simp [setElts])
          binary f s .contains (.set ty) ty),
    (2, fun _ => do
          let ty ← elements setElts (by simp [setElts])
          let op ← elements [BinaryOp.containsAll, BinaryOp.containsAny] (by decide)
          binary f s op (.set ty) (.set ty)),
    (1, fun _ => do
          let ty ← elements setElts (by simp [setElts])
          match (← f.atTy s (.set ty)) with
          | none => return none
          | some x => return ofR s (.unaryApp .isEmpty x.e) (typeOfUnaryApp .isEmpty (car x.ty))),
    (1, fun _ => do
          let p ← genPattern
          match (← f.atTy s .string) with
          | none => return none
          | some x => return ofR s (.unaryApp (.like p) x.e) (typeOfUnaryApp (.like p) (car .string))),
    (2, fun _ => do
          let fn ← elements [ExtFun.isIpv4, .isIpv6, .isLoopback, .isMulticast] (by decide)
          match (← f.atTy s (.ext .ipAddr)) with
          | none => return none
          | some x => return ofR s (.call fn [x.e]) (typeOfCall fn [car x.ty] [x.e])),
    (1, fun _ => do
          match (← f.atTy s (.ext .ipAddr)) with
          | none => return none
          | some x =>
            match (← f.atTy s (.ext .ipAddr)) with
            | none => return none
            | some y => return ofR s (.call .isInRange [x.e, y.e])
                          (typeOfCall .isInRange [car x.ty, car y.ty] [x.e, y.e])),
    (1, fun _ => do
          let fn ← elements [ExtFun.lessThan, .lessThanOrEqual, .greaterThan, .greaterThanOrEqual]
            (by decide)
          match (← f.atTy s (.ext .decimal)) with
          | none => return none
          | some x =>
            match (← f.atTy s (.ext .decimal)) with
            | none => return none
            | some y => return ofR s (.call fn [x.e, y.e]) (typeOfCall fn [car x.ty, car y.ty] [x.e, y.e]))
,
    (1, fun _ => ruleRecordHas f s),
    (1, fun _ => ruleExtHas f s),
    (1, fun _ => ruleRecordGet f s (.bool .anyBool))
  ] : List (Nat × (Unit → G (Option J)))) ++ reads) (by simp)

/-- Rules specific to a target type. -/
def construct (ty : CedarType) : List (Nat × (Unit → G (Option J))) :=
  match ty with
  | .int => [
      (2, fun _ => do
            let op ← elements [BinaryOp.add, BinaryOp.sub, BinaryOp.mul] (by decide)
            binary f s op .int .int),
      (1, fun _ => do
            match (← f.atTy s .int) with
            | none => return none
            | some a => return ofR s (.unaryApp .neg a.e) (typeOfUnaryApp .neg (car .int))),
      (1, fun _ => do
            let fn ← elements [ExtFun.toMilliseconds, .toSeconds, .toMinutes, .toHours, .toDays]
              (by decide)
            match (← f.atTy s (.ext .duration)) with
            | none => return none
            | some x => return ofR s (.call fn [x.e]) (typeOfCall fn [car x.ty] [x.e]))]
  | .string =>
    match tagReads s with
    | [] => []
    | r :: rs => [(2, fun _ => do
        let q ← elements (r :: rs) (by simp)
        return ofR s (.binaryApp .getTag q.1 q.2.2)
          (typeOfBinaryApp .getTag (car q.2.1) (car .string) q.1 q.2.2 s.caps env))]
  | .set elt => [
      (3, fun _ => do
            let n ← chooseNat 1 3
            let x₁ ← f.atTy s elt
            let x₂ ← f.atTy s elt
            let x₃ ← f.atTy s elt
            let xs := ([x₁, x₂, x₃].take n).filterMap id
            return ofR s (.set (xs.map (·.e))) (typeOfSet (xs.map (car ·.ty))))]
  | .ext .datetime => [
      (1, fun _ => do
            match (← f.atTy s (.ext .datetime)) with
            | none => return none
            | some x =>
              match (← f.atTy s (.ext .duration)) with
              | none => return none
              | some y => return ofR s (.call .offset [x.e, y.e])
                            (typeOfCall .offset [car x.ty, car y.ty] [x.e, y.e])),
      (1, fun _ => do
            match (← f.atTy s (.ext .datetime)) with
            | none => return none
            | some x => return ofR s (.call .toDate [x.e]) (typeOfCall .toDate [car x.ty] [x.e]))]
  | .ext .duration => [
      (1, fun _ => do
            match (← f.atTy s (.ext .datetime)) with
            | none => return none
            | some x =>
              match (← f.atTy s (.ext .datetime)) with
              | none => return none
              | some y => return ofR s (.call .durationSince [x.e, y.e])
                            (typeOfCall .durationSince [car x.ty, car y.ty] [x.e, y.e])),
      (1, fun _ => do
            match (← f.atTy s (.ext .datetime)) with
            | none => return none
            | some x => return ofR s (.call .toTime [x.e]) (typeOfCall .toTime [car x.ty] [x.e]))]
  | _ => []

/-- Rules at an inhabited non-boolean type: a leaf, a conditional, a read if one exists, and the
type's own constructions. -/
def stepAt (ty : CedarType) : G (Option J) :=
  pick (3, fun _ => leaf s ty) (([(2, fun _ => ruleIte f s fun s' => f.atTy s' ty)] :
      List (Nat × (Unit → G (Option J)))) ++
    (if readable s ty then [(3, fun _ => ruleRead f s ty)] else []) ++
    [(1, fun _ => ruleRecordGet f s ty)] ++ construct f s ty) (by simp)

def stepAny : G Spec.Expr :=
  frequency! [
    (3, fun _ => oneOf! [
          fun _ => (Spec.Expr.lit ·) <$> CedarWide.genPrim,
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

/-- The family at fuel `d`. At fuel `0`, leaves only (a boolean literal, a leaf at each type). -/
def fam [Gen G] : Nat → Fam G
  | 0 => { bool := fun _ => do
             let p := Prim.bool (← genBool)
             return ofR [] (.lit p) (typeOfLit p env),
           atTy := fun s ty => leaf s ty,
           any := (Spec.Expr.lit ·) <$> CedarWide.genPrim }
  | d + 1 =>
    let f := fam d
    { bool := stepBool f, atTy := stepAt f, any := stepAny f }

/-- A boolean judgment at fuel `d`, under no capabilities. -/
def genS [Gen G] (d : Nat) : G (Option J) := (fam d).bool []

/-! ## Properties -/

/-- Does the real typechecker agree with the judgment the generator computed, exactly — type and
capabilities? The generator never calls `typeOf`; this checks it. -/
def agrees (j : J) : Bool :=
  match typeOf j.e ∅ env with
  | .ok (tx, c) => tx.typeOf == j.ty && c == j.out.caps
  | .error _ => false

/-- The generator never rejects (no `none`) and its computed judgment is exactly `typeOf`'s. -/
def prop_correct_by_construction [Gen G] : PropM G Unit := do
  let r ← generate (genS 4)
  match r with
  | none => check false "the generator returned none"
  | some j =>
    check (agrees j) s!"judgment disagrees with typeOf for {reprStr j.e}: claimed {reprStr j.ty}, \
      typeOf says {reprStr ((typeOf j.e ∅ env).map fun p => (p.1.typeOf, p.2))}"

/-- Cedar's `type_of_is_sound`, generating the expression first, with the `BASALT_H` trace
(`CedarWide.prop_soundness_traced`'s shape). -/
def prop_soundness_traced [Gen G] : PropM G Unit := do
  let r ← generate (genS 4)
  let req ← generate CedarWide.genRequest
  let es ← generate CedarWide.genEntities
  let e := match r with | some j => j.e | none => .lit (.bool true)
  let he := hash (reprStr e)
  let hi := mixHash he (mixHash (hash (reprStr req)) (hash (reprStr es.toList)))
  check (dbgTrace s!"BASALT_H {he} {hi}" fun _ => true)
  assume (requestMatchesEnvironment env req)
  assume (CedarWide.entitiesOk es)
  match typeOf e ∅ env with
  | .error _ => check false s!"ill-typed: {reprStr e}"
  | .ok (tx, _) =>
    check (CedarWide.soundOutcome e req es tx)
      s!"UNSOUND: {reprStr e} evaluated to {reprStr (evaluate e req es)}"

end CedarGen
