/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import BasaltFuzz.Cedar.Wide

/-!
# A correct-by-construction generator for Cedar's typing judgment

Generates Cedar expressions with the type and output capabilities Cedar's typechecker gives them,
over `CedarWide`'s schema, *without calling `typeOf`*. Each typing rule is a generator branch that
combines its sub-results with the typechecker's own per-rule helper (`typeOfAnd`, `typeOfIf`,
`typeOfBinaryApp`, `typeOfHasAttr`, `typeOfExtHasAttr`, …) exactly as `typeOf` combines them, and a
rule is offered only where it applies, so no choice is ever rejected.

Capabilities are tracked exactly as `typeOf` computes them. A read justified by a capability is
offered only through a *path* — a variable or literal followed by attribute reads — every optional
step of which is itself justified in the current scope (`pathOK`). That condition is what makes such a
read typecheck, and it cannot be weakened to "the base typechecked when the capability was made":
Cedar's typechecker is not monotone in capabilities (`CEDAR.md`), so a base can typecheck under the
capabilities where it was generated and fail under the larger set where it is read.

Every size — set elements, record fields, `like` patterns, the multi-attribute `has` chain — grows with
the fuel, so each is unbounded in the limit. Mathlib-free, so `basalt-fuzz` links it.
-/

namespace CedarGen

open Basalt.PBT RandomChoice
open Cedar Cedar.Data Cedar.Spec Cedar.Validation
open CedarTyped (genInt64 genString genChar genBool)
open CedarWide (env userT groupT photoT albumT actionT view read ctxTy addrTy entityTypes eids
  genAttr attrsOf)

/-! ## Judgments -/

/-- A generated judgment: the expression, the typed expression `typeOf` gives it, and its output
capabilities. Every sub-result is exactly `typeOf`'s for that subterm, so the helper combining them
computes exactly what `typeOf` computes for the whole. -/
structure J where
  e : Spec.Expr
  tx : TypedExpr
  out : Capabilities

def J.ty (j : J) : CedarType := j.tx.typeOf

/-- A sub-result as the `ResultType` a helper takes. -/
def J.res (j : J) : ResultType := .ok (j.tx, j.out)

/-- A helper's result as a judgment for `e`. `none` only if the helper rejected, which the rules
below never let happen. -/
def ofR (e : Spec.Expr) (r : ResultType) : Option J :=
  match r with
  | .ok (tx, c) => some ⟨e, tx, c⟩
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

/-- The attribute `a` of type `bt`, looked up as `typeOfGetAttr`/`typeOfHasAttr` look it up. -/
def attrTy (bt : CedarType) (a : Attr) : Option QualifiedType :=
  match bt with
  | .record rty => rty.find? a
  | .entity ety => (env.ets.attrs? ety).bind (·.find? a)
  | _ => none

/-! ## Paths -/

/-- The typed expression of a path — a variable or literal followed by attribute reads — under `c`,
computed with the helpers `typeOf` uses for these constructors (`typeOfVar`, `typeOfLit`,
`typeOfGetAttr`). `none` if it is not a path or does not typecheck under `c`, which for a path means
an optional step is not justified by a capability in `c`. -/
def pathTx (c : Capabilities) : Spec.Expr → Option TypedExpr
  | .var v => match typeOfVar v env with
    | .ok (tx, _) => some tx
    | .error _ => none
  | .lit p => match typeOfLit p env with
    | .ok (tx, _) => some tx
    | .error _ => none
  | .getAttr p a => do
    let tp ← pathTx c p
    match typeOfGetAttr tp p a c env with
    | .ok (tx, _) => some tx
    | .error _ => none
  | _ => none

/-- Reads the capabilities justify at type `ty`: `(base, its typed expression, attribute)`, the base a
path that typechecks under `c`. -/
def capReads (c : Capabilities) (ty : CedarType) : List (Spec.Expr × TypedExpr × Attr) :=
  c.filterMap fun
    | (x, .attr a) =>
      match pathTx c x with
      | some tx => match attrTy tx.typeOf a with
        | some q => if q.getType == ty then some (x, tx, a) else none
        | none => none
      | none => none
    | _ => none

/-- Tag reads the capabilities justify: `(base, typed base, tag, typed tag)`, base and tag both paths
that typecheck under `c`, the tag a string and the base's tags strings. -/
def tagReads (c : Capabilities) : List (Spec.Expr × TypedExpr × Spec.Expr × TypedExpr) :=
  c.filterMap fun
    | (x, .tag t) =>
      match pathTx c x, pathTx c t with
      | some tx, some tt =>
        match tx.typeOf with
        | .entity ety =>
          if tt.typeOf == .string && env.ets.tags? ety == some (some .string) then
            some (x, tx, t, tt) else none
        | _ => none
      | _, _ => none
    | _ => none

/-- Can the generator build a value of this type under `c`? Every value type can, except a schema
record reachable only through an optional attribute (`addr`), which needs a capability read. -/
def inhabited (c : Capabilities) (ty : CedarType) : Bool :=
  ty != .record addrTy || !(capReads c ty).isEmpty

/-- Base types for `has`, `.`, and the multi-attribute `has` that are inhabited under `c`. -/
def baseTypes (c : Capabilities) : List CedarType :=
  entityTys ++ [.record ctxTy] ++ (if inhabited c (.record addrTy) then [.record addrTy] else [])

/-- Required attributes of type `ty` on an inhabited base, `(base type, attribute)`: readable without a
capability (`getAttrInRecord`'s `.required` case). -/
def requiredReads (c : Capabilities) (ty : CedarType) : List (CedarType × Attr) :=
  (baseTypes c).flatMap fun bt =>
    (attrsOf bt).filterMap fun (a, _) =>
      match attrTy bt a with
      | some (.required t) => if t == ty then some (bt, a) else none
      | _ => none

/-! ## Leaves, each complete over its values -/

/-- A valid argument for an extension constructor: usually one of a few, otherwise any string that
parses — an invalid draw is *repaired* to a valid one rather than rejected, so every valid string is
reachable and no invalid one is produced. -/
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

/-- An entity identifier valid for the type: any `eid` for a standard entity type (every one is
valid), an action for the action type. -/
def genUID [Gen G] (ety : EntityType) : G EntityUID :=
  if ety == actionT then elements [view, read] (by decide)
  else do
    let e ← frequency! [(8, fun _ => elements eids (by decide)), (1, fun _ => genString)] (by simp)
    return ⟨ety, e⟩

/-- Any `EntityType` name, for `is`: usually one of the schema's. -/
def genName [Gen G] : G EntityType :=
  frequency! [(8, fun _ => elements entityTypes (by decide)),
              (1, fun _ => do return ⟨← genString, ← listOf genString⟩)] (by simp)

/-- A literal that typechecks: any boolean, integer, or string, or a valid entity identifier. -/
def genPrim [Gen G] : G Prim :=
  oneOf! [
    fun _ => (Prim.bool ·) <$> genBool,
    fun _ => (Prim.int ·) <$> genInt64,
    fun _ => (Prim.string ·) <$> genString,
    fun _ => do return .entityUID (← genUID (← elements entityTypes (by decide)))]

/-- A `like` pattern of at most `n` elements. -/
def genPattern [Gen G] : Nat → G Pattern
  | 0 => return []
  | n + 1 =>
    oneOf! [fun _ => return [],
            fun _ => do
              let p ← oneOf! [fun _ => pure PatElem.star, fun _ => PatElem.justChar <$> genChar]
              return p :: (← genPattern n)]

/-- Any fragment syntax, well-typed or not, for dead branches, at nesting depth at most `d`. -/
def genAny [Gen G] : Nat → G Spec.Expr
  | 0 =>
    oneOf! [
      fun _ => (Spec.Expr.lit ·) <$> CedarWide.genPrim,
      fun _ => (Spec.Expr.var ·) <$>
        elements [Var.principal, .action, .resource, .context] (by decide)]
  | d + 1 =>
    frequency! [
      (3, fun _ => genAny 0),
      (1, fun _ => do return .ite (← genAny d) (← genAny d) (← genAny d)),
      (1, fun _ => do return .and (← genAny d) (← genAny d)),
      (1, fun _ => do return .or (← genAny d) (← genAny d)),
      (1, fun _ => do
            let op ← elements [UnaryOp.not, .neg, .isEmpty] (by decide)
            return .unaryApp op (← genAny d)),
      (1, fun _ => do
            let op ← elements [BinaryOp.eq, .mem, .hasTag, .getTag, .less, .lessEq, .add, .sub, .mul,
              .contains, .containsAll, .containsAny] (by decide)
            return .binaryApp op (← genAny d) (← genAny d)),
      (1, fun _ => do return .hasAttr (← genAny d) (← genAttr)),
      (1, fun _ => do return .getAttr (← genAny d) (← genAttr)),
      (1, fun _ => do return .set [← genAny d]),
      (1, fun _ => do return .record [(← genAttr, ← genAny d)]),
      (1, fun _ => do return .call (← elements [ExtFun.ip, .decimal, .isIpv4, .offset] (by decide))
                         [← genAny d])
    ] (by simp)

/-! ## The generators

Structural recursion on fuel as a family: the rules at fuel `d + 1` take the family at `d`. -/

/-- The generators at one fuel level. -/
structure Fam (G : Type → Type) where
  /-- Boolean judgments. -/
  bool : Capabilities → G (Option J)
  /-- Judgments at an inhabited non-boolean type. -/
  atTy : Capabilities → CedarType → G (Option J)
  /-- Anything, for dead branches. -/
  any : G Spec.Expr
  /-- The fuel, which bounds the sizes of lists the rules build. -/
  fuel : Nat

section
variable [Gen G] (f : Fam G) (c : Capabilities)

/-- Choose among weighted alternatives, the first always applicable. -/
def pick (first : Nat × (Unit → G α)) (rest : List (Nat × (Unit → G α))) (h : 0 < first.1) : G α :=
  frequency (first :: rest) (by simp; omega)

/-- A leaf at an inhabited non-boolean type: a literal, a variable, an extension constructor, a
singleton set, or (for `addr`) a capability read. -/
def leaf (ty : CedarType) : G (Option J) :=
  match ty with
  | .int => do let p := Prim.int (← genInt64); return ofR (.lit p) (typeOfLit p env)
  | .string => do let p := Prim.string (← genString); return ofR (.lit p) (typeOfLit p env)
  | .entity ety => do
    let p := Prim.entityUID (← genUID ety)
    let var : Option Var :=
      if ety == userT then some .principal else if ety == photoT then some .resource
      else if ety == actionT then some .action else none
    match var with
    | some v => oneOf! [fun _ => pure (ofR (.var v) (typeOfVar v env)),
                        fun _ => pure (ofR (.lit p) (typeOfLit p env))]
    | none => return ofR (.lit p) (typeOfLit p env)
  | .set elt => do
    match (← leaf elt) with
    | some x => return ofR (.set [x.e]) (typeOfSet [x.tx])
    | none => return none
  | .record rty =>
    if rty == ctxTy then return ofR (.var .context) (typeOfVar .context env)
    else match capReads c ty with
      | r :: rs => do
        let q ← elements (r :: rs) (by simp)
        return ofR (.getAttr q.1 q.2.2) (typeOfGetAttr q.2.1 q.1 q.2.2 c env)
      | [] => return none
  | .ext xt => do
    let p := Prim.string (← genExtArg xt)
    match typeOfLit p env with
    | .ok (targ, _) => return ofR (.call (ctorOf xt) [.lit p]) (typeOfCall (ctorOf xt) [targ] [.lit p])
    | .error _ => return none
  | _ => return none

/-- `a && b`: an `ff` left operand leaves `b` untyped; otherwise `b` is generated under `c ∪ out(a)`,
as `typeOf` types it. -/
def ruleAnd : G (Option J) := do
  match (← f.bool c) with
  | none => return none
  | some a =>
    if a.ty == .bool .ff then
      return ofR (.and a.e (← f.any)) (typeOfAnd (a.tx, a.out) dead)
    else
      match (← f.bool (c ∪ a.out)) with
      | none => return none
      | some b => return ofR (.and a.e b.e) (typeOfAnd (a.tx, a.out) b.res)

/-- `a || b`: a `tt` left operand leaves `b` untyped; `b` is generated under `c` alone. -/
def ruleOr : G (Option J) := do
  match (← f.bool c) with
  | none => return none
  | some a =>
    if a.ty == .bool .tt then
      return ofR (.or a.e (← f.any)) (typeOfOr (a.tx, a.out) dead)
    else
      match (← f.bool c) with
      | none => return none
      | some b => return ofR (.or a.e b.e) (typeOfOr (a.tx, a.out) b.res)

/-- `if g then t else e`, a branch generated by `branch`; the guard's capabilities reach the *then*
branch only, and a singleton guard leaves the other branch untyped. -/
def ruleIte (branch : Capabilities → G (Option J)) : G (Option J) := do
  match (← f.bool c) with
  | none => return none
  | some g =>
    let r₁ := (g.tx, g.out)
    if g.ty == .bool .tt then
      match (← branch (c ∪ g.out)) with
      | none => return none
      | some t => return ofR (.ite g.e t.e (← f.any)) (typeOfIf r₁ t.res dead)
    else if g.ty == .bool .ff then
      match (← branch c) with
      | none => return none
      | some e => return ofR (.ite g.e (← f.any) e.e) (typeOfIf r₁ dead e.res)
    else
      match (← branch (c ∪ g.out)) with
      | none => return none
      | some t =>
        match (← branch c) with
        | none => return none
        | some e => return ofR (.ite g.e t.e e.e) (typeOfIf r₁ t.res e.res)

/-- A binary application at operand types `ty₁`, `ty₂`, typed by `typeOfBinaryApp`. -/
def binary (op : BinaryOp) (ty₁ ty₂ : CedarType) : G (Option J) := do
  match (← f.atTy c ty₁) with
  | none => return none
  | some a =>
    match (← f.atTy c ty₂) with
    | none => return none
    | some b => return ofR (.binaryApp op a.e b.e)
                  (typeOfBinaryApp op a.tx b.tx a.e b.e c env)

/-- A unary application at operand type `ty`, typed by `typeOfUnaryApp`. -/
def unary (op : UnaryOp) (ty : CedarType) : G (Option J) := do
  let x? ← match ty with
    | .bool _ => f.bool c
    | _ => f.atTy c ty
  match x? with
  | none => return none
  | some x => return ofR (.unaryApp op x.e) (typeOfUnaryApp op x.tx)

/-- An extension-function call on arguments at `tys`, typed by `typeOfCall`. -/
def call (fn : ExtFun) (tys : List CedarType) : G (Option J) := do
  let rec args : List CedarType → G (Option (List J))
    | [] => return some []
    | ty :: rest => do
      match (← f.atTy c ty) with
      | none => return none
      | some x => return (← args rest).map (x :: ·)
  match (← args tys) with
  | none => return none
  | some xs => return ofR (.call fn (xs.map (·.e))) (typeOfCall fn (xs.map (·.tx)) (xs.map (·.e)))

/-- `x has a`, for a generated base of an inhabited base type: the source of attribute capabilities. -/
def ruleHas : G (Option J) := do
  let bt ← elements (baseTypes c) (by simp [baseTypes, entityTys, entityTypes])
  match (← f.atTy c bt) with
  | none => return none
  | some x =>
    let a ← genAttr
    return ofR (.hasAttr x.e a) (typeOfHasAttr x.tx x.e a c env)

/-- `x hasTag t`: the source of tag capabilities. -/
def ruleHasTag : G (Option J) := do
  let ety ← elements entityTypes (by decide)
  binary f c .hasTag (.entity ety) .string

/-- A read at `ty`: from a capability (through a path), or a required attribute of a generated base.
Offered only when one exists (`readable`). -/
def ruleRead (ty : CedarType) : G (Option J) :=
  let capRead (cs : List (Spec.Expr × TypedExpr × Attr)) (h : cs ≠ []) : G (Option J) := do
    let q ← elements cs h
    return ofR (.getAttr q.1 q.2.2) (typeOfGetAttr q.2.1 q.1 q.2.2 c env)
  let reqRead (rs : List (CedarType × Attr)) (h : rs ≠ []) : G (Option J) := do
    let q ← elements rs h
    match (← f.atTy c q.1) with
    | none => return none
    | some x => return ofR (.getAttr x.e q.2) (typeOfGetAttr x.tx x.e q.2 c env)
  match capReads c ty, requiredReads c ty with
  | [], [] => return none
  | r :: rs, [] => capRead (r :: rs) (by simp)
  | [], r :: rs => reqRead (r :: rs) (by simp)
  | r :: rs, r' :: rs' => oneOf! [fun _ => capRead (r :: rs) (by simp),
                                  fun _ => reqRead (r' :: rs') (by simp)]

def readable (ty : CedarType) : Bool := !(capReads c ty).isEmpty || !(requiredReads c ty).isEmpty

/-- A record literal of at most `n + 1` fields with distinct names, `need` (if given) first, each a
judgment at a generated type. Its type is `typeOf`'s for a record literal: each field required. -/
def recordLit (need : Option (Attr × CedarType)) : G (Option (Spec.Expr × TypedExpr)) := do
  let field (ty : CedarType) : G (Option J) :=
    match ty with
    | .bool _ => f.bool c
    | _ => f.atTy c ty
  let pickTy : G CedarType :=
    elements (CedarType.bool .anyBool :: valueTypes.filter (inhabited c)) (by simp)
  let rec more (names : List Attr) : Nat → G (Option (List (Attr × J)))
    | 0 => return some []
    | n + 1 => oneOf! [
        fun _ => return some [],
        fun _ => do
          let a ← genAttr
          if a ∈ names then more names n else
          match (← field (← pickTy)) with
          | none => return none
          | some j => return (← more (a :: names) n).map ((a, j) :: ·)]
  let first ← match need with
    | some (a, ty) => pure ((← field ty).map fun j => [(a, j)])
    | none => do
      let a ← genAttr
      pure ((← field (← pickTy)).map fun j => [(a, j)])
  match first with
  | none => return none
  | some fs =>
    match (← more (fs.map (·.1)) f.fuel) with
    | none => return none
    | some rest =>
      let all := fs ++ rest
      -- exactly `typeOf`'s typed expression for a record literal
      let rty : RecordType := Map.make (all.map fun (a, j) => (a, Qualified.required j.tx.typeOf))
      return some (.record (all.map fun (a, j) => (a, j.e)),
        .record (all.map fun (a, j) => (a, j.tx)) (.record rty))

/-- `{…} has a`. -/
def ruleRecordHas : G (Option J) := do
  match (← recordLit f c none) with
  | none => return none
  | some (r, tr) =>
    let a ← genAttr
    return ofR (.hasAttr r a) (typeOfHasAttr tr r a c env)

/-- `{…, a: v, …}.a`, reading a field built at the wanted type. -/
def ruleRecordGet (ty : CedarType) : G (Option J) := do
  let a ← genAttr
  match (← recordLit f c (some (a, ty))) with
  | none => return none
  | some (r, tr) => return ofR (.getAttr r a) (typeOfGetAttr tr r a c env)

/-- An attribute chain for the multi-attribute `has` from a base of type `cur`: `n + 1` attributes.
Every attribute but the last must be an entity- or record-typed attribute of the type reached so far,
or absent (the chain then short-circuits to `false`, and the rest is unconstrained); an attribute that
is neither is repaired to an absent one. -/
def genChain [Gen G] (cur : Option CedarType) : Nat → G (List Attr)
  | 0 => do return [← genAttr]
  | n + 1 => do
    match cur with
    | none => return (← genAttr) :: (← genChain none n)
    | some bt =>
      let a ← genAttr
      let next : Option CedarType := (attrTy bt a).map Qualified.getType
      match next with
      | none => return a :: (← genChain none n)
      | some t@(.entity _) | some t@(.record _) => return a :: (← genChain (some t) n)
      | some _ => return "zzz" :: (← genChain none n)

/-- `x has a.b.…`, typed by Cedar's `typeOfExtHasAttr`. -/
def ruleExtHas : G (Option J) := do
  let bt ← elements (baseTypes c) (by simp [baseTypes, entityTys, entityTypes])
  match (← f.atTy c bt) with
  | none => return none
  | some x =>
    let n ← chooseNat 1 (f.fuel + 1)
    match (← genChain (some bt) n) with
    | [] => return none
    | a :: as =>
      match typeOfExtHasAttr x.tx x.e (a :: as) c env with
      | .ok (bty, c') => return some ⟨.extHasAttr x.e a as, .extHasAttr x.tx a as (.bool bty), c'⟩
      | .error _ => return none

/-- A set literal of `1..fuel+1` elements at `elt`. -/
def ruleSet (elt : CedarType) : G (Option J) := do
  let rec elems : Nat → G (Option (List J))
    | 0 => return some []
    | n + 1 => do
      match (← f.atTy c elt) with
      | none => return none
      | some x => return (← elems n).map (x :: ·)
  let n ← chooseNat 1 (f.fuel + 1)
  match (← elems n) with
  | none => return none
  | some xs => return ofR (.set (xs.map (·.e))) (typeOfSet (xs.map (·.tx)))

/-- Boolean rules. Every one applies in every scope; the read rule is offered only when some read of
a boolean exists. -/
def stepBool : G (Option J) :=
  pick (2, fun _ => do let p := Prim.bool (← genBool); return ofR (.lit p) (typeOfLit p env)) ((
  [ (4, fun _ => ruleAnd f c),
    (2, fun _ => ruleOr f c),
    (2, fun _ => ruleIte f c fun c' => f.bool c'),
    (4, fun _ => ruleHas f c),
    (2, fun _ => ruleHasTag f c),
    (1, fun _ => ruleExtHas f c),
    (1, fun _ => ruleRecordHas f c),
    (1, fun _ => ruleRecordGet f c (.bool .anyBool)),
    (1, fun _ => unary f c .not (.bool .anyBool)),
    (1, fun _ => do unary f c (.is (← genName)) (← elements entityTys (by simp [entityTys, entityTypes]))),
    (1, fun _ => do unary f c .isEmpty (.set (← elements setElts (by simp [setElts])))),
    (1, fun _ => do unary f c (.like (← genPattern f.fuel)) .string),
    (2, fun _ => do
          let ty ← elements [CedarType.int, .ext .datetime, .ext .duration] (by decide)
          binary f c (← elements [BinaryOp.less, BinaryOp.lessEq] (by decide)) ty ty),
    (3, fun _ => do
          let ty ← elements (CedarType.int :: valueTypes.filter (inhabited c)) (by simp)
          binary f c .eq ty ty),
    (1, fun _ => do
          match (← f.bool c) with
          | none => return none
          | some a =>
            match (← f.bool c) with
            | none => return none
            | some b => return ofR (.binaryApp .eq a.e b.e)
                          (typeOfBinaryApp .eq a.tx b.tx a.e b.e c env)),
    (1, fun _ => do
          binary f c .eq (← elements entityTys (by simp [entityTys, entityTypes]))
            (← elements entityTys (by simp [entityTys, entityTypes]))),
    (1, fun _ => do
          let p₁ ← genPrim
          let p₂ ← genPrim
          match typeOfLit p₁ env, typeOfLit p₂ env with
          | .ok (t₁, _), .ok (t₂, _) =>
            return ofR (.binaryApp .eq (.lit p₁) (.lit p₂)) (typeOfBinaryApp .eq t₁ t₂ (.lit p₁) (.lit p₂) c env)
          | _, _ => return none),
    (3, fun _ => do
          let t₂ ← elements entityTys (by simp [entityTys, entityTypes])
          binary f c .mem (← elements entityTys (by simp [entityTys, entityTypes]))
            (← elements [t₂, .set t₂] (by simp))),
    (2, fun _ => do
          let ty ← elements setElts (by simp [setElts])
          binary f c .contains (.set ty) ty),
    (2, fun _ => do
          let ty ← elements setElts (by simp [setElts])
          binary f c (← elements [BinaryOp.containsAll, .containsAny] (by decide)) (.set ty) (.set ty)),
    (2, fun _ => do
          call f c (← elements [ExtFun.isIpv4, .isIpv6, .isLoopback, .isMulticast] (by decide))
            [.ext .ipAddr]),
    (1, fun _ => call f c .isInRange [.ext .ipAddr, .ext .ipAddr]),
    (1, fun _ => do
          call f c (← elements [ExtFun.lessThan, .lessThanOrEqual, .greaterThan, .greaterThanOrEqual]
            (by decide)) [.ext .decimal, .ext .decimal])
  ] : List (Nat × (Unit → G (Option J)))) ++
    (if readable c (.bool .anyBool) then [(1, fun _ => ruleRead f c (.bool .anyBool))] else [])) (by simp)

/-- Rules specific to a target type. -/
def construct (ty : CedarType) : List (Nat × (Unit → G (Option J))) :=
  match ty with
  | .int => [
      (2, fun _ => do binary f c (← elements [BinaryOp.add, .sub, .mul] (by decide)) .int .int),
      (1, fun _ => unary f c .neg .int),
      (1, fun _ => do
            call f c (← elements [ExtFun.toMilliseconds, .toSeconds, .toMinutes, .toHours, .toDays]
              (by decide)) [.ext .duration])]
  | .string =>
    match tagReads c with
    | [] => []
    | r :: rs => [(2, fun _ => do
        let q ← elements (r :: rs) (by simp)
        return ofR (.binaryApp .getTag q.1 q.2.2.1)
          (typeOfBinaryApp .getTag q.2.1 q.2.2.2 q.1 q.2.2.1 c env))]
  | .set elt => [(3, fun _ => ruleSet f c elt)]
  | .ext .datetime => [
      (1, fun _ => call f c .offset [.ext .datetime, .ext .duration]),
      (1, fun _ => call f c .toDate [.ext .datetime])]
  | .ext .duration => [
      (1, fun _ => call f c .durationSince [.ext .datetime, .ext .datetime]),
      (1, fun _ => call f c .toTime [.ext .datetime])]
  | _ => []

/-- Rules at an inhabited non-boolean type: a leaf, a conditional, a read if one exists, a record
literal's field, and the type's own constructions. -/
def stepAt (ty : CedarType) : G (Option J) :=
  pick (3, fun _ => leaf c ty) (([(2, fun _ => ruleIte f c fun c' => f.atTy c' ty),
      (1, fun _ => ruleRecordGet f c ty)] : List (Nat × (Unit → G (Option J)))) ++
    (if readable c ty then [(3, fun _ => ruleRead f c ty)] else []) ++ construct f c ty) (by simp)

end

/-- The family at fuel `d`. At fuel `0`, leaves only. -/
def fam [Gen G] : Nat → Fam G
  | 0 => { bool := fun _ => do let p := Prim.bool (← genBool); return ofR (.lit p) (typeOfLit p env),
           atTy := fun c ty => leaf c ty,
           any := genAny 0,
           fuel := 0 }
  | d + 1 =>
    let f := fam d
    { bool := stepBool f, atTy := stepAt f, any := genAny (d + 1), fuel := d + 1 }

/-- A boolean judgment at fuel `d`, under no capabilities. -/
def genS [Gen G] (d : Nat) : G (Option J) := (fam d).bool []

/-! ## Properties -/

/-- Does the real typechecker agree with the judgment the generator computed, exactly — type and
output capabilities? The generator never calls `typeOf`; this checks it. -/
def agrees (j : J) : Bool :=
  match typeOf j.e ∅ env with
  | .ok (tx, c) => tx.typeOf == j.ty && c == j.out
  | .error _ => false

/-- The generator never rejects (no `none`), and its judgment is exactly `typeOf`'s. -/
def prop_correct_by_construction [Gen G] : PropM G Unit := do
  let r ← generate (genS 4)
  match r with
  | none => check false "the generator returned none"
  | some j =>
    check (agrees j) s!"judgment disagrees with typeOf for {reprStr j.e}: claimed {reprStr j.ty}, \
      typeOf says {reprStr ((typeOf j.e ∅ env).map fun p => (p.1.typeOf, p.2))}"

/-- Cedar's `type_of_is_sound`, generating the expression first, printing the `BASALT_H` hashes
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
