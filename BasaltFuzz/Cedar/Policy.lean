/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Cedar.Slice.PolicySlice
import BasaltFuzz.Cedar.Gen

/-!
# Policy sets for Cedar's validator and authorizer

Generates a policy set (scopes over `CedarWide`'s entities, conditions from `CedarGen`), a request
for one of three actions, and an entity store, for properties stated by Cedar's validation and
authorization theorems. A condition is generated for the `view`/`read` environment, so every policy's
action scope excludes `share`, under which the scope types `false` and the condition is never typed.
-/

namespace CedarPolicy

open Basalt.PBT RandomChoice
open Cedar Cedar.Data Cedar.Spec Cedar.Validation
open CedarTyped (genInt64 genBool)
open CedarWide (env userT groupT photoT albumT actionT view read ctxTy actEntry uid)

/-! ## Schema: `CedarWide`'s, plus an action on albums with an empty context -/

def share : EntityUID := ⟨actionT, "share"⟩

def shareEntry : ActionSchemaEntry :=
  { appliesToPrincipal := Set.make [userT], appliesToResource := Set.make [albumT],
    ancestors := Set.empty, context := Map.empty }

def schema : Schema :=
  { ets := env.ets, acts := Map.make [(view, actEntry [read]), (read, actEntry []), (share, shareEntry)] }

/-! ## Policies -/

def users : List EntityUID := [uid userT "alice", uid userT "bob"]
def groups : List EntityUID := [uid groupT "admins", uid groupT "staff"]
def photos : List EntityUID := [uid photoT "p1", uid photoT "p2"]
def albums : List EntityUID := [uid albumT "a1"]

def genScope [Gen G] (ety : EntityType) (leaves : List EntityUID) (parents : List EntityUID)
    (hl : leaves ≠ []) (hp : parents ≠ []) : G Scope :=
  frequency! [
    (3, fun _ => pure .any),
    (2, fun _ => (Scope.eq ·) <$> elements leaves hl),
    (2, fun _ => (Scope.mem ·) <$> elements (leaves ++ parents) (by simp [hl])),
    (1, fun _ => pure (.is ety)),
    (1, fun _ => (Scope.isMem ety ·) <$> elements parents hp)] (by simp)

def genActionScope [Gen G] : G ActionScope :=
  frequency! [
    (2, fun _ => pure (.actionScope (.eq view))),
    (2, fun _ => pure (.actionScope (.eq read))),
    (2, fun _ => pure (.actionScope (.mem read))),
    (1, fun _ => pure (.actionInAny [view, read])),
    (1, fun _ => pure (.actionInAny [view]))] (by simp)

/-- A condition the validator does not find impossible: a body typed `ff` becomes an `unless`, one
typed `tt` a `when`, since a single impossible policy fails the whole set's validation. -/
def genCondition [Gen G] : G Condition := do
  let kind ← elements [ConditionKind.when, .unless] (by decide)
  match ← CedarGen.genS 3 with
  | none => return { kind := .when, body := .lit (.bool true) }
  | some j =>
    let kind := match j.tx.typeOf with
      | .bool .ff => .unless
      | .bool .tt => .when
      | _ => kind
    return { kind, body := j.e }

def genPolicy [Gen G] (n : Nat) : G Policy := do
  let effect ← elements [Effect.permit, .forbid] (by decide)
  let p ← genScope userT users groups (by decide) (by decide)
  let a ← genActionScope
  let r ← genScope photoT photos albums (by decide) (by decide)
  let k ← elements [0, 1, 1, 2] (by decide)
  let mut cs := []
  for _ in List.range k do cs := cs ++ [← genCondition]
  return { id := s!"policy{n}", effect, principalScope := .principalScope p, actionScope := a,
           resourceScope := .resourceScope r, condition := cs }

def genPolicies [Gen G] : G Policies := do
  let k ← elements [1, 2, 2, 3] (by decide)
  let mut ps := []
  for n in List.range k do ps := ps ++ [← genPolicy n]
  return ps

/-! ## Requests and entities -/

def genRequest [Gen G] : G Request := do
  let base ← CedarWide.genRequest
  match ← elements [view, read, share] (by decide) with
  | ⟨_, "share"⟩ => return { base with action := share, resource := uid albumT "a1", context := Map.empty }
  | a => return { base with action := a }

def genEntities [Gen G] : G Entities := do
  let es ← CedarWide.genEntities
  return Map.make ((share, actionSchemaEntryToEntityData shareEntry) :: es.toList)

/-! ## Properties -/

def excused (r : Result Value) : Bool :=
  match r with
  | .ok (.prim (.bool _)) => true
  | .ok _ => false
  | .error e => CedarTyped.isExcusedError e

/-- The policy set's size: the input size the traced property reports. -/
def policiesSize (ps : Policies) : Nat := (ps.map fun p => CedarWide.exprSize p.toExpr).sum

/-- Cedar's validation and authorization theorems over a validated policy set:
`validation_is_sound` (each policy evaluates to a boolean or an excused error), with
`validation_is_sound_response` (so does each one the authorizer reports erroring);
`validate_with_level_is_sound` at levels 0–2 (slicing the store at a level the set validates at keeps
the response); `allowed_iff_explicitly_permitted_and_not_denied`, `order_and_dup_independent`
(the reversed set) and `isAuthorized_eq_for_scope_based_policy_slice`. Prints `BASALT_H` as the
traced expression properties do. -/
def prop_policy_traced [Gen G] : PropM G Unit := do
  let ps ← generate genPolicies
  let req ← generate genRequest
  let es ← generate genEntities
  let hp := hash (reprStr ps)
  let hi := mixHash hp (mixHash (hash (reprStr req)) (hash (reprStr es.toList)))
  let v := match validate ps schema with
    | .ok _ => "ok" | .error (.impossiblePolicy _) => "impossible" | .error _ => "type"
  check (dbgTrace s!"BASALT_H {hp} {hi} {policiesSize ps} {v}" fun _ => true)
  assume (validateRequest schema req matches .ok _)
  assume (validateEntities schema es matches .ok _)
  match validate ps schema with
  | .error _ => pure ()
  | .ok _ =>
    let resp := isAuthorized req es ps
    for p in ps do
      let r := evaluate p.toExpr req es
      check (excused r) s!"UNSOUND policy: {reprStr p} evaluated to {reprStr r}"
    for id in resp.erroringPolicies.toList do
      check (ps.any fun p => p.id == id && excused (evaluate p.toExpr req es))
        s!"UNSOUND response: {id} reported erroring"
    for n in [0, 1, 2] do
      if validateWithLevel ps schema n matches .ok _ then
        check (isAuthorized req (es.sliceAtLevel req n) ps == resp)
          s!"UNSOUND slice: level {n} changes the response for {reprStr ps}"
    let permits := satisfiedPolicies .permit ps req es
    let forbids := satisfiedPolicies .forbid ps req es
    check ((resp.decision == .allow) == (!permits.isEmpty && forbids.isEmpty))
      s!"UNSOUND decision: {reprStr resp.decision} for {reprStr ps}"
    check (isAuthorized req es ps.reverse == resp) s!"UNSOUND order: {reprStr ps}"
    check (isAuthorized req es (Slice.BoundAnalysis.slice Slice.scopeAnalysis req es ps) == resp)
      s!"UNSOUND policy slice: {reprStr ps}"

end CedarPolicy
