/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Basalt.Fuzz.Basic
import BasaltFuzz.MiniCedar.GenValid
import BasaltFuzz.MiniCedar.Props

/-!
# MiniCedar regression tests

Pins the evaluator's Cedar semantics, a witness for every planted optimizer rule together with the
class of input it needs, and a deterministic sample on which the sound optimizer and the
typechecker keep their contracts.
-/

namespace MiniCedar.Test

open MiniCedar Basalt.Fuzz Basalt.PBT

/-! ## Fixture -/

def alice : EntityUID := ⟨"User", "alice"⟩
def carol : EntityUID := ⟨"User", "carol"⟩
def d1 : EntityUID := ⟨"Doc", "d1"⟩
def d2 : EntityUID := ⟨"Doc", "d2"⟩

def int (i : Int) : Expr := .lit (.int (Int64.ofInt i))
def uid (u : EntityUID) : Expr := .lit (.entityUID u)
def tt : Expr := .lit (.bool true)
def ff : Expr := .lit (.bool false)

/-- `alice` and `d1` exist; `carol` and `d2` do not. -/
def fixtureEntities : Entities := [
  (alice, { attrs := Map.make [("age", .prim (.int 1)), ("name", .prim (.string "alice")),
                                ("manager", .prim (.entityUID alice))],
            ancestors := [⟨"Group", "admins"⟩] }),
  (d1, { attrs := Map.make [("owner", .prim (.entityUID alice)), ("public", .prim (.bool false)),
                             ("level", .prim (.int 0)), ("tags", .set [])],
         ancestors := [] })]

def fixtureRequest : Request :=
  { principal := alice, action := actionView, resource := d1,
    context := Map.make [("authenticated", .prim (.bool true)), ("count", .prim (.int 0))] }

#guard fixtureRequest.conforms schema
#guard fixtureEntities.conform schema

def eval (e : Expr) : Result Value := evaluate fixtureRequest fixtureEntities e

/-- Well typed, and raises `arithBoundsError`. -/
def overflow : Expr := .binaryApp .add (.lit (.int Int64.maxValue)) (int 1)
/-- Well typed, and raises `entityDoesNotExist`. -/
def absentAge : Expr := .getAttr (uid carol) "age"

/-! ## Evaluator semantics -/

#guard eval overflow == .error .arithBoundsError
#guard eval absentAge == .error .entityDoesNotExist
#guard eval (.getAttr (.var .principal) "bogus") == .error .attrDoesNotExist
-- `&&` short-circuits on its left operand only.
#guard eval (.and ff (int 1)) == .ok (.prim (.bool false))
#guard eval (.and tt (int 1)) == .error .typeError
-- Operands are evaluated left to right, so the left error wins.
#guard eval (.binaryApp .add overflow absentAge) == .error .arithBoundsError
#guard eval (.binaryApp .add absentAge overflow) == .error .entityDoesNotExist
-- Of two equal keys, the first survives.
#guard eval (.getAttr (.record [("a", int 1), ("a", int 2)]) "a") == .ok (.prim (.int 1))
-- Sets are canonical across constructors: booleans before integers before strings.
#guard eval (.set [.lit (.string "s"), int 1, tt, ff, int 1]) ==
  .ok (.set [.prim (.bool false), .prim (.bool true), .prim (.int 1), .prim (.string "s")])
-- `==` is total, so it compares across types.
#guard eval (.binaryApp .eq (int 1) tt) == .ok (.prim (.bool false))
#guard eval (.binaryApp .mem (.var .principal) (uid ⟨"Group", "admins"⟩)) == .ok (.prim (.bool true))

/-! ## Typechecker -/

#guard typeOf schema (.getAttr (.var .principal) "age") == some .int
#guard typeOf schema (.getAttr (.var .principal) "bogus") == none
#guard typeOf schema (.binaryApp .eq (.var .principal) (.var .resource)) == some .bool
#guard typeOf schema (.set []) == none
#guard typeOf schema (.and tt (int 1)) == none

/-! ## Planted optimizer rules

A witness per planted rule: the rule changes its result, the sound rules do not, and it is well
typed exactly when the rule's class says a well-typed counterexample exists. -/

def witnesses : List (String × Expr) := [
  ("and-true-left", .and tt (int 1)),
  ("or-false-left", .or ff (int 1)),
  ("not-not", .unaryApp .not (.unaryApp .not (int 1))),
  ("ite-bool-id", .ite (int 1) tt ff),
  ("add-zero", .binaryApp .add tt (int 0)),
  ("and-true-right", .and (int 1) tt),
  ("mul-zero", .binaryApp .mul overflow (int 0)),
  ("eq-refl", .binaryApp .eq overflow overflow),
  ("ite-same", .ite (.binaryApp .less overflow (int 0)) (int 1) (int 1)),
  ("and-false-right", .and (.binaryApp .less overflow (int 0)) ff),
  ("sub-self", .binaryApp .sub overflow overflow),
  ("record-access", .getAttr (.record [("a", int 1), ("b", overflow)]) "a"),
  ("and-commute", .and (.binaryApp .eq (.var .principal) (.var .resource)) (.getAttr (uid d2) "public")),
  ("neg-neg", .unaryApp .neg (.unaryApp .neg (.lit (.int Int64.minValue)))),
  ("record-last", .getAttr (.record [("a", int 1), ("a", int 2)]) "a"),
  ("eq-commute", .binaryApp .eq
    (.binaryApp .add (.getAttr (.var .principal) "age") (.lit (.int Int64.maxValue))) absentAge),
  ("add-commute", .binaryApp .add
    (.binaryApp .add (.getAttr (.var .principal) "age") (.lit (.int Int64.maxValue))) absentAge)
]

def witnessOk (p : PlantedRule) : Bool :=
  match witnesses.lookup p.rule.name with
  | none => false
  | some w =>
    eval (optimize p.optimizer w) != eval w &&
    eval (optimize soundRules w) == eval w &&
    (typeOf schema w).isSome == (p.bugClass != .illTyped)

/- Every planted rule has a witness that meets its claims. -/
#guard plantedRules.all witnessOk
#guard witnesses.length == plantedRules.length

/-! ## A deterministic sample

`runOne` is pure, so a fixed set of buffers is a reproducible campaign. -/

/-- Buffer `k` of a fixed pseudo-random family (a 64-bit LCG). -/
def buffer (k : Nat) : ByteArray := Id.run do
  let mut s : UInt64 := UInt64.ofNat (k * 2654435761 + 1)
  let mut out := ByteArray.empty
  for _ in [0:256] do
    s := s * 6364136223846793005 + 1442695040888963407
    out := out.push (s >>> 56).toUInt8
  return out

def fails (T : PropM FuzzGen Unit) (n : Nat) : Nat :=
  (List.range n).countP fun k =>
    match (runOne T (buffer k)).outcome with
    | .error (.fail _) => true
    | _ => false

#guard fails (prop_optimize_sound soundRules genAnyExpr) 1000 == 0
#guard fails (prop_typecheck_sound genAnyExpr) 1000 == 0
#guard fails (prop_optimize_preserves_type soundRules genAnyExpr) 1000 == 0

/- `genTyped τ` is sound for `typeOf`, at each kind of type it is asked for. -/
#guard [CType.bool, .int, .string, .entity "User", .set .string, .set (.entity "Doc"),
        .record schema.request.context].all fun τ =>
  (List.range 1000).all fun k =>
    match (genTyped (G := FuzzGen) τ).run' { buffer := buffer k, cursor := 0 } with
    | some e => typeOf schema e == some τ
    | none => false

#guard fails (prop_optimize_sound soundRules genValidExpr) 1000 == 0
#guard fails (prop_typecheck_sound genValidExpr) 1000 == 0

end MiniCedar.Test
