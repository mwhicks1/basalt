/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import BasaltFuzz.MiniCedar.Syntax

/-!
# MiniCedar: the evaluator

`Cedar.Spec.evaluate` (`cedar-lean/Cedar/Spec/Evaluator.lean`) restricted to MiniCedar, clause for
clause, including the order in which operands are evaluated and which error each failure raises.
It accepts every `Expr`; an ill-typed one fails with an error rather than getting stuck.
-/

namespace MiniCedar

def Value.asBool : Value → Result Bool
  | .prim (.bool b) => .ok b
  | _ => .error .typeError

def Value.asEntityUID : Value → Result EntityUID
  | .prim (.entityUID uid) => .ok uid
  | _ => .error .typeError

def Value.ofBool (b : Bool) : Value := .prim (.bool b)

/-- `Int64` arithmetic with Cedar's overflow check (`Int64.add?` and friends in cedar-lean). -/
def intOrErr (i : Int) : Result Value :=
  if -2 ^ 63 ≤ i ∧ i < 2 ^ 63 then .ok (.prim (.int (Int64.ofInt i))) else .error .arithBoundsError

def apply₁ : UnaryOp → Value → Result Value
  | .not, .prim (.bool b) => .ok (.ofBool !b)
  | .neg, .prim (.int i) => intOrErr (-i.toInt)
  | .isEmpty, .set vs => .ok (.ofBool vs.isEmpty)
  | .is ety, .prim (.entityUID uid) => .ok (.ofBool (ety == uid.ty))
  | _, _ => .error .typeError

def inₑ (uid₁ uid₂ : EntityUID) (es : Entities) : Bool :=
  uid₁ == uid₂ || (es.ancestorsOrEmpty uid₁).contains uid₂

def inₛ (uid : EntityUID) (vs : List Value) (es : Entities) : Result Value := do
  let uids ← vs.mapM Value.asEntityUID
  .ok (.ofBool (uids.any (inₑ uid · es)))

def apply₂ (op : BinaryOp) (v₁ v₂ : Value) (es : Entities) : Result Value :=
  match op, v₁, v₂ with
  | .eq, _, _ => .ok (.ofBool (v₁ == v₂))
  | .less, .prim (.int i), .prim (.int j) => .ok (.ofBool (decide (i < j)))
  | .lessEq, .prim (.int i), .prim (.int j) => .ok (.ofBool (decide (i ≤ j)))
  | .add, .prim (.int i), .prim (.int j) => intOrErr (i.toInt + j.toInt)
  | .sub, .prim (.int i), .prim (.int j) => intOrErr (i.toInt - j.toInt)
  | .mul, .prim (.int i), .prim (.int j) => intOrErr (i.toInt * j.toInt)
  | .contains, .set vs, _ => .ok (.ofBool (vs.contains v₂))
  | .containsAll, .set vs₁, .set vs₂ => .ok (.ofBool (vs₂.all vs₁.contains))
  | .containsAny, .set vs₁, .set vs₂ => .ok (.ofBool (vs₁.any vs₂.contains))
  | .mem, .prim (.entityUID u₁), .prim (.entityUID u₂) => .ok (.ofBool (inₑ u₁ u₂ es))
  | .mem, .prim (.entityUID u₁), .set vs => inₛ u₁ vs es
  | _, _, _ => .error .typeError

def attrsOf (v : Value) (lookup : EntityUID → Result (List (String × Value))) :
    Result (List (String × Value)) :=
  match v with
  | .record r => .ok r
  | .prim (.entityUID uid) => lookup uid
  | _ => .error .typeError

def hasAttr (v : Value) (a : String) (es : Entities) : Result Value := do
  let r ← attrsOf v (fun uid => .ok (es.attrsOrEmpty uid))
  .ok (.ofBool (Map.find? r a).isSome)

def getAttr (v : Value) (a : String) (es : Entities) : Result Value := do
  let r ← attrsOf v es.attrs
  match Map.find? r a with
  | some v => .ok v
  | none => .error .attrDoesNotExist

mutual
def evaluate (req : Request) (es : Entities) : Expr → Result Value
  | .lit p => .ok (.prim p)
  | .var .principal => .ok (.prim (.entityUID req.principal))
  | .var .action => .ok (.prim (.entityUID req.action))
  | .var .resource => .ok (.prim (.entityUID req.resource))
  | .var .context => .ok (.record req.context)
  | .ite c t e => do
    let b ← (← evaluate req es c).asBool
    if b then evaluate req es t else evaluate req es e
  | .and a b => do
    let x ← (← evaluate req es a).asBool
    if !x then .ok (.ofBool x) else .ofBool <$> (← evaluate req es b).asBool
  | .or a b => do
    let x ← (← evaluate req es a).asBool
    if x then .ok (.ofBool x) else .ofBool <$> (← evaluate req es b).asBool
  | .unaryApp op e => do
    apply₁ op (← evaluate req es e)
  | .binaryApp op a b => do
    let v₁ ← evaluate req es a
    let v₂ ← evaluate req es b
    apply₂ op v₁ v₂ es
  | .hasAttr e a => do hasAttr (← evaluate req es e) a es
  | .getAttr e a => do getAttr (← evaluate req es e) a es
  | .set xs => do .ok (.set (Set.make (← evaluateList req es xs)))
  | .record fs => do .ok (.record (Map.make (← evaluateFields req es fs)))

def evaluateList (req : Request) (es : Entities) : List Expr → Result (List Value)
  | [] => .ok []
  | x :: xs => do
    let v ← evaluate req es x
    let vs ← evaluateList req es xs
    .ok (v :: vs)

def evaluateFields (req : Request) (es : Entities) :
    List (String × Expr) → Result (List (String × Value))
  | [] => .ok []
  | (a, x) :: fs => do
    let v ← evaluate req es x
    let vs ← evaluateFields req es fs
    .ok ((a, v) :: vs)
end

end MiniCedar
