/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import BasaltFuzz.MiniCedar.Eval

/-!
# MiniCedar: a rule-based optimizer, with planted unsound rules

`optimize rules` rewrites bottom up, applying at each node the first rule that fires. The contract
is exact: `evaluate req es (optimize rules e) = evaluate req es e` for *every* expression, request
and entities — the same value, or the same error. `soundRules` meets it; each of `plantedRules`
breaks it, and is sound on some restricted set of inputs, which its `BugClass` names. The witness
pins in `BasaltTest/MiniCedar.lean` check that every planted rule is killable and the sound rules
agree on every witness.
-/

namespace MiniCedar

structure Rule where
  name : String
  rewrite : Expr → Option Expr

def Rule.applyFirst (rules : List Rule) (e : Expr) : Expr :=
  (rules.findSome? (·.rewrite e)).getD e

mutual
def optimize (rules : List Rule) : Expr → Expr
  | .lit p => Rule.applyFirst rules (.lit p)
  | .var v => Rule.applyFirst rules (.var v)
  | .ite c t e => Rule.applyFirst rules (.ite (optimize rules c) (optimize rules t) (optimize rules e))
  | .and a b => Rule.applyFirst rules (.and (optimize rules a) (optimize rules b))
  | .or a b => Rule.applyFirst rules (.or (optimize rules a) (optimize rules b))
  | .unaryApp op e => Rule.applyFirst rules (.unaryApp op (optimize rules e))
  | .binaryApp op a b => Rule.applyFirst rules (.binaryApp op (optimize rules a) (optimize rules b))
  | .hasAttr e a => Rule.applyFirst rules (.hasAttr (optimize rules e) a)
  | .getAttr e a => Rule.applyFirst rules (.getAttr (optimize rules e) a)
  | .set xs => Rule.applyFirst rules (.set (optimizeList rules xs))
  | .record fs => Rule.applyFirst rules (.record (optimizeFields rules fs))

def optimizeList (rules : List Rule) : List Expr → List Expr
  | [] => []
  | x :: xs => optimize rules x :: optimizeList rules xs

def optimizeFields (rules : List Rule) : List (String × Expr) → List (String × Expr)
  | [] => []
  | (a, x) :: fs => (a, optimize rules x) :: optimizeFields rules fs
end

/-! ## Sound rules -/

mutual
/-- Evaluation cannot depend on the request or the entities: no variable, and nothing that looks
an entity up (`in`, attribute access and test). -/
def Expr.isClosed : Expr → Bool
  | .lit _ => true
  | .var _ | .hasAttr .. | .getAttr .. | .binaryApp .mem .. => false
  | .ite c t e => c.isClosed && t.isClosed && e.isClosed
  | .and a b | .or a b | .binaryApp _ a b => a.isClosed && b.isClosed
  | .unaryApp _ e => e.isClosed
  | .set xs => Expr.allClosed xs
  | .record fs => Expr.fieldsClosed fs

def Expr.allClosed : List Expr → Bool
  | [] => true
  | x :: xs => x.isClosed && Expr.allClosed xs

def Expr.fieldsClosed : List (String × Expr) → Bool
  | [] => true
  | (_, x) :: fs => x.isClosed && Expr.fieldsClosed fs
end

def Expr.isLit : Expr → Bool
  | .lit _ => true
  | _ => false

/-- The first occurrence of each element, in order. -/
def dedupFirst (xs : List Expr) : List Expr :=
  xs.foldl (fun seen x => if seen.contains x then seen else seen ++ [x]) []

def boolLit (b : Bool) : Expr := .lit (.bool b)
def intLit (i : Int64) : Expr := .lit (.int i)

/-- A closed expression that evaluates to a primitive becomes that literal. One that fails is left
alone: an error has no literal. -/
def foldConst : Rule where
  name := "fold-const"
  rewrite e :=
    if e.isLit || !e.isClosed then none
    else match evaluate default [] e with
      | .ok (.prim p) => some (.lit p)
      | _ => none

def iteConst : Rule where
  name := "ite-const"
  rewrite
    | .ite (.lit (.bool true)) t _ => some t
    | .ite (.lit (.bool false)) _ e => some e
    | _ => none

/-- Only the *left* operand short-circuits. -/
def shortCircuit : Rule where
  name := "short-circuit"
  rewrite
    | .and (.lit (.bool false)) _ => some (boolLit false)
    | .or (.lit (.bool true)) _ => some (boolLit true)
    | _ => none

/-- Sound because `!c` and `ite c ..` raise the same error when `c` is not a boolean. -/
def iteNot : Rule where
  name := "ite-not"
  rewrite
    | .ite (.unaryApp .not c) t e => some (.ite c e t)
    | _ => none

/-- A repeated element evaluates to the same result as its first occurrence, and after it. -/
def setDedup : Rule where
  name := "set-dedup"
  rewrite
    | .set xs => let ys := dedupFirst xs; if ys.length < xs.length then some (.set ys) else none
    | _ => none

/-- Only when every field is a literal: a record literal evaluates all of its fields. The first
field with the key wins, as in `Map.make`. -/
def recordLit : Rule where
  name := "record-lit"
  rewrite
    | .getAttr (.record fs) a => if fs.all (·.2.isLit) then Map.find? fs a else none
    | .hasAttr (.record fs) a =>
      if fs.all (·.2.isLit) then some (boolLit (Map.find? fs a).isSome) else none
    | _ => none

def soundRules : List Rule := [foldConst, iteConst, shortCircuit, iteNot, setDedup, recordLit]

/-! ## Planted unsound rules -/

/-- The inputs a planted rule is sound on, i.e. what a counterexample must have. -/
inductive BugClass where
  /-- Sound on well-typed inputs: a counterexample is ill typed. -/
  | illTyped
  /-- Sound on inputs that evaluate without error: a counterexample is well typed and raises one. -/
  | runtimeError
  /-- As `runtimeError`, where the error needs an extreme `Int64` literal. -/
  | boundary
  /-- Sound on records without repeated keys. -/
  | duplicateKey
  /-- Sound unless two operands both fail, with different errors. -/
  | errorOrder
  deriving DecidableEq, Repr

structure PlantedRule where
  rule : Rule
  bugClass : BugClass

private def planted (name : String) (c : BugClass) (f : Expr → Option Expr) : PlantedRule :=
  { rule := { name, rewrite := f }, bugClass := c }

def plantedRules : List PlantedRule := [
  planted "and-true-left" .illTyped fun
    | .and (.lit (.bool true)) b => some b
    | _ => none,
  planted "or-false-left" .illTyped fun
    | .or (.lit (.bool false)) b => some b
    | _ => none,
  planted "not-not" .illTyped fun
    | .unaryApp .not (.unaryApp .not e) => some e
    | _ => none,
  planted "ite-bool-id" .illTyped fun
    | .ite c (.lit (.bool true)) (.lit (.bool false)) => some c
    | _ => none,
  planted "add-zero" .illTyped fun
    | .binaryApp .add e (.lit (.int 0)) => some e
    | _ => none,
  planted "and-true-right" .illTyped fun
    | .and a (.lit (.bool true)) => some a
    | _ => none,
  planted "mul-zero" .runtimeError fun
    | .binaryApp .mul _ (.lit (.int 0)) => some (intLit 0)
    | _ => none,
  planted "eq-refl" .runtimeError fun
    | .binaryApp .eq a b => if a == b then some (boolLit true) else none
    | _ => none,
  planted "ite-same" .runtimeError fun
    | .ite _ t e => if t == e then some t else none
    | _ => none,
  planted "and-false-right" .runtimeError fun
    | .and _ (.lit (.bool false)) => some (boolLit false)
    | _ => none,
  planted "sub-self" .runtimeError fun
    | .binaryApp .sub a b => if a == b then some (intLit 0) else none
    | _ => none,
  planted "record-access" .runtimeError fun
    | .getAttr (.record fs) a => Map.find? fs a
    | _ => none,
  planted "and-commute" .runtimeError fun
    | .and a b => if b.size < a.size then some (.and b a) else none
    | _ => none,
  planted "neg-neg" .boundary fun
    | .unaryApp .neg (.unaryApp .neg e) => some e
    | _ => none,
  planted "record-last" .duplicateKey fun
    | .getAttr (.record fs) a =>
      if fs.all (·.2.isLit) then Map.find? fs.reverse a else none
    | _ => none,
  planted "eq-commute" .errorOrder fun
    | .binaryApp .eq a b => if b.size < a.size then some (.binaryApp .eq b a) else none
    | _ => none,
  planted "add-commute" .errorOrder fun
    | .binaryApp .add a b => if b.size < a.size then some (.binaryApp .add b a) else none
    | _ => none
]

/-- The sound rules with one planted rule, tried first so it fires wherever it matches. -/
def PlantedRule.optimizer (p : PlantedRule) : List Rule := p.rule :: soundRules

end MiniCedar
