/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Basalt.Combinators
import Basalt.PBT.Property

/-!
# CedarLite: a fuzzable, provable subset of the Cedar policy language

A self-contained model of a meaningful fragment of Cedar
(`/home/mwhicks/src/cedar-spec/cedar-lean/Cedar/Spec`), built to compare Basalt's coverage-guided
`FuzzGen` backend against the random `IO`/`Plausible` backends on a *large, well-formed* generator —
the kind of target the toy `BasaltFuzz/BuggyBST.lean` cannot exercise.

A modelled subset rather than real Cedar keeps the experiment self-contained and fully instrumented
for coverage, and pairs the generator with an inductive typing judgment (in
`BasaltExamples/Cedar.lean`) against which it is proved sound and complete. The fragment is
reconstructed faithfully: it keeps Cedar's real constructor names, its `Value`/`Prim`/`Error`/`Result`
shapes, and its exact short-circuiting `ite`/`and`/`or` and `apply₂` operator semantics.

The one deliberate divergence from Cedar: integer primitives are unbounded `Int` rather than `Int64`,
so arithmetic is total and cannot raise `arithBoundsError`. This makes "well-typed ⇒ evaluation does
not raise a type error" a clean, always-true property, and lets the generator be *complete* over the
(infinite) set of integer literals.

This module must stay Mathlib-free: the `basalt-fuzz` executable links everything it imports
(`fuzz-run/README.md`), so it imports only `Basalt.Combinators` and `Basalt.PBT.Property`. The proofs
live in `BasaltExamples/Cedar.lean`, which imports this module and the `Basalt` umbrella.
-/

namespace CedarLite

open Basalt.PBT RandomChoice

/-! ## Syntax and values (a subset of `Cedar.Spec`) -/

/-- CedarLite types. Cedar's `CedarType` also has `string`, `entity`, `set`, `record`, and `ext`;
this fragment keeps the two base types that drive short-circuiting and arithmetic. -/
inductive CType where
  | bool
  | int
  deriving DecidableEq, Repr, Inhabited

instance : BEq CType := instBEqOfDecidableEq
instance : LawfulBEq CType := by infer_instance

/-- Primitive values. Mirrors `Cedar.Spec.Prim` minus `string`/`entityUID`; `int` is unbounded `Int`
here rather than Cedar's `Int64`. -/
inductive Prim where
  | bool (b : Bool)
  | int (i : Int)
  deriving DecidableEq, Repr, Inhabited

/-- Runtime values. Mirrors `Cedar.Spec.Value` restricted to primitives. -/
inductive Value where
  | prim (p : Prim)
  deriving DecidableEq, Repr, Inhabited

/-- Evaluation errors. Mirrors `Cedar.Spec.Error`; only `typeError` is reachable in this fragment
(unbounded `Int` removes `arithBoundsError`). -/
inductive Error where
  | typeError
  deriving DecidableEq, Repr, Inhabited

instance : BEq Value := instBEqOfDecidableEq
instance : BEq Error := instBEqOfDecidableEq

/-- As `Cedar.Spec.Result`. -/
abbrev Result (α) := Except Error α

/-- Structural `BEq` on results, so a property can compare two evaluation outcomes. -/
instance : BEq (Result Value) where
  beq
    | .ok a,    .ok b    => a == b
    | .error a, .error b => a == b
    | _,        _        => false

/-- Cedar's unary operators kept here: `not` and `neg`. -/
inductive UnaryOp where
  | not
  | neg
  deriving DecidableEq, Repr, Inhabited

/-- Cedar's binary operators kept here: equality, the two integer comparisons, and the three
arithmetic operators. -/
inductive BinaryOp where
  | eq
  | less
  | lessEq
  | add
  | sub
  | mul
  deriving DecidableEq, Repr, Inhabited

/-- Expressions. Constructor names and shapes follow `Cedar.Spec.Expr`; `var` is a De Bruijn index
into a context (Cedar's `principal`/`action`/`resource`/`context` are the schema-typed variables
this abstracts). Omitted vs. Cedar: `getAttr`/`hasAttr`/`set`/`record`/`call`/`extHasAttr`. -/
inductive Expr where
  | lit (p : Prim)
  | var (i : Nat)
  | ite (cond thenExpr elseExpr : Expr)
  | and (a b : Expr)
  | or (a b : Expr)
  | unaryApp (op : UnaryOp) (e : Expr)
  | binaryApp (op : BinaryOp) (a b : Expr)
  deriving DecidableEq, Repr, Inhabited

/-- The number of constructors in an expression; used as a cost bound and for reporting. -/
def Expr.size : Expr → Nat
  | .lit _ => 1
  | .var _ => 1
  | .ite c t e => 1 + c.size + t.size + e.size
  | .and a b => 1 + a.size + b.size
  | .or a b => 1 + a.size + b.size
  | .unaryApp _ e => 1 + e.size
  | .binaryApp _ a b => 1 + a.size + b.size

/-! ## Evaluation (mirrors `Cedar.Spec.evaluate`) -/

/-- As `Cedar.Spec.Value.asBool`. -/
def Value.asBool : Value → Result Bool
  | .prim (.bool b) => .ok b
  | _ => .error .typeError

/-- As `Cedar.Spec.Value.asInt`. -/
def Value.asInt : Value → Result Int
  | .prim (.int i) => .ok i
  | _ => .error .typeError

/-- As `Cedar.Spec.apply₁`, for the two unary operators kept. -/
def apply₁ : UnaryOp → Value → Result Value
  | .not, .prim (.bool b) => .ok (.prim (.bool !b))
  | .neg, .prim (.int i)  => .ok (.prim (.int (-i)))
  | _, _ => .error .typeError

/-- As `Cedar.Spec.apply₂`, for the six binary operators kept. `eq` is heterogeneous and total, as in
Cedar; the others demand integer operands. -/
def apply₂ : BinaryOp → Value → Value → Result Value
  | .eq,     v₁, v₂                       => .ok (.prim (.bool (v₁ == v₂)))
  | .less,   .prim (.int i), .prim (.int j) => .ok (.prim (.bool (decide (i < j))))
  | .lessEq, .prim (.int i), .prim (.int j) => .ok (.prim (.bool (decide (i ≤ j))))
  | .add,    .prim (.int i), .prim (.int j) => .ok (.prim (.int (i + j)))
  | .sub,    .prim (.int i), .prim (.int j) => .ok (.prim (.int (i - j)))
  | .mul,    .prim (.int i), .prim (.int j) => .ok (.prim (.int (i * j)))
  | _, _, _ => .error .typeError

/-- A variable environment: De Bruijn index → value. -/
abbrev Env := List Value

/-- The evaluator. `ite`/`and`/`or` short-circuit exactly as `Cedar.Spec.evaluate` does. -/
def eval (env : Env) : Expr → Result Value
  | .lit p => .ok (.prim p)
  | .var i => match env[i]? with
    | some v => .ok v
    | none   => .error .typeError
  | .ite c t e => do
    let b ← (← eval env c).asBool
    if b then eval env t else eval env e
  | .and a b => do
    let x ← (← eval env a).asBool
    if !x then .ok (.prim (.bool false)) else do
      let y ← (← eval env b).asBool
      .ok (.prim (.bool y))
  | .or a b => do
    let x ← (← eval env a).asBool
    if x then .ok (.prim (.bool true)) else do
      let y ← (← eval env b).asBool
      .ok (.prim (.bool y))
  | .unaryApp op e => do
    let v ← eval env e
    apply₁ op v
  | .binaryApp op a b => do
    let v₁ ← eval env a
    let v₂ ← eval env b
    apply₂ op v₁ v₂

/-! ## Generators

`genExpr Γ τ` generates well-typed expressions of type `τ` in context `Γ`, following the type-directed
recipe of `BasaltExamples/STLC/GenTerm.lean`. Leaves are weighted heavily with `frequency!` so the
branching process stays subcritical (mean offspring `< 1`) and every backend terminates quickly. -/

/-- Generates an arbitrary `Bool`. -/
def genBool [Gen G] : G Bool :=
  oneOf! [fun _ => pure true, fun _ => pure false]

/-- Generates an arbitrary natural, à la `BasaltExamples/ArbNat.lean`: flip to stop at `0` or recurse
and add one. Complete over all of `ℕ`. -/
def genNat [Gen G] : G Nat :=
  oneOf! [fun _ => pure 0, fun _ => do let n ← genNat; pure (n + 1)]
partial_fixpoint

/-- Generates an arbitrary integer, complete over all of `ℤ`: a nonnegative branch (`+n`) and a
negative branch (`-(n+1)`). -/
def genInt [Gen G] : G Int :=
  oneOf! [fun _ => (Int.ofNat ·) <$> genNat, fun _ => (fun n => -(n + 1 : Int)) <$> genNat]

/-- Generates an arbitrary type. -/
def genCType [Gen G] : G CType :=
  oneOf! [fun _ => pure .bool, fun _ => pure .int]

/-- All variables in `Γ` that have type `τ`, as `Expr.var` leaves. -/
def varsWithType (Γ : List CType) (τ : CType) : List Expr :=
  Γ.zipIdx.filterMap (fun (τ', i) => if τ' == τ then some (Expr.var i) else none)

/-- The smallest term of type `τ`: a literal. Complete over the literals of that type. -/
def genZero [Gen G] (τ : CType) : G Expr :=
  match τ with
  | .bool => (fun b => .lit (.bool b)) <$> genBool
  | .int  => (fun i => .lit (.int i)) <$> genInt

/-- Leaf weight: `frequency!` gives each leaf branch this weight and each recursive branch weight `1`,
keeping the mean number of recursive children below `1`. -/
private abbrev leafW : Nat := 6

/-- Generates a well-typed expression of type `τ` in context `Γ`.

Branches, by type:
* always: a literal (`genZero`), a conditional `ite`, and equality `binaryApp eq` at an arbitrary
  operand type;
* at `bool`: `and`, `or`, `not`, and the integer comparisons `less`/`lessEq`;
* at `int`: `neg`, `add`, `sub`, `mul`;
* plus a variable of type `τ` when `Γ` has one.

Every branch is guarded so it produces only type-`τ` terms, which is what makes the generator sound;
every well-typed term is reachable through some branch, which is what makes it complete. -/
def genExpr [Gen G] (Γ : List CType) (τ : CType) : G Expr :=
  match τ with
  | .bool =>
    let vars := varsWithType Γ .bool
    if hne : vars ≠ [] then
      frequency! [
        (leafW, fun _ => elements vars hne),
        (leafW, fun _ => genZero .bool),
        (1, fun _ => do let c ← genExpr Γ .bool; let t ← genExpr Γ .bool; let e ← genExpr Γ .bool
                        return .ite c t e),
        (1, fun _ => do let a ← genExpr Γ .bool; let b ← genExpr Γ .bool; return .and a b),
        (1, fun _ => do let a ← genExpr Γ .bool; let b ← genExpr Γ .bool; return .or a b),
        (1, fun _ => do let e ← genExpr Γ .bool; return .unaryApp .not e),
        (1, fun _ => do let a ← genExpr Γ .int; let b ← genExpr Γ .int; return .binaryApp .less a b),
        (1, fun _ => do let a ← genExpr Γ .int; let b ← genExpr Γ .int; return .binaryApp .lessEq a b),
        (1, fun _ => do let τ' ← genCType; let a ← genExpr Γ τ'; let b ← genExpr Γ τ'
                        return .binaryApp .eq a b)
      ] (by simp <;> omega)
    else
      frequency! [
        (leafW, fun _ => genZero .bool),
        (1, fun _ => do let c ← genExpr Γ .bool; let t ← genExpr Γ .bool; let e ← genExpr Γ .bool
                        return .ite c t e),
        (1, fun _ => do let a ← genExpr Γ .bool; let b ← genExpr Γ .bool; return .and a b),
        (1, fun _ => do let a ← genExpr Γ .bool; let b ← genExpr Γ .bool; return .or a b),
        (1, fun _ => do let e ← genExpr Γ .bool; return .unaryApp .not e),
        (1, fun _ => do let a ← genExpr Γ .int; let b ← genExpr Γ .int; return .binaryApp .less a b),
        (1, fun _ => do let a ← genExpr Γ .int; let b ← genExpr Γ .int; return .binaryApp .lessEq a b),
        (1, fun _ => do let τ' ← genCType; let a ← genExpr Γ τ'; let b ← genExpr Γ τ'
                        return .binaryApp .eq a b)
      ] (by simp <;> omega)
  | .int =>
    let vars := varsWithType Γ .int
    if hne : vars ≠ [] then
      frequency! [
        (leafW, fun _ => elements vars hne),
        (leafW, fun _ => genZero .int),
        (1, fun _ => do let c ← genExpr Γ .bool; let t ← genExpr Γ .int; let e ← genExpr Γ .int
                        return .ite c t e),
        (1, fun _ => do let e ← genExpr Γ .int; return .unaryApp .neg e),
        (1, fun _ => do let a ← genExpr Γ .int; let b ← genExpr Γ .int; return .binaryApp .add a b),
        (1, fun _ => do let a ← genExpr Γ .int; let b ← genExpr Γ .int; return .binaryApp .sub a b),
        (1, fun _ => do let a ← genExpr Γ .int; let b ← genExpr Γ .int; return .binaryApp .mul a b)
      ] (by simp <;> omega)
    else
      frequency! [
        (leafW, fun _ => genZero .int),
        (1, fun _ => do let c ← genExpr Γ .bool; let t ← genExpr Γ .int; let e ← genExpr Γ .int
                        return .ite c t e),
        (1, fun _ => do let e ← genExpr Γ .int; return .unaryApp .neg e),
        (1, fun _ => do let a ← genExpr Γ .int; let b ← genExpr Γ .int; return .binaryApp .add a b),
        (1, fun _ => do let a ← genExpr Γ .int; let b ← genExpr Γ .int; return .binaryApp .sub a b),
        (1, fun _ => do let a ← genExpr Γ .int; let b ← genExpr Γ .int; return .binaryApp .mul a b)
      ] (by simp <;> omega)
partial_fixpoint

/-- Generates a value of type `τ`. -/
def genValue [Gen G] (τ : CType) : G Value :=
  match τ with
  | .bool => (fun b => .prim (.bool b)) <$> genBool
  | .int  => (fun i => .prim (.int i)) <$> genInt

/-- Generates an environment binding each variable in `Γ` to a value of its type. -/
def genEnv [Gen G] (Γ : List CType) : G Env :=
  match Γ with
  | [] => pure []
  | τ :: Γ' => do
    let v ← genValue τ
    let vs ← genEnv Γ'
    return v :: vs

/-! ## Partial evaluation (a model of `Cedar.TPE`)

`Cedar.TPE.evaluate` reduces an expression against a *partial* request/entities, producing a residual
that agrees with concrete evaluation once the unknowns are filled in
(`Cedar/Thm/TPE/Soundness.lean`'s `partial_evaluate_is_sound`:
`(x.evaluate req es).toOption = ((TPE.evaluate env x preq pes).evaluate req es).toOption`). `tpe`
below is that idea on CedarLite: it substitutes the *known* variables of a partial environment and
constant-folds, leaving the rest as a residual expression, and its soundness property is the analogue
of `partial_evaluate_is_sound`. This is the experiment's deep-structure target: the folds live behind
`ite`/`and`/`or` short-circuits and nested operators, so a bug in them hides behind structure a
uniform sampler reaches only by luck. -/

/-- A partial environment: a known value (`some`) or an unknown (`none`) per variable. -/
abbrev PEnv := List (Option Value)

/-- Inject a value back into an expression (the residual for a known variable or a folded operator). -/
def Value.toExpr : Value → Expr
  | .prim p => .lit p

/-- The partial evaluator. Substitutes known variables, folds constant `unaryApp`/`binaryApp`, and
short-circuits `ite`/`and`/`or` whose guard is a known constant — exactly the reductions
`Cedar.TPE.evaluate` performs, restricted to this fragment. -/
def tpe (pe : PEnv) : Expr → Expr
  | .lit p => .lit p
  | .var i => match pe[i]? with
    | some (some v) => v.toExpr
    | _ => .var i
  | .ite c t e =>
    match tpe pe c with
    | .lit (.bool true)  => tpe pe t
    | .lit (.bool false) => tpe pe e
    | c' => .ite c' (tpe pe t) (tpe pe e)
  | .and a b =>
    match tpe pe a with
    | .lit (.bool false) => .lit (.bool false)
    | .lit (.bool true)  => tpe pe b
    | a' => .and a' (tpe pe b)
  | .or a b =>
    match tpe pe a with
    | .lit (.bool true)  => .lit (.bool true)
    | .lit (.bool false) => tpe pe b
    | a' => .or a' (tpe pe b)
  | .unaryApp op e =>
    let e' := tpe pe e
    match op, e' with
    | .not, .lit (.bool bb) => .lit (.bool !bb)
    | .neg, .lit (.int ii)  => .lit (.int (-ii))
    | _, _ => .unaryApp op e'
  | .binaryApp op a b =>
    let a' := tpe pe a
    let b' := tpe pe b
    match a', b' with
    | .lit pa, .lit pb =>
      match apply₂ op (.prim pa) (.prim pb) with
      | .ok v => v.toExpr
      | .error _ => .binaryApp op a' b'
    | _, _ => .binaryApp op a' b'

/-- A partial evaluator with a planted bug: it folds a statically-**false** `ite` guard to the
*then*-branch instead of the *else*-branch (swapped branches — a classic optimizer defect). The
result differs from `eval` only when the guard folds to a constant `false` and the two branches
evaluate differently, so triggering it needs a foldable-false condition (e.g. a comparison of two
literals, or a known variable) wrapping two branches that disagree — structure a coverage-guided
search reaches by banking each fold. -/
def tpeBuggy (pe : PEnv) : Expr → Expr
  | .lit p => .lit p
  | .var i => match pe[i]? with
    | some (some v) => v.toExpr
    | _ => .var i
  | .ite c t e =>
    match tpeBuggy pe c with
    | .lit (.bool true)  => tpeBuggy pe t
    | .lit (.bool false) => tpeBuggy pe t  -- BUG: should be `tpeBuggy pe e`
    | c' => .ite c' (tpeBuggy pe t) (tpeBuggy pe e)
  | .and a b =>
    match tpeBuggy pe a with
    | .lit (.bool false) => .lit (.bool false)
    | .lit (.bool true)  => tpeBuggy pe b
    | a' => .and a' (tpeBuggy pe b)
  | .or a b =>
    match tpeBuggy pe a with
    | .lit (.bool true)  => .lit (.bool true)
    | .lit (.bool false) => tpeBuggy pe b
    | a' => .or a' (tpeBuggy pe b)
  | .unaryApp op e =>
    let e' := tpeBuggy pe e
    match op, e' with
    | .not, .lit (.bool bb) => .lit (.bool !bb)
    | .neg, .lit (.int ii)  => .lit (.int (-ii))
    | _, _ => .unaryApp op e'
  | .binaryApp op a b =>
    let a' := tpeBuggy pe a
    let b' := tpeBuggy pe b
    match a', b' with
    | .lit pa, .lit pb =>
      match apply₂ op (.prim pa) (.prim pb) with
      | .ok v => v.toExpr
      | .error _ => .binaryApp op a' b'
    | _, _ => .binaryApp op a' b'

/-! ## Properties

Each is polymorphic in `G`, so the same term runs under `FuzzGen`, `IO`, and `Plausible.Gen`. -/

/-- The fixed request context the experiment generates over: four schema-typed variables, standing in
for Cedar's `principal`/`action`/`resource`/`context`. -/
def reqCtx : List CType := [.bool, .int, .bool, .int]

/-- Derive a partial environment from a concrete one by keeping or blanking each binding, so the two
refine by construction (every known entry agrees with `env`). -/
def genPEnvFrom [Gen G] : Env → G PEnv
  | [] => pure []
  | v :: vs => do
    let keep ← genBool
    let rest ← genPEnvFrom vs
    return (if keep then some v else none) :: rest

/-- Type soundness: a well-typed boolean expression evaluates without error under a matching
environment. Should never fail — the no-false-positive sanity check (like `bst-gen`). -/
def prop_eval_total [Gen G] : PropM G Unit := do
  let env ← generate (genEnv reqCtx)
  let e ← generate (genExpr reqCtx .bool)
  check (eval env e).isOk s!"e={reprStr e}, env={reprStr env}"

/-- TPE soundness: partially evaluating then concretely evaluating agrees with direct evaluation.
The analogue of Cedar's `partial_evaluate_is_sound`. Should never fail. -/
def prop_tpe_sound [Gen G] : PropM G Unit := do
  let env ← generate (genEnv reqCtx)
  let pe ← generate (genPEnvFrom env)
  let e ← generate (genExpr reqCtx .bool)
  check (eval env (tpe pe e) == eval env e) s!"e={reprStr e}, env={reprStr env}"

/-- The buggy partial evaluator claims the same soundness. A counterexample is an expression whose
`ite` guard folds to `false` over two differing branches; the message renders it. -/
def prop_tpe_buggy [Gen G] : PropM G Unit := do
  let env ← generate (genEnv reqCtx)
  let pe ← generate (genPEnvFrom env)
  let e ← generate (genExpr reqCtx .bool)
  let got := eval env (tpeBuggy pe e)
  let want := eval env e
  check (got == want) s!"e={reprStr e}, env={reprStr env}, got={reprStr got}, want={reprStr want}"

/-- Is the expression a *nested* `ite` — an `ite` whose then-branch is itself an `ite`? Rarer than a
bare `ite` root (probability `≈ 1/19² ≈ 1/360` under `genExpr`), chosen so the staged benchmark's
per-stage gate is low enough to separate the backends. -/
def isIteRoot : Expr → Bool
  | .ite _ (.ite ..) _ => true
  | _ => false

/-- A staged benchmark, the Cedar analogue of `BasaltFuzz/Staged.lean`'s `propChain`: draw `n`
well-typed boolean expressions and stop early unless each is `ite`-rooted, failing only when all `n`
are. A blind sampler needs all `n` rare draws at once (`≈ 19⁻ⁿ`); a coverage-guided one banks each
newly-reached stage and mutates onward, paying roughly `n · 19`. This is the regime where a
*well-formed* generator benefits from coverage feedback: the failure hides behind a depth of
structure the generator produces only rarely by chance.

Do not drop the `break`: as in `propChain`, it is what nests the stages so that reaching stage `k+1`
is new coverage; without it every input runs all `n` draws and the benchmark degrades to blind search. -/
def prop_cedar_chain [Gen G] (n : Nat) : PropM G Unit := do
  let mut ok := 0
  for _ in [0:n] do
    if isIteRoot (← generate (genExpr reqCtx .bool)) then ok := ok + 1 else break
  check (ok < n) s!"ite-rooted stages={ok} of {n}"

end CedarLite
