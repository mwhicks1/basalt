/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Basalt.Fuzz.Basic
import SplitMix.Native

/-!
# The `ChoiceFuzz` interpretation

`ChoiceFuzz` decodes a fuzzer input as a *choice sequence*: one record per non-unit `choose`, a kind
tag and the absolute value drawn. Replay is positional; a record is used when its kind matches the
draw and its value is permitted by the draw's bounds, and otherwise, as past the end, the value comes
from a fill seeded by the buffer. A run returns what every draw actually received (`realized`) and
each draw's bounds, which is what the bridge's mutator edits (`DESIGN-choice-sequences.md` §3).
-/

namespace Basalt.Fuzz

open Basalt.PBT

/-- The kind tag of a bare `choose`. -/
def kindNat : UInt8 := 1

/-- The kind tag of a draw made through `RandomChoice.chooseAs`. -/
def kindTag : ChoiceKind → UInt8
  | .nat => 1 | .int => 2 | .index => 3 | .branch => 4 | .bool => 5 | .more => 6 | .length => 7

/-- `n` in unsigned LEB128, appended to `b`. -/
def pushLEB (b : ByteArray) (n : Nat) : ByteArray :=
  if h : n < 128 then b.push n.toUInt8
  else pushLEB (b.push (n % 128 + 128).toUInt8) (n / 128)
termination_by n
decreasing_by omega

/-- The records of a buffer: each a kind byte then an LEB128 value. Total: an unknown kind or a value
cut off by the end of the buffer ends the records, and the rest of the run is fill. -/
def parseRecords (b : ByteArray) : ByteArray × Array Nat := Id.run do
  let mut kinds := ByteArray.empty
  let mut vals : Array Nat := #[]
  let mut i := 0
  while i < b.size do
    let k := b.get! i
    if k == 0 || k > 7 then break
    let mut v := 0
    let mut shift := 1
    let mut j := i + 1
    let mut done := false
    while j < b.size && !done do
      let x := b.get! j
      v := v + (x.toNat % 128) * shift
      shift := shift * 128
      j := j + 1
      done := x < 128
    if !done then break
    kinds := kinds.push k
    vals := vals.push v
    i := j
  return (kinds, vals)

/-- What a draw gets on a misfit or past the end: a fresh value from the fill (the default), or the
range's least value. -/
inductive FillPolicy where
  | fresh
  | simplest
  deriving Inhabited, BEq

/-- One run's state: the input's records and the next one to read, the fill, and what the run did:
`realized` re-encodes every draw as a record, and `bounds` holds, per draw, a flags byte (bit 0: the
value came from the fill) and the bounds `lo`, `hi` in LEB128, and per span a flags byte (`2` and the
label in LEB128 where it opens, `4` where it closes). `kinds := false` treats every draw as `.nat`,
which is design A. -/
structure ChoiceState where
  kinds : ByteArray
  vals : Array Nat
  pos : Nat := 0
  fill : SplitMix
  policy : FillPolicy := .fresh
  useKinds : Bool := true
  realized : ByteArray := ByteArray.emptyWithCapacity 256
  bounds : ByteArray := ByteArray.emptyWithCapacity 512

/-- A choice-sequence interpretation of `Gen`. The `Option` base is `FuzzGen`'s, for the same
reason. -/
abbrev ChoiceFuzz (α : Type) := StateT ChoiceState Option α

instance : Inhabited (ChoiceFuzz α) :=
  ⟨fun _ => none⟩

/-- One draw in `[lo, hi]` of kind `tag`. A unit range reads and records nothing. -/
def choiceStep (tag : UInt8) (lo hi : Nat) (s : ChoiceState) : Nat × ChoiceState :=
  if hi ≤ lo then (lo, s) else
  let tag := if s.useKinds then tag else kindNat
  let p := s.pos
  let stored := if p < s.vals.size && s.kinds.get! p == tag then
    let v := s.vals[p]!
    if lo ≤ v && v ≤ hi then some v else none
    else none
  match stored with
  | some v =>
    (v, { s with pos := p + 1, realized := pushLEB (s.realized.push tag) v,
                 bounds := pushLEB (pushLEB (s.bounds.push 0) lo) hi })
  | none =>
    let (v, g) := match s.policy with
      | .fresh => s.fill.randNat lo hi
      | .simplest => (lo, s.fill)
    (v, { s with pos := p + 1, fill := g, realized := pushLEB (s.realized.push tag) v,
                 bounds := pushLEB (pushLEB (s.bounds.push 1) lo) hi })

/-- Record a span's opening (`some l`) or closing (`none`) in the trace. -/
def spanEvent (l : Option UInt64) (s : ChoiceState) : PUnit × ChoiceState :=
  if !s.useKinds then (⟨⟩, s) else
  match l with
  | some l => (⟨⟩, { s with bounds := pushLEB (s.bounds.push 2) l.toNat })
  | none => (⟨⟩, { s with bounds := s.bounds.push 4 })

/-- `choose` takes the record at the cursor if it fits, else the fill. The clamp is the identity on
what `choiceStep` returns; it is what puts the value in range by construction. -/
instance : RandomChoice ChoiceFuzz where
  choose lo hi h := do
    let v ← modifyGet (choiceStep kindNat lo hi)
    pure (ULift.up ⟨max lo (min hi v), by omega, by omega⟩)
  chooseAs k lo hi h := do
    let v ← modifyGet (choiceStep (kindTag k) lo hi)
    pure (ULift.up ⟨max lo (min hi v), by omega, by omega⟩)
  span l g := do
    modifyGet (spanEvent (some l))
    let a ← g
    modifyGet (spanEvent none)
    pure a

instance : MonoSpan ChoiceFuzz where
  monotone_span _ := fun _ _ hxy =>
    Lean.Order.MonoBind.bind_mono_right fun _ => Lean.Order.MonoBind.bind_mono_left hxy

/-- `ChoiceFuzz` has everything a generator needs. -/
example : Gen ChoiceFuzz := inferInstance

/-- What one run produced: its outcome, its realized records and bounds, and the fill afterwards. -/
structure ChoiceResult where
  outcome : TestOutcome
  realized : ByteArray
  bounds : ByteArray
  fill : SplitMix

/-- Run a property on the records of `bytes`, filling from `fill`. Under libFuzzer the fill is
seeded by the buffer (`runChoiceOn`), so a saved input replays; a random phase passes its own PRNG
and an empty buffer, which makes the run plain random generation that records its choices. -/
def runChoice (T : PropM ChoiceFuzz Unit) (bytes : ByteArray) (fill : SplitMix)
    (policy : FillPolicy := .fresh) (useKinds : Bool := true) : ChoiceResult :=
  let (kinds, vals) := parseRecords bytes
  match (runProp T).run { kinds, vals, fill, policy, useKinds } with
  | some (outcome, s) => { outcome, realized := s.realized, bounds := s.bounds, fill := s.fill }
  | none => { outcome := Except.error .discard, realized := .empty, bounds := .empty, fill }

/-- `runChoice` with the fill seeded by the buffer. -/
def runChoiceOn (T : PropM ChoiceFuzz Unit) (bytes : ByteArray) (policy : FillPolicy := .fresh)
    (useKinds : Bool := true) : ChoiceResult :=
  runChoice T bytes (SplitMix.ofSeed (fillSeed bytes)) policy useKinds

end Basalt.Fuzz
