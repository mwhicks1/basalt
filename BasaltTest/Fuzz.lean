/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Basalt.Combinators
import Basalt.Fuzz.Runner
import BasaltExamples.BST
import BasaltFuzz.BuggyBST

/-!
# `FuzzGen` regression tests

Deterministic checks of the byte → choice mapping, run purely (no fuzzer): `runOne` on fixed byte
arrays must produce fixed outcomes. Pins the contract that a corpus byte maps to a specific choice.
-/

open Basalt.Fuzz Basalt.PBT RandomChoice

/-- Build an input buffer from a byte list. -/
private def bytes (l : List UInt8) : ByteArray := ⟨l.toArray⟩

private def renderOutcome : TestOutcome → String
  | .ok () => "pass"
  | .error (.fail r) => s!"fail: {r}"
  | .error .discard => "discard"

/- Most pins care only about the verdict; `renderShort` below adds the deficit where that is the
point. -/
private def render (r : FuzzResult) : String := renderOutcome r.outcome

/- A single choice in `[0,9]` consumes one byte and reduces mod 10; the property is `· < 9`. -/
private def propLt9 : PropM FuzzGen Unit := forAll (chooseNat 0 9) (· < 9)

/- Byte `9` → value `9`, so `9 < 9` fails and renders the drawn value. -/
/-- info: fail: 9 -/
#guard_msgs in #eval IO.println (render (runOne propLt9 (bytes [9])))

/- Byte `3` → value `3`. -/
/-- info: pass -/
#guard_msgs in #eval IO.println (render (runOne propLt9 (bytes [3])))

/- Empty buffer takes the zero-extension path → value `0`. -/
/-- info: pass -/
#guard_msgs in #eval IO.println (render (runOne propLt9 (bytes [])))

/- A two-branch `oneOf` reads one byte and takes bit 0: even → first branch, odd → second. -/
private def propPick : PropM FuzzGen Unit :=
  forAll (oneOf [fun _ => pure 100, fun _ => pure 200]) (fun n => n == 100)

/- Even byte → first branch. -/
/-- info: pass -/
#guard_msgs in #eval IO.println (render (runOne propPick (bytes [8])))

/- Odd byte → second branch. -/
/-- info: fail: 200 -/
#guard_msgs in #eval IO.println (render (runOne propPick (bytes [9])))

/- `oneOf!` makes `oneOf`'s draw, so a byte picks the same branch. -/
private def propPickCompiled : PropM FuzzGen Unit :=
  forAll (oneOf! [fun _ => pure 100, fun _ => pure 200]) (fun n => n == 100)

/-- info: pass -/
#guard_msgs in #eval IO.println (render (runOne propPickCompiled (bytes [8])))

/-- info: fail: 200 -/
#guard_msgs in #eval IO.println (render (runOne propPickCompiled (bytes [9])))

/- A recursive polymorphic generator from `BasaltExamples/` runs at `FuzzGen` and terminates on a
fixed buffer. -/
private def propBSTsizeNonneg : PropM FuzzGen Unit :=
  forAll (BST.Tree.genBST 0 20) (fun t => t.size ≥ 0)

/-- info: pass -/
#guard_msgs in #eval IO.println (render (runOne propBSTsizeNonneg (bytes [1,5,1,3,0,0,0,0])))

/- Two draws (one byte each), a precondition, then `check` — plain monadic `do`. -/
private def propTwo : PropM FuzzGen Unit := do
  let x ← generate (chooseNat 0 9)
  let y ← generate (chooseNat 0 9)
  assume (x != y)
  check (x < y) s!"x={x}, y={y}"

/- Ordered: `x=3, y=7`. -/
/-- info: pass -/
#guard_msgs in #eval IO.println (render (runOne propTwo (bytes [3, 7])))

/- Mis-ordered: `x=7, y=3`, rendering both drawn inputs. -/
/-- info: fail: x=7, y=3 -/
#guard_msgs in #eval IO.println (render (runOne propTwo (bytes [7, 3])))

/- Equal: the precondition rejects the input. -/
/-- info: discard -/
#guard_msgs in #eval IO.println (render (runOne propTwo (bytes [5, 5])))

/-! ### The deficit

How many bytes a run wanted beyond the ones it was given is the whole feedback channel for `--grow`,
which appends that many zeros. These pin the two facts growth rests on: the count is exact, and
appending zeros does not change the outcome. -/

private def renderShort (r : FuzzResult) : String := s!"{render r} (short {r.deficit})"

/- One byte for two draws: the second reads past the end and gets `0`, so the property fails on
`7 < 0` and reports a deficit of exactly the one byte it went without. -/
/-- info: fail: x=7, y=0 (short 1) -/
#guard_msgs in #eval IO.println (renderShort (runOne propTwo (bytes [7])))

/- Materializing that byte is what `--grow` does, and it is semantics-preserving: the same failure,
now with the byte the fuzzer can mutate actually present in the input. -/
/-- info: fail: x=7, y=0 (short 0) -/
#guard_msgs in #eval IO.println (renderShort (runOne propTwo (bytes [7, 0])))

/- A run that fits inside its buffer reports no deficit, which is what keeps growth from firing on
inputs that were never starved. -/
/-- info: pass (short 0) -/
#guard_msgs in #eval IO.println (renderShort (runOne propTwo (bytes [3, 7])))

/- The deficit counts every byte the run went without, not just the first: after `[1, 5]` builds a
node, `genBST` recurses on both subtrees and each reads a `frequency` byte past the end. -/
/-- info: pass (short 2) -/
#guard_msgs in #eval IO.println (renderShort (runOne propBSTsizeNonneg (bytes [1, 5])))

/-! ### Random fill

Under `randomFill` a read past the end is a byte of the buffer's own seeded stream, so a run is
still a function of its buffer, reads inside the buffer are unchanged, and materializing the bytes
a run read past its end (what `--grow` does) preserves it. The bridge computes the same stream from
the seed, so it pins the same `mix64 1`. -/

/-- info: 6238072747940578789 -/
#guard_msgs in #eval IO.println (mix64 1)

private def rfill : FuzzConfig := { randomFill := true }

/- Inside the buffer, the fill is never read. -/
/-- info: fail: x=7, y=3 -/
#guard_msgs in #eval IO.println (render (runOne propTwo (bytes [7, 3]) rfill))

/- Past it, the second draw is the fill's, not `0`, and the same on every run of the buffer. -/
/-- info: true -/
#guard_msgs in #eval IO.println
  (render (runOne propTwo (bytes [7]) rfill) == render (runOne propTwo (bytes [7]) rfill) &&
   render (runOne propTwo (bytes [7]) rfill) != render (runOne propTwo (bytes [7])))

/-- Materialize the `k` bytes a random-fill run of `b` read past its end, as the bridge's `--grow`
does from the seed it is handed. -/
private def grow (b : ByteArray) (k : Nat) : ByteArray := Id.run do
  let seed := (runOne propBSTsizeNonneg b rfill).seed
  let mut out := b
  for i in [b.size:b.size + k] do out := out.push (fillByte seed i)
  return out

/- The grown buffer draws exactly what the short one did, with nothing left to fill. -/
/-- info: true -/
#guard_msgs in #eval IO.println <| Id.run do
  let b := bytes [1, 5]
  let r := runOne propBSTsizeNonneg b { randomFill := true, record := true }
  let g := grow b r.deficit
  let r' := runOne propBSTsizeNonneg g { randomFill := true, record := true }
  return r.trace == r'.trace && r'.deficit == 0 && r.deficit > 0

/-! ### One property, every backend

`basalt-fuzz --backend=` rests on one registry entry (a `Basalt.PBT.Property`) running at `FuzzGen`,
`IO`, and `Plausible.Gen`. These pin that, so a monomorphic property or a missing `Gen` instance is a
build failure here rather than a link error in the opt-in executable. -/

private def propAnyBackend : Property := fun _ => do
  let x ← generate (chooseNat 0 9)
  check (x ≤ 9) s!"x={x}"

/- `x ≤ 9` holds for every draw, so the outcome is `pass` whatever the backend chooses. -/
/-- info: pass -/
#guard_msgs in #eval IO.println (render (runOne (propAnyBackend FuzzGen) (bytes [4])))

/-- info: pass -/
#guard_msgs in #eval do IO.println (renderOutcome (← runProp (propAnyBackend IO)))

/-- info: pass -/
#guard_msgs in
#eval do IO.println (renderOutcome (← Plausible.Gen.run (runProp (propAnyBackend Plausible.Gen)) 0))

/-! ### The fuzz target's `genBST` is the proved one

`Fuzz/BuggyBST.lean` restates `BasaltExamples/BST`'s `Tree.genBST` rather than importing it, because
that import would pull Mathlib into the executable's link closure (`fuzz-run/README.md`). The copy's
claim — that the fuzzed generator is the one proved sound, complete, terminating, and cost-bounded —
holds only while the two agree, so these pins make a drift a build failure: both are
`[Gen G]` terms, so at `FuzzGen` on the same bytes they must build the same tree. -/

/- A compact `(left key right)` s-expression rather than `Repr`, so a pin is one line. It preserves
structure, unlike `toList`, which is not injective on trees and would pass two differently-shaped
trees with the same keys. -/
private def showOrig : BST.Tree Int → String
  | .leaf => "."
  | .node l x r => s!"({showOrig l} {x} {showOrig r})"

private def showCopy : BuggyBST.Tree → String
  | .leaf => "."
  | .node l x r => s!"({showCopy l} {x} {showCopy r})"

/- Runs both generators on one buffer, printing the shared tree so a mismatch shows what each
produced rather than just `false`. -/
private def agreeOn (bs : List UInt8) : String :=
  let lo := BuggyBST.loKey
  let hi := BuggyBST.hiKey
  let orig : FuzzGen String := showOrig <$> BST.Tree.genBST lo hi
  let copy : FuzzGen String := showCopy <$> BuggyBST.genBST lo hi
  let run (g : FuzzGen String) : Option String := (g.run { buffer := ⟨bs.toArray⟩, cursor := 0 }).map (·.1)
  match run orig, run copy with
  | some a, some b => if a == b then s!"agree: {a}" else s!"DIFFER: example={a} fuzz={b}"
  | _, _ => "one generator failed to produce a value"

/- A buffer that drives several `frequency`/`chooseInt` steps: both generators consume the bytes in
the same order and build the same tree. -/
/-- info: agree: ((. 3 .) 4 .) -/
#guard_msgs in #eval IO.println (agreeOn [1, 3, 1, 2, 0, 0, 0, 0])

/- The empty buffer takes the zero-fill path in both (`frequency` → first branch → `leaf`). -/
/-- info: agree: . -/
#guard_msgs in #eval IO.println (agreeOn [])

/- A longer buffer, exercising deeper recursion on both sides. -/
/-- info: agree: ((. 6 (. 7 .)) 8 .) -/
#guard_msgs in #eval IO.println (agreeOn [1, 7, 1, 5, 0, 1, 6, 0, 0, 1, 9, 0, 0])

/- A tree branching on both sides at depth two, so the pin covers both recursive calls rather than
just the left spine. -/
/-- info: agree: (((. 3 .) 5 .) 9 (. 10 (. 11 .))) -/
#guard_msgs in #eval IO.println (agreeOn [1, 8, 1, 4, 1, 2, 0, 0, 0, 1, 12, 1, 10, 0, 0, 0])

/-! ## `RecordGen` replays at `FuzzGen`

A run at `RecordGen` must decode, at `FuzzGen`, to the same outcome while reading exactly the bytes
it recorded: what a warm-up seed (`fuzz-run/README.md`) relies on. `readNat_recordDraw` proves it
per draw; this checks whole runs, over ranges that take one byte, several bytes, a range that is a
power of 256, and a bignum. -/

/-- A property whose failure message shows every value drawn, so "same outcome" is "same values". -/
private def propRecorded [Gen G] : PropM G Unit := do
  let a ← generate (chooseNat 0 199)
  let b ← generate (chooseNat 3 70000)
  let c ← generate (chooseNat 0 255)
  let d ← generate (chooseNat 5 5)
  let e ← generate (chooseNat (2 ^ 70) (2 ^ 70 + 2 ^ 65))
  let t ← generate (BST.Tree.genBST 0 100)
  check false s!"{a} {b} {c} {d} {e} {reprStr t}"

/-- Of `n` recorded runs from `seed`, how many replay with a different outcome or read a different
number of bytes than were recorded. -/
private def replayMismatches (n : Nat) (seed : UInt64) : Nat := Id.run do
  let mut g := SplitMix.ofSeed seed
  let mut bad := 0
  for _ in [0:n] do
    let (outcome, bytes, g') := runRecord propRecorded g
    g := g'
    let r := runOne propRecorded bytes
    let cursor := ((runProp propRecorded : FuzzGen _).run { buffer := bytes, cursor := 0 }).map (·.2.cursor)
    if renderOutcome r.outcome != renderOutcome outcome || cursor != some bytes.size then
      bad := bad + 1
  return bad

/-- info: 0 -/
#guard_msgs in #eval IO.println (replayMismatches 500 2026)

/-! ## `ChoiceFuzz`

A record is a kind byte and an LEB128 value; replay is positional, and a record that does not fit
its draw, like a draw past the end, takes the fill. These pin the decoding, that every value is in
the draw's range whatever the buffer, and that a run's realized records replay it exactly — which
is what the mutator edits and what a random phase seeds the corpus with. -/

/-- The values a choice run of `propTwo`-style draws produced, and whether each came from a record. -/
private def propPair [Gen G] : PropM G Unit := do
  let x ← generate (chooseNat 0 9)
  let y ← generate (chooseNat 100 300)
  check false s!"{x} {y}"

/- `[1, 7, 1, 172, 1]`: two `.nat` records, `7` and `172` (LEB128 `0xAC 0x01`). -/
/-- info: fail: 7 172 -/
#guard_msgs in #eval IO.println (renderOutcome (runChoiceOn propPair (bytes [1, 7, 1, 172, 1])).outcome)

/- A record out of its draw's range (`20` for `[0, 9]`) is replaced by the fill, and the next record
is still read at the next draw: replay is positional. -/
/-- info: true -/
#guard_msgs in #eval IO.println <|
  let r := runChoiceOn propPair (bytes [1, 20, 1, 172, 1])
  (renderOutcome r.outcome).endsWith " 172" && renderOutcome r.outcome != "fail: 20 172"

/- The realized records of a run replay it exactly, fill values included, with no fill used. -/
/-- info: true -/
#guard_msgs in #eval IO.println <|
  let r := runChoiceOn propPair (bytes [1, 20])
  let r' := runChoiceOn propPair r.realized
  renderOutcome r.outcome == renderOutcome r'.outcome && r.realized == r'.realized &&
    r'.bounds.get! 0 == 0

/-- Draws whose ranges depend on earlier values, checked in range: the support rule. -/
private def propInRange [Gen G] : PropM G Unit := do
  let x ← generate (chooseNat 0 100)
  let y ← generate (chooseNat x (x + 5))
  let z ← generate (chooseInt (-3) 3)
  check (x ≤ 100 && x ≤ y && y ≤ x + 5 && -3 ≤ z && z ≤ 3) s!"out of range: {x} {y} {z}"

/-- Of `n` random buffers, how many give a value outside its draw's range, or whose realized
records do not replay them. -/
private def choiceMismatches (n : Nat) (seed : UInt64) : Nat := Id.run do
  let mut g := SplitMix.ofSeed seed
  let mut bad := 0
  for _ in [0:n] do
    let (len, g1) := g.randNat 0 40
    let mut b := ByteArray.empty
    let mut g2 := g1
    for _ in [0:len] do
      let (x, g3) := g2.randNat 0 255
      b := b.push (if x < 128 then 1 else x.toUInt8)
      g2 := g3
    g := g2
    let r := runChoiceOn propRecorded b
    let r' := runChoiceOn propRecorded r.realized
    if renderOutcome r.outcome != renderOutcome r'.outcome || r.realized != r'.realized ||
        renderOutcome (runChoiceOn propInRange b).outcome != "pass" then
      bad := bad + 1
  return bad

/-- info: 0 -/
#guard_msgs in #eval IO.println (choiceMismatches 300 7)

/- A random phase's run (no records, the campaign's PRNG) replays from its realized records. -/
/-- info: 0 -/
#guard_msgs in #eval IO.println <| Id.run do
  let mut g := SplitMix.ofSeed 99
  let mut bad := 0
  for _ in [0:200] do
    let r := runChoice propRecorded ByteArray.empty g
    g := r.fill
    if renderOutcome (runChoiceOn propRecorded r.realized).outcome != renderOutcome r.outcome then
      bad := bad + 1
  return bad

/-! ### Kinds and spans

A record is used only by a draw of its own kind, so a branch index is not read as an integer; a
span is an event in the trace, not a record. -/

/-- A `chooseInt` draw (kind `.int`) then a `oneOf` (kind `.branch`). -/
private def propKinds [Gen G] : PropM G Unit := do
  let x ← generate (chooseInt 0 9)
  let b ← generate (oneOf [fun _ => pure 0, fun _ => pure 1])
  check false s!"{x} {b}"

/- Tags 2 (`.int`) and 4 (`.branch`) in order: both records are used. -/
/-- info: fail: 7 1 -/
#guard_msgs in #eval IO.println (renderOutcome (runChoiceOn propKinds (bytes [2, 7, 4, 1])).outcome)

/- The same values with their tags swapped are both misfits, so both draws come from the fill and
the realized records carry the draws' own tags. -/
/-- info: true -/
#guard_msgs in #eval IO.println <|
  let r := runChoiceOn propKinds (bytes [4, 7, 2, 1])
  r.realized.get! 0 == 2 && r.realized.get! 2 == 4 && r.bounds.get! 0 == 1

/- `oneOf`'s span around the chosen branch is an open event (flags 2) after the branch draw's bounds
and a close (flags 4) at the end; under `useKinds := false` there are none, and every tag is `.nat`. -/
/-- info: [0, 0, 9, 0, 0, 1, 2, 4] -/
#guard_msgs in #eval IO.println <|
  ((runChoiceOn propKinds (bytes [2, 7, 4, 1])).bounds.toList.take 7 ++
    [(runChoiceOn propKinds (bytes [2, 7, 4, 1])).bounds.toList.getLast!])

/-- info: true -/
#guard_msgs in #eval IO.println <|
  let r := runChoiceOn propKinds (bytes [1, 7, 1, 1]) .fresh (useKinds := false)
  renderOutcome r.outcome == "fail: 7 1" && r.realized == bytes [1, 7, 1, 1] &&
    !r.bounds.toList.any (· == 2)

