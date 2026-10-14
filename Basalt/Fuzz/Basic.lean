/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Basalt.PBT.Property

/-!
# The `FuzzGen` interpretation

`FuzzGen` is an executable interpretation of `Gen` whose `choose` results are decided by an external
coverage-guided fuzzer rather than by a PRNG: the fuzzer proposes a byte buffer, `choose` reads bytes
from it to select each value, and coverage of the generator and the property guides its mutations
("parametric fuzzing"). Because `choose` is total, a whole fuzzer input is a pure function
`ByteArray → FuzzResult` (`runOne`).
-/

namespace Basalt.Fuzz

open Basalt.PBT

/-- State threaded through one fuzzer input: the fuzzer-controlled byte buffer and a read cursor.
The cursor is *not* clamped to the buffer, so how far it overshoots is the input's unmet demand
(`FuzzResult.deficit`). -/
structure FuzzState where
  buffer : ByteArray
  cursor : Nat
  /-- What a read past the end returns: `none` reads `0`; `some seed` reads `fillByte seed i` at
  position `i`, a seeded random byte (`FuzzConfig.randomFill`). -/
  fill : Option UInt64 := none
  /-- When recording, four words per non-unit draw: `lo`, `hi`, the value, and the cursor before
  the draw (each truncated to 64 bits). -/
  trace : Option (Array UInt64) := none

/-- A fuzzer-driven interpretation of `Gen`: `choose` reads bytes from an externally supplied buffer.

The `Option` base is there to adjoin the bottom element `partial_fixpoint` needs, which the raw state
`α × FuzzState` has no source of for an arbitrary `α`. It is a compile-time device only: a productive
generator always yields `some`, and a divergent one loops (caught by libFuzzer's `-timeout`) rather
than returning `none`. -/
abbrev FuzzGen (α : Type) := StateT FuzzState Option α

instance : Inhabited (FuzzGen α) :=
  ⟨fun _ => none⟩

/-- Bits needed to distinguish `k` outcomes (0 when `k ≤ 1`). -/
def bitsFor (k : Nat) : Nat :=
  if k ≤ 1 then 0 else (k - 1).log2 + 1

/-- Bytes needed to distinguish `k` outcomes: the smallest count covering `bitsFor k`. Reading the
*fewest* bytes per range keeps a tight, mutation-friendly map from input bytes to choices. -/
def bytesFor (k : Nat) : Nat := (bitsFor k + 7) / 8

/-- SplitMix64's output finalizer. `native.c`'s `basalt_mix64` is the same function: `--grow` under
random fill materializes the bytes a run read past its end, so the two must agree: both pin
`mix64 1`, here in `BasaltTest/Fuzz.lean` and there at startup. -/
def mix64 (z : UInt64) : UInt64 :=
  let z := (z ^^^ (z >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

/-- The random-fill byte at position `i` of a buffer whose fill seed is `seed`. -/
def fillByte (seed : UInt64) (i : Nat) : UInt8 :=
  (mix64 (seed + (i.toUInt64 + 1) * 0x9e3779b97f4a7c15)).toUInt8

/-- A buffer's fill seed: FNV-1a over its bytes, finalized. A function of the buffer alone, so a
saved input replays the same under random fill. -/
def fillSeed (b : ByteArray) : UInt64 :=
  mix64 (b.foldl (fun h x => (h ^^^ x.toUInt64) * 0x100000001b3) 0xcbf29ce484222325)

/-- Read one byte, advancing the cursor. Past the end of the buffer, read the fill: `0` by default
(zero-extension), which is what keeps `choose` total. The cursor still advances, so the overshoot
survives as the run's `deficit` — which is what lets the fuzzer be told to supply the missing bytes
(`fuzz-run/README.md`). -/
def readByte (s : FuzzState) : UInt8 × FuzzState :=
  let b := if s.cursor < s.buffer.size then s.buffer.get! s.cursor else
    match s.fill with
    | none => 0
    | some seed => fillByte seed s.cursor
  (b, { s with cursor := s.cursor + 1 })

/-- Read `n` more bytes big-endian onto `acc`, advancing the cursor. -/
def readNatFrom (acc : Nat) (s : FuzzState) : Nat → Nat × FuzzState
  | 0 => (acc, s)
  | n + 1 => let (b, s') := readByte s; readNatFrom (acc * 256 + b.toNat) s' n

/-- Read `n` bytes big-endian as a `Nat`, advancing the cursor (zero-filling past end-of-buffer). -/
def readNat (s : FuzzState) (n : Nat) : Nat × FuzzState := readNatFrom 0 s n

/-- One draw in `[lo, hi]`: read `bytesFor (hi - lo + 1)` bytes and reduce them into the range,
recording the draw if the state records. The value is `lo + raw % range`; `raw` is returned. -/
def drawStep (lo hi : Nat) (s : FuzzState) : Nat × FuzzState :=
  let range := hi - lo + 1
  let c0 := s.cursor
  let (raw, s) := readNat s (bytesFor range)
  match s.trace with
  | none => (raw, s)
  | some t =>
    if range ≤ 1 then (raw, s) else
    (raw, { s with trace := some (t.push lo.toUInt64 |>.push hi.toUInt64
                                    |>.push (lo + raw % range).toUInt64 |>.push c0.toUInt64) })

/-- `choose` consumes `bytesFor (hi - lo + 1)` bytes and reduces them into `[lo, hi]`. Total. -/
instance : RandomChoice FuzzGen where
  choose lo hi h := do
    let raw ← modifyGet (drawStep lo hi)
    have := Nat.mod_lt raw (show hi - lo + 1 > 0 by omega)
    pure (ULift.up ⟨lo + raw % (hi - lo + 1), by omega⟩)

/-- `FuzzGen` has everything a generator needs. -/
example : Gen FuzzGen := inferInstance

/-- What one input produced: its outcome, and how many bytes it wanted beyond the ones it was
given (the `deficit`). -/
structure FuzzResult where
  outcome : TestOutcome
  deficit : Nat
  /-- How many bytes the run read, in or past the buffer. -/
  cursor : Nat := 0
  /-- The fill seed, if the run filled at random. -/
  seed : UInt64 := 0
  /-- The draws, if recorded (`FuzzState.trace`). -/
  trace : Array UInt64 := #[]
  deriving Inhabited

/-- How `runOne` decodes past the end, and whether it records. Defaults are the original `FuzzGen`. -/
structure FuzzConfig where
  randomFill : Bool := false
  record : Bool := false

/-- Run a property on one input buffer — the pure core the C bridge calls per input. The `none` case
is the `partial_fixpoint` bottom, unreachable for a productive generator; we map it to `discard` for
totality, with no deficit to report. -/
def runOne (T : PropM FuzzGen Unit) (bytes : ByteArray) (cfg : FuzzConfig := {}) : FuzzResult :=
  let seed := if cfg.randomFill then fillSeed bytes else 0
  let s0 : FuzzState := { buffer := bytes, cursor := 0,
                          fill := if cfg.randomFill then some seed else none,
                          trace := if cfg.record then some (Array.mkEmpty 256) else none }
  match (runProp T).run s0 with
  | some (outcome, s) => { outcome, deficit := s.cursor - bytes.size, cursor := s.cursor, seed,
                           trace := s.trace.getD #[] }
  | none              => { outcome := Except.error .discard, deficit := 0, seed }

end Basalt.Fuzz
