/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
module

public import Basalt.PBT.Property

/-!
# The `FuzzGen` interpretation

`FuzzGen` is an executable interpretation of `Gen` whose `choose` results are decided by an external
coverage-guided fuzzer rather than by a PRNG: the fuzzer proposes a byte buffer, `choose` reads bytes
from it to select each value, and coverage of the generator and the property guides its mutations
("parametric fuzzing"). Because `choose` is total, a whole fuzzer input is a pure function
`ByteArray → FuzzResult` (`runOne`).
-/

public section

namespace Basalt.Fuzz

open Basalt.PBT

/-- State threaded through one fuzzer input: the fuzzer-controlled byte buffer and a read cursor.
The cursor is *not* clamped to the buffer, so how far it overshoots is the input's unmet demand
(`FuzzResult.deficit`). -/
structure FuzzState where
  buffer : ByteArray
  cursor : Nat
  /-- When recording, four 64-bit little-endian words per draw of more than one outcome below `2^64`:
  `lo`, `hi`, the value, and the cursor where the draw's bytes start. Packed, since a boxed word per
  element would cost an allocation each. -/
  trace : Option ByteArray := none

/-- A fuzzer-driven interpretation of `Gen`: `choose` reads bytes from an externally supplied buffer.

The `Option` base is there to adjoin the bottom element `partial_fixpoint` needs, which the raw state
`α × FuzzState` has no source of for an arbitrary `α`. It is a compile-time device only: a productive
generator always yields `some`, and a divergent one loops (caught by libFuzzer's `-timeout`) rather
than returning `none`. -/
abbrev FuzzGen (α : Type) := StateT FuzzState Option α

instance : Inhabited (FuzzGen α) :=
  ⟨fun _ => none⟩

/-- Bits needed to distinguish `k` outcomes (0 when `k ≤ 1`). -/
@[expose] def bitsFor (k : Nat) : Nat :=
  if k ≤ 1 then 0 else (k - 1).log2 + 1

/-- Bytes needed to distinguish `k` outcomes: the smallest count covering `bitsFor k`. Reading the
*fewest* bytes per range keeps a tight, mutation-friendly map from input bytes to choices. -/
@[expose] def bytesFor (k : Nat) : Nat := (bitsFor k + 7) / 8

/-- Read one byte, advancing the cursor. Past the end of the buffer, read `0`: the buffer is
zero-extended rather than exhausted, which is what keeps `choose` total. The cursor still advances, so
the overshoot survives as the run's `deficit`. -/
@[expose] def readByte (s : FuzzState) : UInt8 × FuzzState :=
  let b := if s.cursor < s.buffer.size then s.buffer.get! s.cursor else 0
  (b, { s with cursor := s.cursor + 1 })

/-- Read `n` more bytes big-endian onto `acc`, advancing the cursor. -/
@[expose] def readNatFrom (acc : Nat) (s : FuzzState) : Nat → Nat × FuzzState
  | 0 => (acc, s)
  | n + 1 => let (b, s') := readByte s; readNatFrom (acc * 256 + b.toNat) s' n

/-- Read `n` bytes big-endian as a `Nat`, advancing the cursor (zero-filling past end-of-buffer). -/
@[expose] def readNat (s : FuzzState) (n : Nat) : Nat × FuzzState := readNatFrom 0 s n

/-- `x`'s low eight bytes, little-endian, appended to `b`. -/
@[expose] def pushWord (b : ByteArray) (x : Nat) : ByteArray :=
  let w := x.toUInt64
  b.push w.toUInt8 |>.push (w >>> 8).toUInt8 |>.push (w >>> 16).toUInt8 |>.push (w >>> 24).toUInt8
    |>.push (w >>> 32).toUInt8 |>.push (w >>> 40).toUInt8 |>.push (w >>> 48).toUInt8
    |>.push (w >>> 56).toUInt8

/-- One draw in `[lo, hi]`: read `bytesFor (hi - lo + 1)` bytes, recording the draw if the state
records and the draw fits the trace's words. `raw` is returned; the value is `lo + raw % (hi - lo + 1)`. -/
@[expose] def drawStep (lo hi : Nat) (s : FuzzState) : Nat × FuzzState :=
  let range := hi - lo + 1
  let c0 := s.cursor
  let (raw, s) := readNat s (bytesFor range)
  match s.trace with
  | none => (raw, s)
  | some t =>
    if range ≤ 1 || hi ≥ 2 ^ 64 then (raw, s) else
    -- Clear the field first, so that `t` is unshared and the pushes happen in place.
    let s := { s with trace := none }
    (raw, { s with trace := some (pushWord (pushWord (pushWord (pushWord t lo) hi)
                                    (lo + raw % range)) c0) })

/-- `choose` consumes `bytesFor (hi - lo + 1)` bytes and reduces them into `[lo, hi]`. Total. -/
instance : RandomChoice FuzzGen where
  choose lo hi h := do
    let raw ← modifyGet (drawStep lo hi)
    have := Nat.mod_lt raw (show hi - lo + 1 > 0 by omega)
    pure (ULift.up ⟨lo + raw % (hi - lo + 1), by omega⟩)

/-- `FuzzGen` has everything a generator needs. -/
example : Gen FuzzGen := inferInstance

/-- What one input produced: its outcome, how many bytes it read (`cursor`, past the end
included), and how many of those it was not given (the `deficit`). -/
structure FuzzResult where
  outcome : TestOutcome
  deficit : Nat
  cursor : Nat
  /-- The draws, if recorded (`FuzzState.trace`). -/
  trace : ByteArray := .empty
  deriving Inhabited

/-- Run a property on one input buffer — the pure core the C bridge calls per input. The `none` case
is the `partial_fixpoint` bottom, unreachable for a productive generator; we map it to `discard` for
totality, with nothing read to report. `record` records the draws. -/
def runOne (T : PropM FuzzGen Unit) (bytes : ByteArray) (record : Bool := false) : FuzzResult :=
  let s0 : FuzzState :=
    { buffer := bytes, cursor := 0, trace := if record then some (.emptyWithCapacity 1024) else none }
  match (runProp T).run s0 with
  | some (outcome, s) => { outcome, deficit := s.cursor - bytes.size, cursor := s.cursor,
                           trace := s.trace.getD .empty }
  | none              => { outcome := Except.error .discard, deficit := 0, cursor := 0 }

end Basalt.Fuzz
