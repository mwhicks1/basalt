/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
module

public import Basalt.Fuzz.Basic
public import Basalt.IO
public import Basalt.PBT.Driver

/-!
# Running a property under libFuzzer

The Lean half of the C bridge in `Basalt/Fuzz/native.c`: `go` hands libFuzzer's driver a per-input
closure, and libFuzzer calls back into `runOneIO` once per mutated input. A failing input is reported
through `Basalt.PBT`'s shared failure contract and then crashes the process, which is how libFuzzer
saves the input as an artifact; `replay` consumes one.
-/

public section

namespace Basalt.Fuzz

open Basalt.PBT

/-- The C bridge: store `run` as the per-input callback, then hand `argv` to libFuzzer's driver.
Blocks in the fuzzing loop; libFuzzer parses its own flags from `argv`. `guided` says that `run`
reads libFuzzer's buffer (without it the buffer is ignored), and `truncate` arms `--truncate`.
Returns only if the campaign completes without a failure (a failure aborts the process). -/
@[extern "basalt_fuzz_go"]
opaque goImpl (run : ByteArray → IO UInt8) (argv : Array String) (guided truncate : Bool) : IO Unit

/-- Called at the conclusion of a run to report to the C code how many bytes it read
(`FuzzResult.cursor`), which `--truncate` cuts the next mutation of its input to. -/
@[extern "basalt_fuzz_note_cursor"]
opaque noteCursorImpl (cursor : UInt64) : BaseIO Unit

/-- Count a run's outcome in `counters` and give the C bridge its code: `0` = pass, `1` = failed,
`2` = discard. A failure is reported by `onFail` with the tests run so far (`runs`, then discards)
before `1` is returned, since the bridge then aborts. The tally is kept here because libFuzzer's own
`#N` markers count only corpus-worthy inputs, which is not the number of tests run. -/
def tally (counters : IO.Ref (Nat × Nat)) (outcome : TestOutcome)
    (onFail : String → Nat → Nat → IO Unit) : IO UInt8 := do
  match outcome with
  | Except.ok () => counters.modify (fun (r, d) => (r + 1, d)); pure 0
  | Except.error .discard => counters.modify (fun (r, d) => (r, d + 1)); pure 2
  | Except.error (.fail msg) =>
    counters.modify (fun (r, d) => (r + 1, d))
    let (runs, discards) ← counters.get
    onFail msg runs discards
    pure 1

/-- Run the property on one input, for the C bridge (`tally`). -/
def runOneIO (counters : IO.Ref (Nat × Nat)) (T : PropM FuzzGen Unit)
    (bytes : ByteArray) : IO UInt8 := do
  let r := runOne T bytes -- run the property test
  noteCursorImpl r.cursor.toUInt64 -- the bytes it read, for `--truncate`
  tally counters r.outcome fun msg runs discards =>
    reportFailure msg
      #[("input bytes", s!"{bytes.toList.map (fun b => b.toNat)}"),
        ("runs", s!"{runs} ({discards} discarded)"),
        ("buffer", s!"{bytes.size} bytes, {r.deficit} short")]

/-- Start a fuzzing campaign for property `T`. `argv` is forwarded to libFuzzer (corpus dirs,
`-runs`, `-max_len`, `-artifact_prefix`, …). A failure aborts the process, with the artifact saved and
the exit code set by libFuzzer. -/
def go (T : PropM FuzzGen Unit) (argv : Array String := #[]) (truncate : Bool := false) :
    IO Unit := do
  IO.println s!"[basalt] starting libFuzzer campaign ({argv.toList})"
  -- libFuzzer announces that the linked custom mutator disables `-len_control`; an explicit flag
  -- wins over that default (`withDefaults`), so say so.
  if let some lc := argv.find? (·.startsWith "-len_control=") then
    IO.println s!"[basalt] {lc} is explicit and overrides libFuzzer's \
      \"Disabling -len_control by default\""
  let counters ← IO.mkRef (0, 0)
  -- Report nothing after `goImpl`: libFuzzer `exit()`s when `-runs` is exhausted, so a line placed
  -- there silently never appears (the tally lives in `runOneIO`, the statistics in an `atexit`).
  goImpl (fun bytes => runOneIO counters T bytes) argv true truncate

/-- Run the property once at `IO`, ignoring libFuzzer's buffer (`tally`). A failure is reported with
no input bytes: the choices came from the PRNG. -/
def runOneRandom (counters : IO.Ref (Nat × Nat)) (T : PropM IO Unit) (_ : ByteArray) : IO UInt8 := do
  tally counters (← runProp T) fun msg runs discards =>
    reportFailure msg #[("runs", s!"{runs} ({discards} discarded)")]

/-- A *random* campaign run inside libFuzzer's loop: every input is drawn at `IO` and libFuzzer's
buffer is ignored, so nothing guides the search, but the same binary, instrumentation, and counters
as `go` are in place. This is the control arm of a coverage comparison (`BASALT_COV_OUT`,
`fuzz-run/README.md`), with only the source of the choices changed. -/
def goRandom (T : PropM IO Unit) (argv : Array String := #[]) : IO Unit := do
  IO.println s!"[basalt] starting random campaign under libFuzzer ({argv.toList})"
  let counters ← IO.mkRef (0, 0)
  goImpl (runOneRandom counters T) argv false false

/-- Replay one saved input file against a property (no fuzzer): reproduces the outcome
deterministically and prints it. This is how a saved artifact (`crash-…`) is consumed.

The bytes alone are the whole reproduction: zero-extension is a property of `readByte`, not a
campaign setting, so an artifact means the same thing however it was produced. -/
def replay (T : PropM FuzzGen Unit) (path : String) : IO Unit := do
  let bytes ← IO.FS.readBinFile path
  IO.println s!"[basalt] replaying {path} ({bytes.size} bytes)"
  let r := runOne T bytes
  match r.outcome with
  | Except.ok () => IO.println s!"outcome: pass ({r.deficit} bytes short)"
  | Except.error .discard => IO.println s!"outcome: discard ({r.deficit} bytes short)"
  | Except.error (.fail msg) => reportFailure msg

/-- Basalt's flags, parsed. -/
structure FuzzFlags where
  /-- `--truncate`. -/
  truncate : Bool := false
  /-- What goes to libFuzzer. -/
  rest : Array String := #[]
  /-- The flags given malformed. -/
  bad : Array String := #[]

/-- Basalt's own fuzz flags, consumed before libFuzzer sees `argv`, which rejects a flag it does not
recognize. -/
private def ours : List String := ["--truncate"]

/-- Split Basalt's flags out of `argv`. -/
def splitFlags (argv : Array String) : FuzzFlags :=
  let isOurs (a : String) := ours.any fun f => a == f || a.startsWith (f ++ "=")
  { truncate := argv.contains "--truncate", rest := argv.filter (!isOurs ·),
    bad := argv.filter (·.startsWith "--truncate=") }

/-- libFuzzer's defaults where Basalt's differ, each only if `argv` does not set it. Linking a
custom mutator makes libFuzzer disable its `-len_control` length ramp; nothing here needs it off,
so libFuzzer's own default comes back. -/
def withDefaults (argv : Array String) : Array String :=
  if argv.any (·.startsWith "-len_control=") then argv else argv.push "-len_control=100"

/-- The coverage-guided backend, for `Basalt.PBT.dispatch`. `--truncate` is Basalt's own
(`fuzz-run/README.md`); the rest of `argv` goes to libFuzzer, and a saved artifact — which *is* a
`FuzzGen` input buffer — can be replayed. -/
@[basalt_backend]
def fuzzBackend : Backend where
  name := "fuzz"
  campaign T argv := do
    let f := splitFlags argv
    if !f.bad.isEmpty then usageError s!"malformed: {f.bad.toList}; --truncate takes no value"
    go (T FuzzGen) (withDefaults f.rest) f.truncate
  replay? := some (fun T path => replay (T FuzzGen) path)

/-- Random `IO` choices, run and coverage-counted by libFuzzer (`goRandom`): the baseline that
`fuzz`'s coverage is compared against. -/
@[basalt_backend]
def ioUnderFuzzBackend : Backend where
  name := "io-libfuzzer"
  campaign T argv := goRandom (T IO) argv
  replay? := none

end Basalt.Fuzz
