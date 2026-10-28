/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
module

public import Basalt.Fuzz.Basic
public import Basalt.Fuzz.Record
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
def go (T : PropM FuzzGen Unit) (argv : Array String := #[]) (truncate : Bool := false)
    (counters? : Option (IO.Ref (Nat × Nat)) := none) : IO Unit := do
  IO.println s!"[basalt] starting libFuzzer campaign ({argv.toList})"
  -- libFuzzer announces that the linked custom mutator disables `-len_control`; an explicit flag
  -- wins over that default (`withDefaults`), so say so.
  if let some lc := argv.find? (·.startsWith "-len_control=") then
    IO.println s!"[basalt] {lc} is explicit and overrides libFuzzer's \
      \"Disabling -len_control by default\""
  let counters ← match counters? with | some c => pure c | none => IO.mkRef (0, 0)
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

/-! ## Hybrid campaigns -/

/-- When a hybrid campaign moves between its random and coverage-guided rounds (`fuzz-run/README.md`,
"Hybrid campaigns"). Every campaign starts random. -/
inductive SwitchRule where
  /-- In both directions, once a round has gone `scale` times its stale effort without a find. -/
  | stale (scale : Float)
  /-- Once, to fuzzing, when the random round's finds level off: the window rule's `φ` and `c`. -/
  | window (level confidence : Float)
  /-- Once, to fuzzing, after this many random tests. -/
  | fixed (tests : Nat)

/-- The bridge's encoding of a rule: its tag, a count, and two parameters. -/
def SwitchRule.encode : SwitchRule → UInt8 × UInt64 × Float × Float
  | .stale scale => (0, 0, scale, 0)
  | .window level confidence => (1, 0, level, confidence)
  | .fixed tests => (2, tests.toUInt64, 0, 0)

/-- Hand the C bridge the bytes a `RecordGen` run recorded, to keep if the run reached new coverage. -/
@[extern "basalt_hybrid_offer"]
opaque hybridOfferImpl (bytes : ByteArray) : BaseIO Unit

/-- Arm a hybrid campaign in the C bridge, with `runRandom` as the random rounds' callback, the rule
as `SwitchRule.encode` gives it, and `budget` the `-runs` bound (`0`: none). -/
@[extern "basalt_hybrid_config"]
opaque hybridConfigImpl (runRandom : ByteArray → IO UInt8) (rule : UInt8) (tests : UInt64)
    (a b : Float) (budget : UInt64) : IO Unit

/-- One random test, for a random round (`tally`): libFuzzer's buffer is ignored, the run is drawn at
`RecordGen` from `gen`, and its recorded bytes go to the bridge. A failure is reported and its bytes
saved under `artifactPrefix` — a `FuzzGen` input, so `replay` reproduces it — and the bridge exits on
the `1` it returns, without letting libFuzzer save the buffer, which is not this run's input. -/
def runOneRecorded (counters : IO.Ref (Nat × Nat)) (T : PropM RecordGen Unit)
    (gen : IO.Ref SplitMix) (artifactPrefix : String) (_ : ByteArray) : IO UInt8 := do
  let (outcome, bytes, g') := runRecord T (← gen.get)
  gen.set g'
  hybridOfferImpl bytes
  tally counters outcome fun msg runs discards => do
    let path := s!"{artifactPrefix}crash-random-{runs + discards}"
    let saved ← try IO.FS.writeBinFile path bytes; pure path
      catch e => pure s!"not saved ({e})"
    reportFailure msg
      #[("input bytes", s!"{bytes.toList.map (fun b => b.toNat)}"),
        ("runs", s!"{runs} ({discards} discarded), failing in a random round"),
        ("artifact", saved)]

/-- The value of libFuzzer's `-flag=V`, if given. -/
private def strFlag? (argv : Array String) (flag : String) : Option String :=
  argv.findSome? fun a => if a.startsWith flag then some (a.drop flag.length).toString else none

/-- A hybrid campaign: random and coverage-guided rounds in one libFuzzer loop, switching by `rule`.
Every round's tests count against the one `-runs` budget. -/
def goHybrid (T : Property) (rule : SwitchRule) (argv : Array String) (truncate : Bool) :
    IO Unit := do
  let budget := (strFlag? argv "-runs=" |>.bind String.toNat?).getD 0
  IO.println s!"[basalt] hybrid campaign: random first, then {match rule with
    | .stale scale => s!"switching both ways by stale effort (scale {scale})"
    | .window level confidence => s!"fuzzing once finds level off (φ={level}, c={confidence})"
    | .fixed tests => s!"fuzzing after {tests} tests"}"
  let counters ← IO.mkRef (0, 0)
  let gen ← IO.mkRef (← SplitMix.newIO)
  let artifactPrefix := (strFlag? argv "-artifact_prefix=").getD ""
  let (tag, tests, a, b) := rule.encode
  hybridConfigImpl (runOneRecorded counters (T RecordGen) gen artifactPrefix) tag tests a b
    budget.toUInt64
  go (T FuzzGen) argv truncate counters

/-- A decimal such as `0.5` or `10`. -/
private def decimal? (s : String) : Option Float :=
  match s.splitOn "." with
  | [i] => i.toNat?.map Nat.toFloat
  | [i, f] => do
    let i ← (if i.isEmpty then some 0 else i.toNat?)
    let fn ← f.toNat?
    pure (i.toFloat + fn.toFloat / (10 ^ f.length).toFloat)
  | _ => none

/-- Basalt's flags, parsed. -/
structure FuzzFlags where
  /-- `--truncate`. -/
  truncate : Bool := false
  hybrid : Option SwitchRule := none
  /-- What goes to libFuzzer. -/
  rest : Array String := #[]
  /-- The flags given malformed, or given where nothing reads them. -/
  bad : Array String := #[]

/-- Basalt's own fuzz flags, each `--name` or `--name=value`, consumed before libFuzzer sees `argv`,
which rejects a flag it does not recognize. -/
private def ours : List String := ["--truncate", "--hybrid", "--stale-scale", "--level", "--confidence"]

/-- The value of `--name=V`, if given. -/
private def valueOf? (argv : Array String) (name : String) : Option String :=
  argv.findSome? fun a =>
    if a.startsWith (name ++ "=") then some (a.drop (name.length + 1)).toString else none

/-- Split Basalt's flags out of `argv`. A rule's parameter given without that rule is malformed. -/
def splitFlags (argv : Array String) : FuzzFlags :=
  let given (n : String) := (valueOf? argv n).isSome
  let dec (n : String) (d : Float) : Except String Float :=
    match valueOf? argv n with
    | none => .ok d
    | some v => match decimal? v with | some x => if x > 0 then .ok x else .error n | none => .error n
  let rule : Except String (Option SwitchRule) :=
    if !argv.any (fun a => a == "--hybrid" || a.startsWith "--hybrid=") then .ok none
    else match valueOf? argv "--hybrid" with
    | none | some "stale" => do pure (some (.stale (← dec "--stale-scale" 1)))
    | some "window" => do pure (some (.window (← dec "--level" 1) (← dec "--confidence" 10)))
    | some v => match v.toNat? with
      | some n => if n > 0 then .ok (some (.fixed n)) else .error "--hybrid"
      | none => .error "--hybrid"
  let isOurs (a : String) := ours.any fun f => a == f || a.startsWith (f ++ "=")
  let stray (r : Option SwitchRule) : Array String :=
    let stale := match r with | some (.stale _) => true | _ => false
    let window := match r with | some (.window ..) => true | _ => false
    (if given "--stale-scale" && !stale then #["--stale-scale"] else #[]) ++
    #["--level", "--confidence"].filter (fun n => given n && !window)
  let f : FuzzFlags := { truncate := argv.contains "--truncate", rest := argv.filter (!isOurs ·),
                         bad := argv.filter (·.startsWith "--truncate=") }
  match rule with
  | .ok r => { f with hybrid := r, bad := f.bad ++ stray r }
  | .error n => { f with bad := f.bad.push n }

/-- libFuzzer's defaults where Basalt's differ, each only if `argv` does not set it. Linking a
custom mutator makes libFuzzer disable its `-len_control` length ramp; a plain campaign does not need
it off, so libFuzzer's own default comes back. A hybrid campaign keeps the ramp off and raises
`-max_len` from libFuzzer's cold-start 4096: a random round's seeds are as long as their runs read,
and the ramp would hold their mutations to that length for most of the campaign. -/
def withDefaults (hybrid : Bool) (argv : Array String) : Array String :=
  let set (flag value : String) (a : Array String) :=
    if a.any (·.startsWith flag) then a else a.push (flag ++ value)
  if hybrid then argv |> set "-len_control=" "0" |> set "-max_len=" "65536"
  else argv |> set "-len_control=" "100"

/-- The coverage-guided backend, for `Basalt.PBT.dispatch`. `--truncate` and `--hybrid` are Basalt's own
(`fuzz-run/README.md`); the rest of `argv` goes to libFuzzer, and a saved artifact — which *is* a
`FuzzGen` input buffer — can be replayed. -/
@[basalt_backend]
def fuzzBackend : Backend where
  name := "fuzz"
  campaign T argv := do
    let f := splitFlags argv
    if !f.bad.isEmpty then
      usageError s!"malformed: {f.bad.toList}; --truncate takes no value, --hybrid is stale, window or \
        a number of tests, --stale-scale (stale only), --level and --confidence (window only) take a \
        positive decimal"
    match f.hybrid with
    | some rule => goHybrid T rule (withDefaults true f.rest) f.truncate
    | none => go (T FuzzGen) (withDefaults false f.rest) f.truncate
  replay? := some (fun T path => replay (T FuzzGen) path)

/-- Random `IO` choices, run and coverage-counted by libFuzzer (`goRandom`): the baseline that
`fuzz`'s coverage is compared against. -/
@[basalt_backend]
def ioUnderFuzzBackend : Backend where
  name := "io-libfuzzer"
  campaign T argv := goRandom (T IO) argv
  replay? := none

end Basalt.Fuzz
