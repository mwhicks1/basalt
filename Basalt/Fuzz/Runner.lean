/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Basalt.Fuzz.Basic
import Basalt.Fuzz.Record
import Basalt.PBT.Driver

/-!
# Running a property under libFuzzer

The Lean half of the C bridge in `Basalt/Fuzz/native.c`: `go` hands libFuzzer's driver a per-input
closure, and libFuzzer calls back into `runOneIO` once per mutated input. A failing input is reported
through `Basalt.PBT`'s shared failure contract and then crashes the process, which is how libFuzzer
saves the input as an artifact; `replay` consumes one.
-/

namespace Basalt.Fuzz

open Basalt.PBT

/-- The C bridge: store `run` as the per-input callback, then hand `argv` to libFuzzer's driver.
Blocks in the fuzzing loop; libFuzzer parses its own flags from `argv`. `grow` arms the custom
mutator's buffer extension. Returns only if the campaign completes without a failure (a failure
aborts the process). -/
@[extern "basalt_fuzz_go"]
opaque goImpl (run : ByteArray → IO UInt8) (argv : Array String) (grow : Bool) : IO Unit

/-- Called at the conclusion of a run to report to the C code the deficit in the buffer,
i.e., the difference N - S between requested bytes N and available bytes S. -/
@[extern "basalt_fuzz_note_deficit"]
opaque noteDeficitImpl (deficit : UInt32) : BaseIO Unit

/-- Run the property on one input, reporting the byte codes the C bridge expects: `0` = pass,
`1` = failed (the bridge then aborts, so the report must already be flushed), `2` = discard.

`counters` tallies executions and discards so a failing campaign can report the same run line the
other backends do — libFuzzer's own `#N` markers count only corpus-worthy inputs, which is not the
number of tests run. -/
def runOneIO (counters : IO.Ref (Nat × Nat)) (T : PropM FuzzGen Unit)
    (bytes : ByteArray) : IO UInt8 := do
  let r := runOne T bytes -- run the property test
  noteDeficitImpl (UInt32.ofNatClamp r.deficit) -- note any bytes deficit
  match r.outcome with
  | Except.ok () => counters.modify (fun (runs, discards) => (runs + 1, discards)); pure 0
  | Except.error .discard => counters.modify (fun (r, d) => (r, d + 1)); pure 2
  | Except.error (.fail msg) =>
    counters.modify (fun (runs, discards) => (runs + 1, discards))
    let (runs, discards) ← counters.get
    reportFailure msg
      #[("input bytes", s!"{bytes.toList.map (fun b => b.toNat)}"),
        ("runs", s!"{runs} ({discards} discarded)"),
        ("buffer", s!"{bytes.size} bytes, {r.deficit} short")]
    pure 1

/-- Hand the C bridge the bytes a `RecordGen` run recorded, to keep if the run reached new coverage. -/
@[extern "basalt_hybrid_offer"]
opaque hybridOfferImpl (bytes : ByteArray) : BaseIO Unit

/-- How a hybrid campaign moves between random and coverage-guided phases (`fuzz-run/README.md`,
"Random warm-up"). The first phase is random and lasts at most `firstMax` tests (`0`: no cap); it
ends earlier on the leveling-off rule if `adaptive`, and with `switchBack` every later phase ends on
it too. `minWindow`, `level`, and `confidence` are the rule's `K`, `φ`, and `c`. -/
structure HybridConfig where
  firstMax : Nat := 0
  minWindow : Nat := 0
  level : Float := 1
  confidence : Float := 10
  adaptive : Bool := false
  switchBack : Bool := false

/-- Arm a hybrid campaign in the C bridge, with `runRandom` as the random phases' callback and
`budget` the `-runs` bound (`0`: none). -/
@[extern "basalt_hybrid_config"]
opaque hybridConfigImpl (runRandom : ByteArray → IO UInt8) (firstMax minWindow : UInt64)
    (level confidence : Float) (budget : UInt64) (adaptive switchBack : Bool) : IO Unit

/-- One random test, for a random phase: libFuzzer's buffer is ignored, the run is drawn at
`RecordGen` from `gen`, and its recorded bytes go to the bridge. A failure is reported here, its
bytes saved under `artifactPrefix` — a `FuzzGen` input, so `replay` reproduces it — and the bridge
exits on the `1` it returns, without letting libFuzzer save the buffer, which is not this run's
input. -/
def runOneRecorded (counters : IO.Ref (Nat × Nat)) (T : PropM RecordGen Unit)
    (gen : IO.Ref SplitMix) (artifactPrefix : String) (_ : ByteArray) : IO UInt8 := do
  let (outcome, bytes, g') := runRecord T (← gen.get)
  gen.set g'
  hybridOfferImpl bytes
  match outcome with
  | Except.ok () => counters.modify (fun (runs, discards) => (runs + 1, discards)); pure 0
  | Except.error .discard => counters.modify (fun (r, d) => (r, d + 1)); pure 2
  | Except.error (.fail msg) =>
    counters.modify (fun (runs, discards) => (runs + 1, discards))
    let (runs, discards) ← counters.get
    let path := s!"{artifactPrefix}crash-random-{runs + discards}"
    IO.FS.writeBinFile path bytes
    reportFailure msg
      #[("input bytes", s!"{bytes.toList.map (fun b => b.toNat)}"),
        ("runs", s!"{runs} ({discards} discarded), failing in a random phase"),
        ("artifact", path)]
    pure 1

/-- Start a fuzzing campaign for property `T`. `argv` is forwarded to libFuzzer (corpus dirs,
`-runs`, `-max_len`, `-artifact_prefix`, …). A failure aborts the process, with the artifact saved and
the exit code set by libFuzzer. -/
def go (T : PropM FuzzGen Unit) (argv : Array String := #[]) (grow : Bool := false)
    (counters? : Option (IO.Ref (Nat × Nat)) := none) : IO Unit := do
  IO.println s!"[basalt] starting libFuzzer campaign (grow={grow}, {argv.toList})"
  -- libFuzzer announces that the linked custom mutator disables `-len_control` on every campaign,
  -- `--grow` or not; an explicit flag wins over that default (`splitFlags`), so say so.
  if let some lc := argv.find? (·.startsWith "-len_control=") then
    IO.println s!"[basalt] {lc} is explicit and overrides libFuzzer's \
      \"Disabling -len_control by default\""
  let counters ← match counters? with | some c => pure c | none => IO.mkRef (0, 0)
  -- Report nothing after `goImpl`: libFuzzer `exit()`s when `-runs` is exhausted, so a line placed
  -- there silently never appears (the tally lives in `runOneIO`, the statistics in an `atexit`).
  goImpl (fun bytes => runOneIO counters T bytes) argv grow

/-- Run the property once at `IO`, ignoring libFuzzer's buffer, with the byte codes `runOneIO` uses.
A failure is reported the same way; its `input bytes` are meaningless, since the choices came from
the PRNG. -/
def runOneRandom (counters : IO.Ref (Nat × Nat)) (T : PropM IO Unit) (_ : ByteArray) : IO UInt8 := do
  match (← runProp T) with
  | Except.ok () => counters.modify (fun (runs, discards) => (runs + 1, discards)); pure 0
  | Except.error .discard => counters.modify (fun (r, d) => (r, d + 1)); pure 2
  | Except.error (.fail msg) =>
    counters.modify (fun (runs, discards) => (runs + 1, discards))
    let (runs, discards) ← counters.get
    reportFailure msg #[("runs", s!"{runs} ({discards} discarded)")]
    pure 1

/-- A *random* campaign run inside libFuzzer's loop: every input is drawn at `IO` and libFuzzer's
buffer is ignored, so nothing guides the search, but libFuzzer still counts the coverage each run
reaches. This is the control arm of a coverage comparison: the same binary, instrumentation, and
counters as `go`, with only the source of the choices changed. -/
def goRandom (T : PropM IO Unit) (argv : Array String := #[]) : IO Unit := do
  IO.println s!"[basalt] starting random campaign under libFuzzer ({argv.toList})"
  let counters ← IO.mkRef (0, 0)
  goImpl (runOneRandom counters T) argv false

/-- Replay one saved input file against a property (no fuzzer): reproduces the outcome
deterministically and prints it. This is how a saved artifact (`crash-…`) is consumed.

The bytes alone are the whole reproduction: zero-extension is a property of `readByte`, not a
campaign setting, so an artifact means the same thing however it was produced — including one grown
by `--grow`, which is already whatever length the failing run read. -/
def replay (T : PropM FuzzGen Unit) (path : String) : IO Unit := do
  let bytes ← IO.FS.readBinFile path
  IO.println s!"[basalt] replaying {path} ({bytes.size} bytes)"
  let r := runOne T bytes
  match r.outcome with
  | Except.ok () => IO.println s!"outcome: pass ({r.deficit} bytes short)"
  | Except.error .discard => IO.println s!"outcome: discard ({r.deficit} bytes short)"
  | Except.error (.fail msg) => reportFailure msg

/-- Basalt's own fuzz flags, split out of `argv`: libFuzzer rejects a flag it does not recognize, so
what we consume must not be forwarded. `bad` collects the ones given malformed. -/
structure FuzzFlags where
  grow : Bool := false
  hybrid : Option HybridConfig := none
  bad : Array String := #[]

/-- A decimal such as `0.5` or `10`. -/
private def decimal? (s : String) : Option Float :=
  match s.splitOn "." with
  | [i] => i.toNat?.map Nat.toFloat
  | [i, f] => do
    let i ← (if i.isEmpty then some 0 else i.toNat?)
    let fn ← f.toNat?
    pure (i.toFloat + fn.toFloat / (10 ^ f.length).toFloat)
  | _ => none

/-- Basalt's flags, each `--name` or `--name=value`. -/
private def ours : List String :=
  ["--grow", "--warmup", "--warmup-stall", "--switch-back", "--level", "--confidence"]

private def isOurs (a : String) : Bool :=
  ours.any fun f => a == f || a.startsWith (f ++ "=")

/-- The value of `--name=V`, if given. -/
private def valueOf? (argv : Array String) (name : String) : Option String :=
  argv.findSome? fun a =>
    if a.startsWith (name ++ "=") then some (a.drop (name.length + 1)).toString else none

def splitFlags (argv : Array String) : FuzzFlags × Array String :=
  let grow := argv.contains "--grow"
  let nat (n : String) : Option (Option Nat) := (valueOf? argv n).map String.toNat?
  let dec (n : String) : Option (Option Float) := (valueOf? argv n).map decimal?
  let bad := argv.filter (fun a => a.startsWith "--grow=" || a.startsWith "--switch-back=") ++
    #["--warmup", "--warmup-stall", "--level", "--confidence"].filter fun n =>
    (argv.contains n) ||
    (match nat n, dec n with
     | some none, _ => n == "--warmup" || n == "--warmup-stall"
     | _, some none => n == "--level" || n == "--confidence"
     | _, _ => false)
  let first := (nat "--warmup").join
  let stall := (nat "--warmup-stall").join
  let switchBack := argv.contains "--switch-back"
  let hybrid : Option HybridConfig :=
    if first.isNone && stall.isNone && !switchBack then none
    else some { firstMax := first.getD 0, minWindow := stall.getD 0,
                level := ((dec "--level").join).getD 1,
                confidence := ((dec "--confidence").join).getD 10,
                adaptive := stall.isSome || switchBack, switchBack }
  let rest := argv.filter (!isOurs ·)
  -- `-max_len` bounds the buffer and so bounds the structure growth can build; libFuzzer's own
  -- default derives it from the seed corpus, which is 4096 at a cold start. Left there it, and not
  -- the property, decides how far growth gets. A random phase's seeds are as long as their runs
  -- read, so the same holds for the inputs mutated from them.
  let long := grow || hybrid.isSome
  let rest := if long && !rest.any (·.startsWith "-max_len=") then rest.push "-max_len=65536"
              else rest
  -- Linking a custom mutator makes libFuzzer disable its `-len_control` length ramp, which is what
  -- growth wants: the mutator, not the ramp, decides how long an input needs to be. A hybrid
  -- campaign wants it off too: the ramp would hold each seed's mutations to the seed's own length
  -- for most of the campaign. Otherwise there is no mutator decision to make, so restore
  -- libFuzzer's own default and leave the campaign as it was. Only an *absent* flag is defaulted —
  -- passing `-len_control=N` explicitly (including `0`) wins, which is how the modes are compared
  -- under one length regime.
  let rest := if !long && !rest.any (·.startsWith "-len_control=") then
                rest.push "-len_control=100"
              else rest
  ({ grow, hybrid, bad }, rest)

/-- The value of libFuzzer's `-flag=V`, if given. -/
private def strFlag? (argv : Array String) (flag : String) : Option String :=
  argv.findSome? fun a => if a.startsWith flag then some (a.drop flag.length).toString else none

/-- A hybrid campaign: random and coverage-guided phases in one libFuzzer loop, switching as `cfg`
says. Every phase's tests count against the one `-runs` budget. -/
def goHybrid (T : Property) (cfg : HybridConfig) (grow : Bool) (argv : Array String) : IO Unit := do
  let budget := (strFlag? argv "-runs=" |>.bind String.toNat?).getD 0
  IO.println s!"[basalt] hybrid campaign: random first\
    {if cfg.firstMax == 0 then "" else s!" (at most {cfg.firstMax} tests)"}\
    {if cfg.adaptive then s!", switching when coverage levels off (K={cfg.minWindow}, \
      level={cfg.level}, confidence={cfg.confidence})" else ""}\
    {if cfg.switchBack then ", in both directions" else ""}"
  let counters ← IO.mkRef (0, 0)
  let gen ← IO.mkRef (← SplitMix.newIO)
  let artifactPrefix := (strFlag? argv "-artifact_prefix=").getD ""
  hybridConfigImpl (runOneRecorded counters (T RecordGen) gen artifactPrefix)
    cfg.firstMax.toUInt64 cfg.minWindow.toUInt64 cfg.level cfg.confidence budget.toUInt64
    cfg.adaptive cfg.switchBack
  go (T FuzzGen) argv grow counters

/-- The coverage-guided backend, for `Basalt.PBT.dispatch`. `--grow` is Basalt's own
(`fuzz-run/README.md`); the rest of `argv` goes to libFuzzer, and a saved artifact — which *is* a
`FuzzGen` input buffer — can be replayed. -/
@[basalt_backend]
def fuzzBackend : Backend where
  name := "fuzz"
  campaign T argv :=
    let (flags, rest) := splitFlags argv
    if !flags.bad.isEmpty then
      usageError s!"malformed: {flags.bad.toList}; --warmup=N and --warmup-stall=K take a number \
        of tests, --level=φ and --confidence=c a decimal"
    else match flags.hybrid with
    | some cfg => goHybrid T cfg flags.grow rest
    | none => go (T FuzzGen) rest flags.grow
  replay? := some (fun T path => replay (T FuzzGen) path)

/-- Random `IO` choices, run and coverage-counted by libFuzzer (`goRandom`): the baseline that
`fuzz`'s coverage is compared against. -/
@[basalt_backend]
def ioUnderFuzzBackend : Backend where
  name := "io-libfuzzer"
  campaign T argv := let (_, rest) := splitFlags argv; goRandom (T IO) rest
  replay? := none

end Basalt.Fuzz
