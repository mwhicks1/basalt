/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Basalt.Fuzz.Basic
import Basalt.Fuzz.Choice
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
opaque goImpl (run : ByteArray → IO UInt8) (argv : Array String) (grow : Bool) (modes : UInt32) :
    IO Unit

/-- Called at the conclusion of a run to report to the C code the deficit in the buffer,
i.e., the difference N - S between requested bytes N and available bytes S, the run's fill seed
(`FuzzResult.seed`), which `--grow` needs to materialize a random fill, and how many bytes it read,
which `--truncate` cuts the next mutation's input to. -/
@[extern "basalt_fuzz_note_deficit"]
opaque noteDeficitImpl (deficit : UInt32) (seed : UInt64) (cursor : UInt64) : BaseIO Unit

/-- Hand the C bridge a recorded run's draws (`FuzzState.trace`) and how many bytes it read. -/
@[extern "basalt_fuzz_note_trace"]
opaque noteTraceImpl (cursor : UInt64) (trace : @& Array UInt64) : BaseIO Unit

/-- The `FuzzGen` variations Phase 0 of `DESIGN-choice-sequences.md` measures, each off by default:
`randomFill` reads a seeded random byte past the end instead of `0`; `probe` records every draw and
has the bridge keep the traces of runs that reached new coverage, discarding them (the cost probe);
`mutations` logs, per mutated input, why it repeats its parent (`BASALT_M` lines); `truncate` cuts
an input to the bytes its run read before mutating it, as Zest's `gc()` does; `plant` records every
fuzz-mode run's draws so the mutator can plant a harvested literal or a comparison operand into one
(`native.c`, "`--plant`"); `nudge` records them so it can move one by a small delta. -/
structure Diag where
  randomFill : Bool := false
  probe : Bool := false
  mutations : Bool := false
  truncate : Bool := false
  plant : Bool := false
  nudge : Bool := false

/-- The decoding `runOne` uses under `d`. -/
def Diag.config (d : Diag) : FuzzConfig :=
  { randomFill := d.randomFill, record := d.probe || d.mutations || d.plant || d.nudge }

/-- The bridge's mode bits: 1 random fill, 2 probe, 4 mutation log, 16 truncate, 32 plant, 64 nudge. -/
def Diag.modes (d : Diag) : UInt32 :=
  (if d.randomFill then 1 else 0) + (if d.probe then 2 else 0) + (if d.mutations then 4 else 0) +
  (if d.truncate then 16 else 0) + (if d.plant then 32 else 0) + (if d.nudge then 64 else 0)

/-- Run the property on one input, reporting the byte codes the C bridge expects: `0` = pass,
`1` = failed (the bridge then aborts, so the report must already be flushed), `2` = discard.

`counters` tallies executions and discards so a failing campaign can report the same run line the
other backends do — libFuzzer's own `#N` markers count only corpus-worthy inputs, which is not the
number of tests run. -/
def runOneIO (counters : IO.Ref (Nat × Nat)) (T : PropM FuzzGen Unit) (cfg : FuzzConfig)
    (bytes : ByteArray) : IO UInt8 := do
  let r := runOne T bytes cfg -- run the property test
  noteDeficitImpl (UInt32.ofNatClamp r.deficit) r.seed r.cursor.toUInt64 -- note any bytes deficit
  if cfg.record then noteTraceImpl r.cursor.toUInt64 r.trace
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
    (counters? : Option (IO.Ref (Nat × Nat)) := none) (diag : Diag := {}) : IO Unit := do
  IO.println s!"[basalt] starting libFuzzer campaign (grow={grow}, randomFill={diag.randomFill}, \
    probe={diag.probe}, diag={diag.mutations}, plant={diag.plant}, nudge={diag.nudge}, {argv.toList})"
  -- libFuzzer announces that the linked custom mutator disables `-len_control` on every campaign,
  -- `--grow` or not; an explicit flag wins over that default (`splitFlags`), so say so.
  if let some lc := argv.find? (·.startsWith "-len_control=") then
    IO.println s!"[basalt] {lc} is explicit and overrides libFuzzer's \
      \"Disabling -len_control by default\""
  let counters ← match counters? with | some c => pure c | none => IO.mkRef (0, 0)
  -- Report nothing after `goImpl`: libFuzzer `exit()`s when `-runs` is exhausted, so a line placed
  -- there silently never appears (the tally lives in `runOneIO`, the statistics in an `atexit`).
  goImpl (fun bytes => runOneIO counters T diag.config bytes) argv grow diag.modes

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
  goImpl (runOneRandom counters T) argv false 0

/-- Replay one saved input file against a property (no fuzzer): reproduces the outcome
deterministically and prints it. This is how a saved artifact (`crash-…`) is consumed.

The bytes plus the fill are the whole reproduction: an artifact means the same thing however it was
produced — including one grown by `--grow`, which is already whatever length the failing run read.
The fill is a campaign setting, and `replay` takes no flags, so a campaign run with `--fill=random`
replays under `BASALT_FILL=random`. -/
def replay (T : PropM FuzzGen Unit) (path : String) : IO Unit := do
  let bytes ← IO.FS.readBinFile path
  let randomFill := (← IO.getEnv "BASALT_FILL") == some "random"
  IO.println s!"[basalt] replaying {path} ({bytes.size} bytes, {if randomFill then "random" else "zero"} fill)"
  let r := runOne T bytes { randomFill }
  match r.outcome with
  | Except.ok () => IO.println s!"outcome: pass ({r.deficit} bytes short)"
  | Except.error .discard => IO.println s!"outcome: discard ({r.deficit} bytes short)"
  | Except.error (.fail msg) => reportFailure msg

/-- Basalt's own fuzz flags, split out of `argv`: libFuzzer rejects a flag it does not recognize, so
what we consume must not be forwarded. `bad` collects the ones given malformed. -/
structure FuzzFlags where
  grow : Bool := false
  policy : FillPolicy := .fresh
  diag : Diag := {}
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
  ["--grow", "--fill", "--fill-policy", "--trace-probe", "--diag-mutations", "--truncate", "--plant", "--nudge", "--warmup", "--warmup-stall", "--switch-back", "--level", "--confidence"]

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
  let fill := valueOf? argv "--fill"
  let diag : Diag := { randomFill := fill == some "random", probe := argv.contains "--trace-probe",
                       mutations := argv.contains "--diag-mutations",
                       truncate := argv.contains "--truncate", plant := argv.contains "--plant",
                       nudge := argv.contains "--nudge" }
  let bad := argv.filter (fun a => a.startsWith "--grow=" || a.startsWith "--switch-back=" ||
      a.startsWith "--trace-probe=" || a.startsWith "--diag-mutations=" || a.startsWith "--plant=" || a.startsWith "--nudge=" ||
      a == "--fill") ++
    (if fill.any (fun f => f != "random" && f != "zero") then #["--fill"] else #[]) ++
    (if (valueOf? argv "--fill-policy").any (fun f => f != "fresh" && f != "simplest")
     then #["--fill-policy"] else #[]) ++
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
  let policy := if valueOf? argv "--fill-policy" == some "simplest" then .simplest else .fresh
  ({ grow, policy, diag, hybrid, bad }, rest)

/-- The value of libFuzzer's `-flag=V`, if given. -/
private def strFlag? (argv : Array String) (flag : String) : Option String :=
  argv.findSome? fun a => if a.startsWith flag then some (a.drop flag.length).toString else none

/-- A hybrid campaign: random and coverage-guided phases in one libFuzzer loop, switching as `cfg`
says. Every phase's tests count against the one `-runs` budget. -/
def goHybrid (T : Property) (cfg : HybridConfig) (grow : Bool) (argv : Array String)
    (diag : Diag := {}) : IO Unit := do
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
  go (T FuzzGen) argv grow counters diag

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
        of tests, --level=φ and --confidence=c a decimal, --fill is random or zero"
    else match flags.hybrid with
    | some cfg => goHybrid T cfg flags.grow rest flags.diag
    | none => go (T FuzzGen) rest flags.grow none flags.diag
  replay? := some (fun T path => replay (T FuzzGen) path)

/-! ## The choice-sequence backend -/

/-- Hand the C bridge what a `ChoiceFuzz` run did: its realized records and its draws' bounds
(`ChoiceState`), for the mutator to edit. -/
@[extern "basalt_choice_note"]
opaque noteChoiceImpl (realized : @& ByteArray) (bounds : @& ByteArray) : BaseIO Unit

/-- Offer the choice mutator a constant to plant in a draw whose range admits it
(`harvested_literals%`). -/
@[extern "basalt_choice_literal"]
opaque choiceLiteralImpl (n : UInt64) : BaseIO Unit

/-- `runOneIO` for a choice-sequence input. -/
def runOneChoiceIO (counters : IO.Ref (Nat × Nat)) (T : PropM ChoiceFuzz Unit) (policy : FillPolicy)
    (bytes : ByteArray) : IO UInt8 := do
  let r := runChoiceOn T bytes policy
  noteChoiceImpl r.realized r.bounds
  match r.outcome with
  | Except.ok () => counters.modify (fun (runs, discards) => (runs + 1, discards)); pure 0
  | Except.error .discard => counters.modify (fun (r, d) => (r, d + 1)); pure 2
  | Except.error (.fail msg) =>
    counters.modify (fun (runs, discards) => (runs + 1, discards))
    let (runs, discards) ← counters.get
    reportFailure msg
      #[("input bytes", s!"{bytes.toList.map (fun b => b.toNat)}"),
        ("runs", s!"{runs} ({discards} discarded)"),
        ("records", s!"{bytes.size} bytes in, {r.realized.size} realized")]
    pure 1

/-- `runOneRecorded` for the choice backend: a random test is a `ChoiceFuzz` run of no records,
filled from the campaign's PRNG, and its realized records are the seed, which replays exactly. -/
def runOneChoiceRandom (counters : IO.Ref (Nat × Nat)) (T : PropM ChoiceFuzz Unit)
    (gen : IO.Ref SplitMix) (artifactPrefix : String) (_ : ByteArray) : IO UInt8 := do
  let r := runChoice T ByteArray.empty (← gen.get)
  gen.set r.fill
  hybridOfferImpl r.realized
  match r.outcome with
  | Except.ok () => counters.modify (fun (runs, discards) => (runs + 1, discards)); pure 0
  | Except.error .discard => counters.modify (fun (r, d) => (r, d + 1)); pure 2
  | Except.error (.fail msg) =>
    counters.modify (fun (runs, discards) => (runs + 1, discards))
    let (runs, discards) ← counters.get
    let path := s!"{artifactPrefix}crash-random-{runs + discards}"
    IO.FS.writeBinFile path r.realized
    reportFailure msg
      #[("runs", s!"{runs} ({discards} discarded), failing in a random phase"),
        ("artifact", path)]
    pure 1

/-- The bridge's mode bit for a choice-sequence campaign (`Diag.modes` holds the others). -/
def choiceMode : UInt32 := 8

/-- A choice-sequence campaign: libFuzzer's buffer is a record sequence, and the bridge's mutator
edits the realized records of the input it mutates. -/
def goChoice (T : PropM ChoiceFuzz Unit) (argv : Array String) (policy : FillPolicy)
    (counters? : Option (IO.Ref (Nat × Nat)) := none) : IO Unit := do
  IO.println s!"[basalt] starting choice-sequence campaign ({argv.toList})"
  let counters ← match counters? with | some c => pure c | none => IO.mkRef (0, 0)
  goImpl (runOneChoiceIO counters T policy) argv false choiceMode

/-- `goHybrid` for the choice backend. -/
def goHybridChoice (T : Property) (cfg : HybridConfig) (argv : Array String) (policy : FillPolicy) :
    IO Unit := do
  let budget := (strFlag? argv "-runs=" |>.bind String.toNat?).getD 0
  IO.println s!"[basalt] hybrid choice-sequence campaign: random first\
    {if cfg.adaptive then s!", switching when coverage levels off (level={cfg.level})" else ""}"
  let counters ← IO.mkRef (0, 0)
  let gen ← IO.mkRef (← SplitMix.newIO)
  let artifactPrefix := (strFlag? argv "-artifact_prefix=").getD ""
  hybridConfigImpl (runOneChoiceRandom counters (T ChoiceFuzz) gen artifactPrefix)
    cfg.firstMax.toUInt64 cfg.minWindow.toUInt64 cfg.level cfg.confidence budget.toUInt64
    cfg.adaptive cfg.switchBack
  goChoice (T ChoiceFuzz) argv policy counters

/-- Replay a choice-sequence input. The fill is seeded by the buffer, so it needs no flag; the fill
policy does (`BASALT_FILL_POLICY=simplest`). -/
def replayChoice (T : PropM ChoiceFuzz Unit) (path : String) : IO Unit := do
  let bytes ← IO.FS.readBinFile path
  let policy := if (← IO.getEnv "BASALT_FILL_POLICY") == some "simplest" then .simplest else .fresh
  IO.println s!"[basalt] replaying {path} ({bytes.size} bytes) as a choice sequence"
  let r := runChoiceOn T bytes policy
  match r.outcome with
  | Except.ok () => IO.println s!"outcome: pass"
  | Except.error .discard => IO.println s!"outcome: discard"
  | Except.error (.fail msg) => reportFailure msg

/-- The choice-sequence backend (`DESIGN-choice-sequences.md`): `fuzz`'s flags, except that
`--grow` and `--fill` have no meaning here, plus `--fill-policy=fresh|simplest`. -/
@[basalt_backend]
def choiceBackend : Backend where
  name := "choice"
  campaign T argv :=
    -- The mutator, not libFuzzer's length ramp, decides how long an input is (`splitFlags`).
    let argv := if argv.any (·.startsWith "-len_control=") then argv else argv.push "-len_control=0"
    let argv := if argv.any (·.startsWith "-max_len=") then argv else argv.push "-max_len=65536"
    let (flags, rest) := splitFlags argv
    if !flags.bad.isEmpty then usageError s!"malformed: {flags.bad.toList}"
    else match flags.hybrid with
    | some cfg => goHybridChoice T cfg rest flags.policy
    | none => goChoice (T ChoiceFuzz) rest flags.policy
  replay? := some (fun T path => replayChoice (T ChoiceFuzz) path)

/-- Random `IO` choices, run and coverage-counted by libFuzzer (`goRandom`): the baseline that
`fuzz`'s coverage is compared against. -/
@[basalt_backend]
def ioUnderFuzzBackend : Backend where
  name := "io-libfuzzer"
  campaign T argv := let (_, rest) := splitFlags argv; goRandom (T IO) rest
  replay? := none

end Basalt.Fuzz
