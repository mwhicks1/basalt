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

/-- Zero the coverage counters before the first warm-up run. -/
@[extern "basalt_warmup_begin"]
opaque warmupBeginImpl : BaseIO Unit

/-- Judge one warm-up run by the coverage it left in the counters, as libFuzzer would, and keep its
recorded `bytes` as a candidate seed if it reached something no earlier run did. -/
@[extern "basalt_warmup_observe"]
opaque warmupObserveImpl (bytes : @& ByteArray) : BaseIO Bool

/-- Write a set cover of the kept runs into `dir` as libFuzzer seeds; returns how many. -/
@[extern "basalt_warmup_write_seeds"]
opaque warmupWriteSeedsImpl (dir : @& String) : BaseIO UInt32

/-- How a random warm-up ends: after `runs` tests, or sooner once `stall` tests in a row (if
nonzero) have found nothing new. -/
structure WarmupConfig where
  runs : Nat
  stall : Nat := 0

/-- Run `T` at `RecordGen` under `cfg`, keeping each run that reached new coverage; returns how many
tests ran. A failure is reported like any other, its recorded bytes are saved under
`artifactPrefix` — a `FuzzGen` input, so `replay` reproduces it — and the process exits. -/
def warmup (T : PropM RecordGen Unit) (cfg : WarmupConfig) (artifactPrefix : String) : IO Nat := do
  warmupBeginImpl
  let mut g ← SplitMix.newIO
  let mut ran := 0
  let mut discards := 0
  let mut sinceNew := 0
  while ran < cfg.runs && (cfg.stall == 0 || sinceNew < cfg.stall) do
    let (outcome, bytes, g') := runRecord T g
    g := g'
    ran := ran + 1
    sinceNew := if (← warmupObserveImpl bytes) then 0 else sinceNew + 1
    match outcome with
    | Except.ok () => pure ()
    | Except.error .discard => discards := discards + 1
    | Except.error (.fail msg) =>
      let path := s!"{artifactPrefix}crash-warmup-{ran}"
      IO.FS.writeBinFile path bytes
      reportFailure msg
        #[("input bytes", s!"{bytes.toList.map (fun b => b.toNat)}"),
          ("runs", s!"{ran - discards} ({discards} discarded), in the random warm-up"),
          ("artifact", path)]
      IO.Process.exit failureExitCode
  return ran

/-- Start a fuzzing campaign for property `T`. `argv` is forwarded to libFuzzer (corpus dirs,
`-runs`, `-max_len`, `-artifact_prefix`, …). A failure aborts the process, with the artifact saved and
the exit code set by libFuzzer. -/
def go (T : PropM FuzzGen Unit) (argv : Array String := #[]) (grow : Bool := false) : IO Unit := do
  IO.println s!"[basalt] starting libFuzzer campaign (grow={grow}, {argv.toList})"
  -- libFuzzer announces that the linked custom mutator disables `-len_control` on every campaign,
  -- `--grow` or not; an explicit flag wins over that default (`splitFlags`), so say so.
  if let some lc := argv.find? (·.startsWith "-len_control=") then
    IO.println s!"[basalt] {lc} is explicit and overrides libFuzzer's \
      \"Disabling -len_control by default\""
  let counters ← IO.mkRef (0, 0)
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
what we consume must not be forwarded. -/
structure FuzzFlags where
  grow : Bool := false
  warmup : Option WarmupConfig := none

private def natArg? (a pre : String) : Option Nat :=
  if a.startsWith pre then (a.drop pre.length).toString.toNat? else none

def splitFlags (argv : Array String) : FuzzFlags × Array String :=
  let grow := argv.contains "--grow"
  let warmRuns := argv.findSome? (natArg? · "--warmup=")
  let stall := (argv.findSome? (natArg? · "--warmup-stall=")).getD 0
  let rest := argv.filter (fun a => a != "--grow" && !a.startsWith "--warmup")
  -- `-max_len` bounds the buffer and so bounds the structure growth can build; libFuzzer's own
  -- default derives it from the seed corpus, which is 4096 at a cold start. Left there it, and not
  -- the property, decides how far growth gets. A warm-up's seeds are as long as their runs read, so
  -- the same holds for the inputs mutated from them.
  let long := grow || warmRuns.isSome
  let rest := if long && !rest.any (·.startsWith "-max_len=") then rest.push "-max_len=65536"
              else rest
  -- Linking a custom mutator makes libFuzzer disable its `-len_control` length ramp, which is what
  -- growth wants: the mutator, not the ramp, decides how long an input needs to be. A warm-up wants
  -- it off too: the ramp would hold each seed's mutations to the seed's own length for most of the
  -- campaign. Otherwise there is no mutator decision to make, so restore libFuzzer's own default
  -- and leave the campaign as it was. Only an *absent* flag is defaulted — passing
  -- `-len_control=N` explicitly (including `0`) wins, which is how the modes are compared under
  -- one length regime.
  let rest := if !long && !rest.any (·.startsWith "-len_control=") then
                rest.push "-len_control=100"
              else rest
  ({ grow, warmup := warmRuns.map ({ runs := ·, stall }) }, rest)

/-- The value of libFuzzer's `-flag=V`, if given. -/
private def strFlag? (argv : Array String) (flag : String) : Option String :=
  argv.findSome? fun a => if a.startsWith flag then some (a.drop flag.length).toString else none

/-- A random warm-up, then libFuzzer seeded with what it found. The seeds go into the first corpus
directory on the command line — libFuzzer's output corpus — or a fresh one appended to it, and
the warm-up's tests come out of the `-runs` budget. -/
def goWarm (T : Property) (cfg : WarmupConfig) (grow : Bool) (argv : Array String) : IO Unit := do
  let budget := strFlag? argv "-runs=" |>.bind String.toNat?
  let cfg := match budget with | some r => { cfg with runs := min cfg.runs r } | none => cfg
  IO.println s!"[basalt] random warm-up of at most {cfg.runs} tests\
    {if cfg.stall == 0 then "" else s!", or until {cfg.stall} in a row find nothing new"}"
  let ran ← warmup (T RecordGen) cfg ((strFlag? argv "-artifact_prefix=").getD "")
  let (dir, argv) ← match argv.find? (fun a => !a.startsWith "-") with
    | some d => pure (d, argv)
    | none => do let d ← IO.FS.createTempDir; pure (d.toString, argv.push d.toString)
  let _ ← warmupWriteSeedsImpl dir
  let argv := match budget with
    | some r => argv.map fun a => if a.startsWith "-runs=" then s!"-runs={r - ran}" else a
    | none => argv
  go (T FuzzGen) argv grow

/-- The coverage-guided backend, for `Basalt.PBT.dispatch`. `--grow` is Basalt's own
(`fuzz-run/README.md`); the rest of `argv` goes to libFuzzer, and a saved artifact — which *is* a
`FuzzGen` input buffer — can be replayed. -/
@[basalt_backend]
def fuzzBackend : Backend where
  name := "fuzz"
  campaign T argv :=
    let (flags, rest) := splitFlags argv
    match flags.warmup with
    | some cfg => goWarm T cfg flags.grow rest
    | none =>
      if argv.any (·.startsWith "--warmup") then
        usageError "--warmup=N needs a number of tests; --warmup-stall=K needs --warmup=N"
      else go (T FuzzGen) rest flags.grow
  replay? := some (fun T path => replay (T FuzzGen) path)

/-- Random `IO` choices, run and coverage-counted by libFuzzer (`goRandom`): the baseline that
`fuzz`'s coverage is compared against. -/
@[basalt_backend]
def ioUnderFuzzBackend : Backend where
  name := "io-libfuzzer"
  campaign T argv := let (_, rest) := splitFlags argv; goRandom (T IO) rest
  replay? := none

end Basalt.Fuzz
