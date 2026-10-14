# Choice-sequence fuzzing for Basalt: design and plan

**Status.** Design settled enough to start; plan in §5. Written against `origin/hybrid-fuzz` @
`d7dec29`, and every code reference below is to that branch.

**How to use this file.** §1–§4 are the current design, with every correction from review folded
in. §5 is the work plan: a tree of steps whose branches depend on measured outcomes, so work can
continue without a check-in at every step. §6 records the decisions and §7 the references. Appendices A–C are
the review rounds (questions and answers), kept as the evidence trail. Section numbers inside A and
B refer to an earlier draft. Where an appendix and the body disagree, the body wins.

**Where the existing pieces are** (on `hybrid-fuzz`):
- `Basalt/Fuzz/Basic.lean` (`FuzzGen`, `readByte`, `runOne`);
- `Basalt/Fuzz/Record.lean` (`RecordGen`);
- `Basalt/Fuzz/Runner.lean` (`go`, `goHybrid`, `splitFlags`, backends);
- `Basalt/Fuzz/native.c` (custom mutator, `--grow`, hybrid phase machinery, coverage dump);
- `BasaltFuzzMain.lean` (property registry), `BasaltFuzz/` (targets, Cedar generators);
- `fuzz-run/` (`build.sh`, `hybrid-experiment.sh`, `cedar-experiment.sh`, `compare-grow.sh`,
  `budget-table.py`, `coverage-curves.py`, `edge-sets.py`);
- the measurement write-ups `fuzz-run/README.md`, `CEDAR.md`, `reports/2026-10-hybrid-fuzzing/`.

## 1. Starting point

- **The only primitive** is `RandomChoice.choose : (lo hi : Nat) → lo ≤ hi → m {x // lo ≤ x ≤ hi}`
  (`Basalt/RandomChoice.lean:12`). `chooseInt`, `elements`, `oneOf`, `frequency`, `listOf`,
  `listOfMaxLength` and `suchThat` all reduce to it, and so do the compiled `oneOf!`/`frequency!`,
  whose `impl` is one `choose` plus an `if` chain (`Combinators.lean:266-306`). A 2-way `oneOf`, a
  `coin`, `chooseNat 0 1` and a boolean are indistinguishable at the instance.
- **How `FuzzGen` decodes.** Each `choose` reads `⌈log₂(range)/8⌉` big-endian bytes and returns
  `lo + raw % range`. A unit range reads nothing, and reads past the end return 0.
  `LLVMFuzzerCustomMutator` is exported and delegates to `LLVMFuzzerMutate` (plus `--grow`, plus
  hybrid seed injection); there is no `CustomCrossOver`. `RecordGen` turns random draws into bytes
  `FuzzGen` decodes identically, which is how the hybrid's random phase seeds the corpus.
- **What the measurements already show:**
  - The hybrid works on Cedar `gen-traced`: random's fast start, then fuzzing's higher plateau,
    about +100 edges (~1.4%) at 5M tests, reached sooner and with less variance.
  - Fuzzing is **inefficient**: only ¼–½ of fuzz tests yield a new expression, and random makes
    3.5M distinct expressions in 55 minutes against about 2.0M for every fuzz arm.
  - **Magic values are unreachable.** A 32-bit needle is not found in 5M runs, and `-trace-cmp` is
    useless because Lean scalars are tagged (`2n+1`).
  - **Draw order matters.** An expression drawn after the request and entities read zeros, i.e.
    first branches, and yielded 1 distinct expression in about 10k tests.
  - **`--grow` does not help** (Appendix B, Q1.1). A materialized zero is a stop sign at the
    frontier. Without `--grow`, appends land *on* the frontier; with it, they land behind the stop
    sign and do nothing. Filling the extension with random bytes ties the baseline.
- **Machinery to reuse** (Appendix A Q1.3, Appendix B Q1.3):
  - the `@[mix_shape]` taxonomy (`Basalt/Obs/Spec.lean:54-81`), which gives the list of choice
    kinds;
  - `Tuning.Site` names (`decl.site<i>`), which can serve as span labels;
  - `@[tunable]`'s body rewrite (`Basalt/Tuning/Attr.lean`), which places recursion spans and is
    the engine for design C.

## 2. What the evidence supports

Details and citations are in the appendices. In short:

- **Coverage guidance over well-formed generators gives small gains.**
  - TOSEM Havoc Paradox: on Gson/Jackson (always-valid generators) every technique ties random.
  - Gentoo: guidance helps naive human generators by +40% on average, and agent generators by
    −0.1% to +2%, not significantly.
  - Etna: Crowbar over bespoke generators adds overhead for minimal gain.
  - Cedar: about +1.4%.

  **Goal.** These gains are small, but we assume they are worth having. The aim is for the
  fuzzing side to reach a **higher ceiling**: more edges at large budgets, with the hybrid keeping
  random's fast start. Efficiency (fewer repeated inputs, more productive mutations) is the main
  *lever*, and it should raise the ceiling, because more mutations reach new code. Success is
  therefore judged on coverage at the largest budgets (§4). The new-expression rate is a
  diagnostic, not the criterion.
- **The waste is confirmed on Cedar independently.** Vikram's thesis §5.5 (§7) runs libFuzzer via
  bolero over Cedar's Rust generators. About 80% of sampled mutations "traverse the same generator
  path" and yield equivalent inputs, pure random generation is markedly more diverse, and coverage
  guidance skews input size upward. That study did not measure coverage; ours shows fuzzing's
  ceiling is higher anyway (§1).
- **Locality (EI) does not fix inefficiency.**
  - Context-aware techniques have Zest's zero-mutation rate (TOSEM Finding #2).
  - They gain +1–3% on 2 of 7 targets.
  - They cost 0.43–1.01× in throughput.
- **Destructive mutations are productive** (TOSEM Finding #5), and BeDivFuzz, which filters them
  out, loses. Keep them, and add fine-grained operators alongside.
- **Typed choices with a "permitted?" check** are what Hypothesis and Hegel converged on. Their
  replay is **positional**: on a misfit they substitute the simplest value (Hypothesis) or
  simplest-or-unit (Hegel). HypoFuzz, the only coverage-guided user of choices, fills misfits with
  fresh random values. Hegel's structural addresses are used only for nondeterministic tests.
- **Collections as "another element?" coins inside per-element spans** (Hypothesis `many`, Hegel
  `hegel_collection_more`) make element deletion one contiguous edit (MacIver & Donaldson,
  ECOOP'20). That evidence is from reduction; for mutation it is a structural argument.
- **Strings are one primitive choice** in both engines. That enables character edits, substring
  splices and whole-literal injection (Hypothesis harvests literals from user code and uses one on
  ~5% of draws).
- **Zest's past-the-end behaviour is the model for the fill:** a fresh random byte, appended to
  the input; unread values are trimmed, so a saved input is exactly its realized choices.
- **Same-site crossover (Zeugma)** gives large inheritance gains (0.7–0.9 vs ~0.1). Its coverage
  gains are partly its framework's speed.

## 3. The design

### 3.1 Records, kinds, alignment

- **Buffer contents.** The libFuzzer buffer is a sequence of records `(kind tag, absolute value)`,
  one per non-unit draw, with a self-delimiting encoding (tag byte plus LEB128; strings are
  length-prefixed).
  - The kind tag *is* metadata. That is safe because libFuzzer never edits the buffer itself:
    defining `LLVMFuzzerCustomMutator` replaces its whole default suite, and crossover goes only
    through our `LLVMFuzzerCustomCrossOver` (§3.4). Only our code writes tags.
  - Bounds, weights and spans are **not stored by default**. Every run recomputes them into the
    *trace* (below), which is where the mutator gets them.
  - Storing them too is a variant worth keeping open; see "self-describing records" below.
- **Replay is positional.** A stored record is used iff its kind matches the request and its
  value is *permitted* by the new constraints (the table below). Otherwise the value comes from
  the fill, and the fill policy is a knob: fresh (the default), simplest, rescale, or pun.
- **The fill is seeded random** past the end and on a misfit: `SplitMix(hash(buffer), position)`.
  Replay of any saved buffer is therefore deterministic and needs no flag, and an empty buffer is
  random generation.
- **The trace.** Each run produces `(kind, value, lo, hi, fromFill)` per draw, plus span
  open/close events. It is kept in Lean state and handed to C once per run as a `ByteArray`.
- **Repair after misalignment ("materialization").** A run of a mutated buffer can misalign: some
  stored records misfit and are replaced by fill, and the run may draw past the end. That is only
  known *after* the run. The run's trace then records what every draw actually received.
  - **When the mutator next touches that input**, it first re-encodes the buffer from the trace,
    so the buffer matches what the run did, and only then applies the new mutation. That happens
    at the next iteration of the same round, or later when the input comes back from the corpus.
  - **Cost:** O(draws) to re-encode, and **no extra execution** (§3.4).
  - **Nothing is copied back** into libFuzzer's saved copy, which is impossible:
    `LLVMFuzzerTestOneInput` gets a `const` buffer, and the corpus admission rule rejects an
    equivalent longer input. The saved buffer still reproduces the run exactly, because the fill
    is a function of the buffer.
  - **Why it is worth doing.** The fill is seeded by the buffer's hash, and every edit changes the
    hash. Without repair, each later mutation also re-randomizes every position that had come from
    the fill. Fill values could then never be refined, and every edit would carry hidden
    destruction. With repair, an edit changes what the operator changed, plus whatever *this* edit
    misaligns.
  - **Precedents and test.** Zest (appending realized bytes) and Hypothesis, HypoFuzz and Hegel
    (mutating realized choices) all do this. Phase 0.2's random-fill × `--grow` arm tests the same
    question at the byte level.
- **Variant: self-describing records.** Store `(kind, value, lo, hi)`, plus span open/close
  markers with label ids, and optionally weights, in the buffer itself.
  - **Gains:** the mutator needs no trace for any input. There is no cache, no re-run on a miss,
    and crossover partners and inputs from other processes (`-jobs`/`-fork`, a shared corpus
    directory) carry their own metadata.
  - **Costs:**
    - buffers 2–4× larger;
    - metadata in a *saved* buffer describes the parent plus the edit, not what the child's run
      did after a misalignment. That is stale but safe: replay still checks each record against
      the actual request.
  - **Decision rule:** Gate 1 (§5) adopts this variant if cache misses or cache cost show up in
    the throughput, or if we move to multi-process campaigns.

**Kinds** (the first slice uses only `.nat`; the rest arrive with the hooks of §3.3):

| Combinator | Record | Span | Permitted iff |
|---|---|---|---|
| `frequency!` / `frequency` | `.branch i` | `(site, i)` around branch `i` | `i < N ∧ weight i > 0` |
| `oneOf!` / `oneOf` | `.branch i` | `(site, i)` | `i < N` |
| `coin r` | `.bool b` | — | always |
| `elements xs` | `.index i` | — | `i < N` |
| `chooseInt lo hi` | `.int v` | — | `lo ≤ v ≤ hi` |
| `chooseNat` / bare `choose` | `.nat v` | — | `lo ≤ v ≤ hi` |
| `listOf g` | `.more b` per element | element span | always |
| `listOfMaxLength n g` | `.length k` | element spans | `k ≤ n` |
| `vectorOf n g` | — | element spans | — |
| `stringOf alphabet lo hi` (new combinator) | `.string s` | — | chars ∈ alphabet, `lo ≤ len ≤ hi` |
| recursive call of `f` | — | `(f, ordinal)` | — |

**Support rule.** Every value `ChoiceFuzz` returns must be in the model's support (pinned by a
test). Otherwise the property could see inputs the generator can never produce.

### 3.2 The interpretation and the C side

```lean
structure ChoiceState where
  records : Array Record     -- decoded once from the buffer
  pos     : Nat
  fill    : SplitMix         -- seeded from hash(buffer)
  trace   : Array Draw       -- returned to C once per run
abbrev ChoiceFuzz := StateT ChoiceState Option   -- Gen via the blanket instance, like FuzzGen
```

**`ChoiceFuzz` is a parallel interpretation, not a layer on `FuzzGen`.** Its decoding (records)
and `FuzzGen`'s (byte widths plus `% range`) share nothing worth factoring. What they share is the
plumbing:
- the `@[basalt_backend]` registration and `runOneIO`-style result codes;
- `native.c`'s driver entry, coverage dump, hybrid phase machinery, and artifact and replay
  handling.

`ChoiceFuzz` becomes a second mode in those. **`FuzzGen` is kept** as the baseline arm and as
Phase 0's testbed; Phase 0 changes it only behind flags. In choice mode the hybrid's random phase
runs `ChoiceFuzz` with its fill seeded from the global PRNG instead of the buffer, and offers the
realized trace as the seed. That replaces `RecordGen`'s role.

**Mutation operators.** Five families, chosen by a bandit rewarded by new features:

| Family | Operators | Needs |
|---|---|---|
| local value | random-in-range; ±δ (geometric); boundaries (`lo`, `hi`, `lo±1`, 0); sign/bit flips for wide ints | bounds (from the trace) |
| constants | a permitted pool constant: untagged cmp operands from our own `__sanitizer_cov_trace_cmp*` hook; literals harvested from target/property | bounds |
| destructive | truncate at *k* (the rest is fill, i.e. regenerated); randomize *m* consecutive values; regenerate a span | — / spans |
| recombination | splice a run whose kind sequence matches the donor's; same-label span splice (Zeugma); nested self-embedding | kinds / spans |
| structural, local | branch flip, keeping the suffix positional or regenerating the branch's span; delete or duplicate an element span; joint `.length` + element edit; string edits and literal injection | kinds, spans |

**Hybrid.** The switching rule is unchanged. The random phase's seeds become `ChoiceFuzz`
realized traces, playing the role `RecordGen` plays for bytes.

### 3.3 How kinds and spans reach `choose`: design B or C

The instance sees only `(lo, hi)`, so kinds and spans need hooks. With no hooks (design A), every
draw is `.nat`. A is the substrate of §5's Phase 1, not a candidate to evaluate on its own.

**B — hooks inside the `Gen` dictionary.** Add defaulted methods to `RandomChoice`:

```lean
chooseAs : ChoiceKind → (lo hi : Nat) → lo ≤ hi → m (ULift {x // lo ≤ x ∧ x ≤ hi}) := fun _ => choose
span     : Name → m α → m α := fun _ g => g
-- plus a string hook defaulting to stringOf's model
```

- **How it reaches generators.** Combinators and the compiled `impl` call the hooks, so every
  existing generator gets kinds and combinator spans with no source change, including CedarGen's
  dynamic `pick` lists. Existing instances inherit the defaults, and IO specializes them away.
- **Costs.**
  - It touches the `Gen` bundle. That is backward-compatible but contrary to the original
    constraint.
  - `Obs`/`GenRel` gain fields discharged by `rfl` at existing observations.
  - `span` inside fixpoints needs a monotonicity law plus a `@[partial_fixpoint_monotone]` lemma.

**C — a separate `ChoiceHints` class and a `@[traced]` rewrite.**
- **How it reaches generators.** The rewrite, modelled on `@[tunable]`, emits `foo.traced` with an
  explicit hints binder and an `rfl` equation back to `foo`.
- **Costs.**
  - No change to `Gen` or any proof.
  - Opt-in per generator, with transitive callees to rewrite.
  - Library combinators need traced twins.
  - CedarGen's dynamic lists and its `Fam`-field recursion need rewrite extensions.

**Recursion spans** (`(f, ordinal)` around recursive calls) need a body rewrite under *either*
design, built from `@[tunable]`'s site and recursive-occurrence detection.

### 3.4 How it runs inside libFuzzer, and what it costs

**libFuzzer's loop**, checked against `compiler-rt/lib/fuzzer` at llvmorg-22.1.8, the version the
README verified. Each round of `Fuzzer::MutateAndTestOne` (`FuzzerLoop.cpp:723-778`) does this:

1. Pick a corpus unit *P* and, separately, a crossover partner *Q* (`ChooseUnitToCrossOverWith`).
   Copy *P*'s bytes into a working buffer *W*.
2. Repeat up to `-mutate_depth` (5) times:
   - **mutate *W* in place.** With our hooks defined, `MutationDispatcher` holds exactly two
     mutators, `Custom` and `CustomCrossOver`, and picks one uniformly per call
     (`FuzzerMutate.cpp:53-60, 541-560`);
   - **run *W*** through `LLVMFuzzerTestOneInput`;
   - **if the run found new coverage**, libFuzzer saves *W*'s bytes to the corpus and the round
     ends.
   - Mutations therefore *stack*: iteration *i* mutates the buffer that iteration *i−1* ran.

**What we add, per step:**

| Step | Today (`FuzzGen`) | `ChoiceFuzz` |
|---|---|---|
| Mutate *W* | `LLVMFuzzerMutate` on bytes | ① get *W*'s trace; ② re-encode *W* from it (repair, §3.1); ③ apply one operator using the trace's kinds, bounds and spans; ④ write *W* (≤ `MaxSize`) |
| Crossover | (none) | the same, with *Q*'s trace for the donor |
| Run *W* | decode bytes per draw, run generator + property | decode records per draw, run generator + property, **append one trace entry per draw**, hand the trace to C once at the end |
| After the run | (coverage dump; hybrid scan in hybrid mode) | keep the trace as "last run"; if the run hit a fresh feature, also store it in the cache under *W*'s hash |

**Where ①'s trace comes from:**
- **Iterations 1–4:** *W* is exactly the buffer that just ran, so its trace is the "last run"
  trace. No lookup and no execution.
- **Iteration 0, and *Q*:** the unit is from the corpus. It was run when it was admitted, which is
  a run that found new coverage, so its trace is in the cache.
- **Misses:** after a restart from an on-disk corpus, a unit replaced by libFuzzer's
  smaller-input reduction, or a unit from another process. A miss costs **one re-run** of that unit
  (generator + property). It happens at most once per unit per process, and each unit's trace is
  cached after.

**Run-time cost, in summary:**
- **Extra executions:** none in steady state; at most one per cache miss.
- **Per test:**
  - O(draws) of bookkeeping: decode, one trace append per draw, one hand-off copy, plus the
    mutator's re-encode and operator.
  - The C-side check for "hit a fresh feature", which the hybrid code already implements
    (`basalt_hybrid_scan`). It is O(counters) per run, so measure it. The cheaper fallback is an LRU
    of recent traces, accepting more misses.
- **Expected size.** The generator and property dominate a Cedar test: build a term, typecheck,
  evaluate, hash. The bookkeeping is a few words per draw. That is an expectation, not a
  measurement, so Phase 0.4 measures it before Phase 1 is built, and Gate 1 refuses to judge
  coverage until throughput is ≥ 0.8× `fuzz-noramp`.
- **Contrast with EI.** EI's measured 0.43–1.01× came from execution-indexing instrumentation on
  every call and return in the JVM. Nothing here instruments calls; under design B the hooks cost
  one extra branch per draw at `ChoiceFuzz` and specialize away elsewhere.
- **Memory.** One trace per admitted corpus unit: draws × ~16 bytes. Neither number is
  measured for Cedar yet (0.4 does). At, say, 10⁴ units of a few hundred draws each, it is tens of
  MB.

## 4. Benchmarks and measurement protocol

- **Targets.**
  - Cedar `gen-traced` (primary) and `wide-traced`;
  - `chain-2/3/4`;
  - the BST bug suite;
  - a new **needle** property (a magic constant behind an equality);
  - `long-n` is **retired** from the gates: it assumes zero-extension (Appendix B, Q1.1).
- **Arms:**
  - `random`, `fuzz-noramp`, `auto-1` (the current best hybrid);
  - each new variant, alone and under the hybrid rule.
- **Metrics.**
  - Edges by tests *and* by time (`BASALT_COV_OUT`), distinct expressions (`BASALT_H`), and edge-set
    unions (`edge-sets.py`).
  - **Diagnostic: input size over the campaign** (Cedar expression size). Vikram's thesis
    (§5.5, Fig. 5.11) finds that coverage guidance grows sizes away from the generator's
    distribution, so a size shift can explain a coverage difference.
  - **Throughput (execs/s), always reported.** TOSEM's recommendation, because overhead creates and
    hides wins.
  - Bug-finding as a success rate at a fixed budget (`compare-grow.sh` style, ≥300 trials).
- **Statistics.**
  - ≥5 trials per arm on Linux (REPORT §3.5's setup), with medians and Mann-Whitney.
  - **The primary criterion is the ceiling:** edges at the largest budget, 5M tests and the
    matching wall-clock time. It is judged by tests *and* by time, for the pure fuzzing arm and for
    the hybrid.
  - "Better" means significant at p < 0.05 on that criterion, with no significant loss on the other
    targets. "Tie" means not significant either way.
  - A gate's winner gets one confirmation run at a longer budget (20M tests, or 4 h), because
    ceilings show late.
  - New-expression rate and per-operator rewards are diagnostics that explain a result, not
    criteria.
- **Reporting.** Each gate's tables and charts go in `reports/<yyyy-mm>-choice-fuzzing/`, as with
  the hybrid report. Each gate ends with a short written verdict that names the branch taken.

## 5. Plan: a decision tree

The steps are ordered, and each gate names what to do on each outcome. "Report" means write up the
gate's result and keep going on the stated branch. **Stop** means pause and ask the user.

### Phase 0 — diagnostics and the fill experiment (no new design; parallelizable)

**0.1 Why are fuzz tests wasted?** Instrument `FuzzGen` campaigns on Cedar `gen-traced` (1M tests,
`fuzz-noramp` and `auto-1`). For each mutation, log:
- whether the child's expression equals the parent's, and whether it is new overall;
- the *cause* of a repeat:
  - (a) every mutated offset is ≥ the parent's cursor (unread bytes);
  - (b) every touched choice decodes to the same value after `% range`;
  - (c) values changed but the expression did not (masked downstream);
- a parent–child expression distance, for all children and for saved ones;
- choices per test and execs/s.

| Outcome | Then |
|---|---|
| (a) is a large share of repeats (≥ 20%) | Quick win in today's `FuzzGen`: truncate the buffer to the parent's cursor before `LLVMFuzzerMutate`, as Zest's `gc()` does. Measure (0.3). The record format (Phase 1) removes the cause by construction anyway. |
| (b) is large | Strong support for typed records. Phase 1 as planned. |
| (c) dominates | The representation's *direct* effect on repeats is limited: the waste is in what the property does with a changed value. Raise the priority of the structural, constants and destructive operators. Gate 1's ceiling test is still the decisive one, because operators can raise coverage without lowering repeats much. |
| Saved children are more distant than all children (as TOSEM #5) | Start the bandit with a high prior on destructive operators. |
| Otherwise | Start the bandit with uniform priors. |

**0.2 Fill experiment.** Change `FuzzGen.readByte` past the end from 0 to seeded random
(`SplitMix(hash(buffer), i)`), behind a flag. Run {zero, random} × {`--grow` off, on} on
`gen-traced`, `wide-traced` and `chain-n`. Also run a `gen-traced` variant that draws the
expression *last* (the order that failed). Check that `basalt-fuzz replay` reproduces an artifact
under random fill.

| Outcome | Then |
|---|---|
| Random fill better (edges or distinct expressions), no significant loss elsewhere | Make it `FuzzGen`'s default, keeping zero as a flag. Rebaseline `fuzz-noramp`/`auto-1` with it for all later gates. It is confirmed as `ChoiceFuzz`'s fill. |
| …and random fill + `--grow` beats random fill alone | Materialization pays. Keep §3.1's materialize-before-mutate as a Phase 1 priority. |
| …but random fill + `--grow` does not beat random fill alone | Materialization is still required in Phase 1 (fill values must be mutable), but weight its benefit low in expectations. |
| Tie | Keep zero as `FuzzGen`'s default. `ChoiceFuzz` still uses a fresh fill, which misalignment requires. Note that the frontier is not the bottleneck on Cedar. |
| Random fill worse | Unexpected. Check determinism and the length distribution (random fill lengthens runs), then report. `ChoiceFuzz`'s misfit fill defaults to *simplest* instead of fresh. |

**0.3 (only if 0.1 found (a) large).** Measure truncate-to-cursor. If it is better, adopt it in
`FuzzGen` and rebaseline.

**0.4 Cost probe (answers "what does the bookkeeping cost?" before anything is built).** Add a
flag to `FuzzGen` that does the trace bookkeeping and discards it:
- append `(kind = nat, value, lo, hi)` per draw to an array in the state;
- hand it to C once per run;
- on the C side, run the fresh-feature check and copy the trace into a hash table.

Measure execs/s with and without the flag on `gen-traced`, plus draws per test and corpus size at
1M and 5M.

| Outcome | Then |
|---|---|
| Overhead ≤ 10% | Phase 1 as designed. |
| 10–20% | Phase 1, but profile first: is it the Lean array, the hand-off or the scan? Fix the largest. |
| > 20% | Before Phase 1, redesign the hot part: e.g. record into a C-side buffer through one `@[extern]` push per draw, skip the scan and use an LRU, or switch to self-describing records (§3.1), which need no cache. |

### Phase 1 — the record substrate (design A, all kinds `.nat`)

1. **`ChoiceFuzz`** (§3.2) with records, fill and trace. Pin the decode contract and determinism
   in `BasaltTest/Fuzz.lean`, beside `readNat_recordDraw`. `replay` works on record buffers.
2. **C side:**
   - trace hand-off and cache;
   - materialize-before-mutate;
   - an operator registry with bandit scheduling, and per-operator reward statistics in the log;
   - `LLVMFuzzerCustomCrossOver` for the record splice.
3. **Operators without kinds:** local value, constants (the untagged-cmp hook first; literal
   harvesting is 3.3), destructive, and the kind-sequence splice (with only `.nat`, this means
   range-compatible runs).
4. **Hybrid:** the random phase emits realized `ChoiceFuzz` traces as seeds, and the switching rule
   is unchanged.
5. **The needle property** (§4).

**Gate 1.** Arms: `random`, rebaselined `fuzz-noramp` and `auto-1`, `choice`, `choice-auto`.

| Outcome | Then |
|---|---|
| `choice` execs/s < 0.8× `fuzz-noramp` | Profile and fix (trace hand-off, cache misses, mutator cost) **before** judging coverage. Re-gate. |
| Cache misses are a visible share of executions, or the cache is a visible share of memory or time | Switch to self-describing records (§3.1) and re-gate. |
| `choice` beats `fuzz-noramp` on the ceiling (§4), and `choice-auto` is ≥ `auto-1` | Phase 2. |
| `choice` beats `fuzz-noramp` but `choice-auto` < `auto-1` | Inspect the switch point and the random phase's seeds under choice mode, fix, and re-gate the hybrid only. Then Phase 2. |
| Better by tests, worse by time, and not fixable | Report, then Phase 2 anyway: kinds may change the ratio. |
| Tie or worse | Read the operator stats and rerun 0.1's cause log on the `choice` arm. The likeliest cause is kind-less misalignment (a branch index read as a `.nat`), which kinds address, so go to Phase 2 as a rescue. If Phase 2 also fails, **stop** and write up the negative result. |
| Needle found by `choice`, not by `fuzz` | Keep the constants family on by default. |
| Needle found by neither | Debug the cmp hook: are operands captured, untagged correctly, and offered only where permitted? |

### Phase 2 — kinds and spans

**2.0 B or C** (§6, decision 1). Default without an answer: prototype **B** on a side branch,
limited to the hooks and the combinators `frequency!`, `oneOf!`, `listOf`, `chooseInt`,
`elements`, `coin` and the new `stringOf`.

| Outcome of `lake build` with B | Then |
|---|---|
| Only hook plumbing breaks (the `Obs`/`GenRel` fields, the new `gen_map`/`spec_apply` lemmas, a handful of mechanical proof fixes) | Continue with B. Merging B needs **user approval**, since it changes the `Gen` bundle. |
| Fan-out: many mechanical fixes, or walker rules beyond the hooks need changes (CLAUDE.md rule 9) | Revert and do **C** (§3.3). |

**2.1 Kinds** per the §3.1 table, with the alignment rule and the support-rule test.

**2.2 `stringOf`, the `.string` kind, string operators and the string literal pool.**

**2.3 Recursion spans:** the minimal `@[traced]` rewrite, wrapping recursive occurrences in `span`.
Do it in order on BST, then CedarTyped (mutual `partial_fixpoint`), then CedarGen (dynamic lists,
`Fam` recursion). If CedarGen's extension stalls, report and run Gate 2 on BST and CedarTyped plus
combinator spans only.

**2.4 Operators that need kinds and spans:**
- branch flip (keep suffix / regenerate span);
- element delete and duplicate;
- joint length edit;
- same-label span splice;
- nested self-embedding.

**Gate 2.** Phase 1's arms plus `choice-kinds` and `choice-kinds-auto`.

| Outcome | Then |
|---|---|
| Kinds+spans beat Phase 1 | Phase 3 by its own triggers. |
| Gain comes from kinds alone (span operators earn little reward) | Drop the span operators from the default schedule and skip 3.1. Phase 3 continues with 3.2–3.3. |
| No gain over Phase 1, and Phase 1 beat `auto-1` | Keep Phase 1 as the result, write up, and **stop**. |
| No gain over Phase 1, and Phase 1 did not beat `auto-1` | Write up the negative result and **stop**. |

### Phase 3 — extensions, each with its own trigger

- **3.1 Address-based replay** (EI-style, using Hegel's `(label, ordinal)*` addresses), as an
  alternative replay mode. **Trigger:** Gate 2's stats show branch flips often rewarded *and* most
  sibling spans after a flip change, i.e. positional suffixes are scrambled. **Accept** only if it
  is better at equal tests *and* ≥ 0.8× throughput.
- **3.2 Choice-level shrinking** for `replay` artifacts (Hypothesis passes, shortlex). **Trigger:**
  any campaign finds a bug.
- **3.3 Literal harvesting at elaboration time** (Nat/Int/String literals of the target and
  property). **Trigger:** Gate 1 or 2 shows the constants family rewarded, or Cedar edges sit behind
  literal comparisons.
- **3.4 Reflective import of value seeds.** **Trigger:** only if a user-supplied seed corpus is
  needed.

## 6. Decisions (resolved)

1. **Design B or C (§3.3): the default.** Prototype B on a side branch, fall back to C on fan-out
   (Phase 2.0), and merge B only with the user's approval, since it changes the `Gen` bundle.
2. **`long-n`: retired** from the gates. Use `chain-n`, the needle and Cedar.
3. **Where the work lands:** branch `choice-fuzz` off `hybrid-fuzz`. This file is at the repository
   root and reports go under `reports/`.

## 7. References

These are the sources the design leans on. The appendices cite them in detail.

- **Vasudev Vikram, *Automating Software Testing with Intelligent Input Generation*, PhD thesis,
  CMU-S3D-26-109, August 2026.** https://vasumv.github.io/pdfs/thesis.pdf. It contains:
  - the Havoc Paradox study (ch. 5.1–5.4);
  - Gentoo (ch. 6);
  - **§5.5, "Cedar: Random is All You Need" (pp. 71–75)**, the closest prior study to ours.

  §5.5 tests Cedar's Rust validator, authorizer and evaluator, using cargo-fuzz/`Arbitrary`
  generators run under bolero's random and libFuzzer engines, 12 h × 5 trials.
  - **Generators.** It compares derived, fail-fast and fail-fix generators. Fail-fix (invalid
    choices patched to valid constants) reaches 91–99.8% validity, and derived generators reach
    0.3–2.5%.
  - **Diversity.** Pure random generation gives a significantly higher share of unique inputs than
    coverage guidance (Fig. 5.10). Derived generators make ~87% duplicates on the authorizer.
  - **Why mutations are wasted.** On a sample of authorizer mutations, about 5% produced duplicate
    byte inputs and 20% changed only the schema. "In 80% of cases, mutations on parametric inputs
    neither changed the schema nor the authorizer inputs, effectively traversing the same generator
    path". Fail-fix generators also map many choice sequences to the same constant.
  - **Size.** Coverage guidance grows input size over the first hours and then plateaus, while
    random generation keeps the generator's size distribution (Fig. 5.11).
  - **Scope.** It measures *validity and diversity*, not coverage. Its caveat: the findings concern
    generators that already encode Cedar's semantic constraints.

  For us, it independently confirms on Cedar the byte-level waste that §5's Phase 0.1 diagnoses,
  with "same generator path" corresponding to causes (a) and (b), and fail-fix masking to (c). Our
  own Cedar data adds what it did not measure: fuzzing's coverage ceiling is higher (§1), which is
  what this work tries to raise further.
- **Li, Huang, Vikram, Lemieux, Padhye, "The Havoc Paradox in Generator-Based Fuzzing", TOSEM
  2025.** https://rohan.padhye.org/files/havocparadox-tosem25.pdf (Appendix B, Q2.1). The
  FUZZING'24 registered report is the earlier, shorter version.
- **Vikram & Padhye, "Fuzzing with Agents? Generators Are All You Need" (Gentoo), arXiv
  2604.01442**, 2026.
- **MacIver & Donaldson, "Test-Case Reduction via Test-Case Generation", ECOOP 2020** (choice
  sequences; the list encoding).
- **Hypothesis**, `hypothesis-python/src/hypothesis/internal/conjecture/` (`choice.py`, `data.py`,
  `engine.py`, `providers.py`, `utils.py`), and issue #3921 (the typed-IR migration).
- **Hegel**, https://github.com/hegeldev/hegel-rust, `hegel-c/src/native/` (`core/choices.rs`,
  `core/state.rs`, `graph.rs`, `core/replay.rs`) and `hegel-c/docs/nondeterminism.md`.
- **HypoFuzz**, https://github.com/Zac-HD/hypofuzz (`provider.py`, `mutator.py`, `corpus.py`).
- **Zest/JQF**, Padhye et al., ISSTA 2019, and `jqf-core/.../ei/ZestGuidance.java` (`LinearInput`).
- **Zeugma**, Hough & Bell, ICSE 2024. **BeDivFuzz**, Nguyen & Grunske, ICSE 2022.
- **Etna**, Keles et al., JFP 2026, arXiv 2603.27002.
- **Reflective generators**, Goldstein et al., ICFP 2023. **Parsing Randomness**, Goldstein & Pierce,
  OOPSLA 2022.
- **GReduce**, Ren et al., arXiv 2402.04623. **Wingate, Stuhlmüller & Goodman**, AISTATS 2011.
- **libFuzzer**, `compiler-rt/lib/fuzzer/FuzzerLoop.cpp` and `FuzzerMutate.cpp` at llvmorg-22.1.8;
  Google's structure-aware fuzzing guide,
  https://github.com/google/fuzzing/blob/master/docs/structure-aware-fuzzing.md.

---

**Note on the appendices.** They are the review record. Section numbers inside them refer to the
first draft, whose §2–§5 have been rewritten. The body above incorporates their corrections, in
particular:
- Hegel replays positionally;
- records store absolute values;
- no whole-buffer byte havoc;
- the zero-mutation claim about EI is withdrawn;
- row 5 of the Q2.4 table is retracted.

## Appendix A. Answers to questions (round 1)

Sources checked for this round:
- `fuzz-run/README.md`, `CEDAR.md`, `reports/2026-10-hybrid-fuzzing/REPORT.md` at `origin/hybrid-fuzz`;
- the Havoc Paradox registered report (FUZZING'24 text);
- Gentoo (arXiv 2604.01442, HTML);
- Hegel at `hegel-rust` HEAD (`hegel-c/src/native/`);
- Hypothesis at HEAD (`internal/conjecture/providers.py`).

Three claims in the body above are corrected here: Q1.1 (`--grow`), Q2.4 (Hegel does *not* realign by
address during mutation), and Q3.2 (whole-buffer byte havoc contradicts the "never fuzz metadata"
principle and is dropped).

### Q1.1 — "Zero-extension means first branch / minimal fuel, so `--grow` hurts"?

You are right, and my sentence ran two things together. Zero-extension is the decoder's behaviour
(`readByte` past the end gives 0) and predates `--grow`. `--grow` only *materializes* those zeros so
mutations can reach them. The measured effect and its explanation are in `fuzz-run/README.md`
"How much growth helps" and `CEDAR.md` Findings:

- **The measurement.** On `long-*` with a fixed budget (300 trials per cell), growth scores 31.4%
  pooled against 28.2% without it, a difference of 3.2 points (z = 1.4, p = 0.15). It is decisive
  only on `long-16` (46.7% vs 35.3%). On Cedar, grown inputs decode to repeats, giving about half as
  many distinct expressions.
- **The mechanism the README isolated.** Filling the extension with *random* bytes instead of zeros
  ties the baseline (50.3% vs 50.0%), so the cost comes from the zeros, not from the appending.
- **Why zeros in particular.** Without `--grow`, the frontier position does not exist. When a
  length-extending mutation (`InsertByte`, `CopyPart`) creates it, the byte placed there is
  *random*. With `--grow`, the frontier is filled with `0`.
- **Why `0` is the bad value.** In Basalt's generators, choice 0 is the first `frequency` branch
  (usually the leaf or stop case) or the smallest size or fuel. One mutation round makes at most
  `-mutate_depth` (5) edits, so most materialized positions stay 0 and the grown input stops as
  early as the short one did. "Semantics-preserving for the run that happened" is not the same as
  "useful for the next mutation".

What this means for the design: fill past the end with **fresh (seeded) random values, not zeros**.
The mutator should also first materialize the parent's *realized* choices, including the values
the fill produced, and only then mutate. That is `--grow` done with the values the run actually
used.

### Q1.2 — Why is `-trace-cmp` useless?

The cause is in `fuzz-run/README.md` (section "what coverage guidance can and cannot see").
`lean_nat_eq`/`_le` do inline into instrumented code and do emit `__sanitizer_cov_trace_const_cmp8`.
But the operand the hook sees is the **tagged** Lean scalar `2n+1`. For `x == 0xDEADBEEF` the hook
reports `0x1BD5B7DDF`, and that value never appears among the buffer's bytes. There are two more
layers of mismatch:
- `choose` returns `lo + raw % range`, not `raw`.
- A Lean `Nat` is not a fixed-width word.

So libFuzzer's comparison-substitution mutators (TORC) plant constants that decode to nothing. The
measured consequence: a 32-bit needle is not found in 5M runs, with or without `-use_cmp`. With a
custom mutator, libFuzzer's default suite, which contains those mutators, is not used at all except
through `LLVMFuzzerMutate`.

This is fixable at the choice level, and that is an argument *for* typed choices (see Q2.4, row 3).
Because the mutator knows `(lo, hi)`, it can plant a candidate value directly in a choice. Candidate
values can come from two places:
- Literals harvested from the property and target at elaboration time. Hypothesis does this:
  `providers.py` `_maybe_draw_constant` returns a constant on 5% of draws, from a global pool of
  boundary-ish ints, floats and strings plus a *local* pool scraped from the user's modules
  (`constants_ast.py`).
- Comparison operands recorded by our own `__sanitizer_cov_trace_cmp*` hook and untagged
  (`(v - 1) / 2`).

### Q1.3 — "Structural information exists on the proof side": what are those examples?

They are Basalt's, not core Lean's. None gives *runtime* structure today. They matter as vocabulary
and as reusable machinery:

- **`@[mix_shape]`** (`Basalt/Obs/Spec.lean:54-81`) defines six "shapes of choice":
  - `range lo hi`: a uniform `Nat` in a range;
  - `threshold`: a biased coin;
  - `index l`: a uniform pick of a list position;
  - `element l`;
  - `select l`: a *weighted* pick, which keeps the weights;
  - `rangeInt lo hi`.

  When the walker proves a law it rewrites each combinator through its `@[gen_map]` lemma into one
  of these (`Basalt/Obs/Combinators.lean`). For example `map_chooseInt` gives
  `O.spec (chooseInt lo hi h) = rangeInt lo hi h pure`, and `map_frequency` gives `select gs …`.
  This is a classification of choice points by kind: int, coin, uniform branch, weighted branch. A
  typed choice sequence needs the same classification, so it supplies `ChoiceKind`, and in design B
  the hooks' laws would be stated against it.
- **`Tuning.Site`** (`Basalt/Tuning/Basic.lean:33-43`) is emitted by `@[tunable]` for each
  `frequency` site. It records a stable name `decl.site<i>`, the number of branches, and the
  number of recursive calls in each branch. Those are exactly a span label, a "weighted n-way
  branch" kind, and the information that tells which branches are structural (they recurse) and
  which are leaves.
- **`@[tunable]`** (`Basalt/Tuning/Attr.lean`) is a MetaM rewrite of a generator's elaborated body.
  It emits a variant and proves by `rfl` that the variant at default arguments equals the original,
  including `partial_fixpoint` bodies and their `_unsafe_rec` executable twin. It shows design C
  (a `@[traced]` rewrite) is feasible here, and it already contains the pieces C needs: site
  discovery, recursive-occurrence detection, and re-proof of monotonicity.

### Q2.1 — EI / Havoc Paradox and well-formed generators

I agree with your reading, and the plan should reweight accordingly. What I could verify:

- **Havoc Paradox (FUZZING'24 registered report).**
  - EI shrinks mutation distance on all seven benchmarks.
  - Its coverage gain over Zest on Closure (24 h, 20 runs: 24,252 vs 24,203 branches) is **not
    significant** (Mann-Whitney).
  - Zeugma's significant gain (24,990) comes with about 2× the executions, which the authors say
    they cannot separate from the technique.
  - The validity question (RQ2) is only *proposed* in that version. I could not open the TOSEM full
    version (ACM returned 403), so I cannot confirm or refute the validity finding you recall.
- **Gentoo (Vikram & Padhye, arXiv 2604.01442).**
  - Coverage guidance plus mutation helps human-written generators significantly on all 7
    benchmarks: +40% on average, from +3% (ChocoPy) to +229% (Commons, whose human generator emits
    random bytes).
  - For agent-written, structure-encoding generators it helps by −0.1% to +2.0%, not significant.
  - The paper attributes the gap to the human generators being naive, which fits your point: the
    big wins come from steering *invalid-producing* generators toward validity.
- **Etna (JFP'26)** agrees: Crowbar over bespoke OCaml generators adds overhead for minimal gain.
- **Cedar is our own data point** for well-formed generators. Fuzzing's 5M plateau is about 100
  edges (~1.4%) above random, and the hybrid reaches it sooner and with less variance. So the gain
  is real but marginal, and it arrives late.

The conclusion I draw: for Basalt-style generators, mutation does not need to fix validity. What it
can improve is **how efficiently it explores the neighbourhood of well-formed inputs that reached
new code**. The best-supported lever for that is the representation of *primitive values*, as you
say (Q2.4, rows 1–4). Address realignment (EI) matters only if Cedar mutations are often
"structure flipped, suffix scrambled". That is measurable before building anything (Q2.4,
step 0), so it becomes a gated option, not the centerpiece.

### Q2.2 — How did I arrive at the minimal choice record? What about strings, and what does Hegel do?

**The minimum is what the instance can see.** `choose` receives only `(lo, hi)`. So the lossless
record is `(lo, hi, value)`. Storing `value − lo` makes the bound check exact and the value
unbiased. Everything else needs information from above `choose`.

**Hypothesis and Hegel use richer kinds** (`hegel-c/src/native/core/choices.rs`;
`conjecture/choice.py`):

| Kind | Constraints (Hypothesis / Hegel) | Basalt source today |
|---|---|---|
| integer | `min, max, weights, shrink_towards` (Hegel: `Small{min,max,towards}` or `Wide` bigint) | `choose`/`chooseNat`/`chooseInt`: min/max yes; weights only via `frequency`; shrink-toward is implicitly `lo` |
| boolean | `p` | 2-way `oneOf`/`frequency`/`coin`; `p` from the weights, invisible at `choose` |
| float | min/max, NaN, smallest magnitude | none |
| bytes | `min_size, max_size` | none |
| string | alphabet `IntervalSet` (shrink-ordered `'0'..'9','A'..'Z'`, …), `min_size, max_size`; Hegel adds an optional grammar/regex constraint, checked on replay by an Earley parser | none: Cedar's `genString` is `listOf genChar` (or `elements`), i.e. a run of char choices |
| (collection) | *not a kind*: Hypothesis `many()` and Hegel `hegel_new_collection`/`collection_more` draw a weighted "more?" boolean per element inside a span | exactly `listOf`'s geometric `oneOf! [stop, cons]` |

**Why strings are one choice in Hypothesis and Hegel.** A whole string can be shrunk, mutated
(Hegel's grammar mutation), or replaced by a harvested literal in one step. In Basalt a string is a
span of choices, so per-character operators work, but "replace this string by `"admin"`" requires
re-encoding a value as choices for *that* generator. Hypothesis does this by inversion (`ValueHole`
plus `strategy._invert`); the reflective-generators paper (ICFP'23) is the general form.

**My proposal follows from that.**
- **Design A:** `(lo, hi, value)` only.
- **Next step:** add a kind and weights (from `frequency`/`oneOf`/`coin`/`chooseInt`).
- **Strings and lists:** treat them as *collection spans* carrying a label, not as primitives.
- **Open point:** a string kind with literal injection needs either a hint from the generator
  (`chooseAs (.string …)` in B/C) or an inversion. I would defer it until a target needs it.
  Cedar's attribute names come from `elements` lists, so they are already a single choice.

### Q2.3 — What does "realign by address, not position" mean?

Take `genBST` and the tree `node (node leaf 2 leaf) 5 (node leaf 8 leaf)`. Its positional choice
sequence is:

```
pos: 0     1    2     3    4     5     6     7    8     9
     node  x=5  node  x=2  leaf  leaf  node  x=8  leaf  leaf
     root       root.left               root.right
```

**Position.** Mutate position 2 (the left subtree's branch) to `leaf`. On positional replay the
left subtree ends at once, and the *right* subtree's branch reads position 3, the old `x=2`. That
value is out of range for a 2-way branch, so it is filled. The right subtree's `x` reads the old
`leaf` choice, and so on. The right subtree is rebuilt from the left one's leftovers. This is the
havoc effect: one structural edit rewrites everything after it.

**Address.** Each draw is named by *where in the generator* it happens: for example
`(genBST,0)/(genBST,1)/(draw,0)` for "the root's second recursive call, its first draw". The record
is a map from those names to values. After the same mutation, the left subtree's old draws are
simply unused, and the right subtree looks up its own names and finds `node, x=8, leaf, leaf`
unchanged. The edit stays local.

Names have to come from somewhere. In JQF EI they come from the call stack plus occurrence counts.
In Hegel's scheme (Q3.3) they come from span labels plus sibling ordinals. Basalt has no spans
without design B or C.

### Q2.4 — Justify the design from the evidence, including Cedar

Honestly: the literature gives *mechanisms* but only weak *effect sizes* for structure-aware
mutation over well-formed generators (Q2.1). The strongest evidence for each part of the design is
Basalt's own measurements. The table maps each measured weakness to its mechanism, to supporting
evidence, and to a prediction that can be tested on Cedar with the existing harness
(`hybrid-experiment.sh`, `BASALT_H` distinct-expression hashes, edge curves).

| # | Measured weakness (Basalt) | Mechanism | Corroborating evidence | Fix in design | Cedar-testable prediction |
|---|---|---|---|---|---|
| 1 | Only ¼–½ of fuzz tests yield a new expression (CEDAR.md); random makes 3.5M distinct expressions in 55 min vs ~2.0M for every fuzz arm | many-to-one bytes→value map: modulo, multi-byte choices, unit ranges, and mutations to buffer bytes beyond what the run read (plausible, not yet measured) | Hypothesis's stated reason for the IR migration, "redundancy" (#3921); EI's much lower "zero-mutation" rate (Havoc Paradox) | records hold only consumed choices; every value edit changes a consumed value to a different in-range value | distinct expressions per fuzz-phase test rise toward random's; the post-switch slope of `auto-1` steepens |
| 2 | Value edits are unaligned and biased: a byte edit can straddle two choices; `% range` bias; a full `Int64` is 8 opaque bytes | byte encoding | Zest names the same issue; Crowbar's FIXME on `mod n` | per-choice value operators: ±δ, boundaries, random-in-range, sign/bit flips on wide ints | fewer wasted tests, as row 1; more edges guarded by numeric boundaries (Cedar `arithBoundsError` paths) |
| 3 | Magic values unreachable (32-bit needle not found in 5M runs); `-trace-cmp` useless (tagged scalars) | constants never reach the buffer in decodable form | Hypothesis's local/global constant pools; libFuzzer CMP/TORC rationale; CONFETTI hints; type-targeted mutation (Hussein et al., ~+20%, partly from constant lookup) | constant pool plus untagged cmp operands, offered as candidate values for a choice whose range admits them | a `magic`-style needle property is found; Cedar edges behind literal comparisons |
| 4 | Frontier and draw-order pathologies: zero-fill is "stop" (Q1.1); 1 distinct expression in the first ~10k tests when the expression was drawn after the request (CEDAR.md); starved entries cannot be canonicalized | "ran out of bytes" exists, and its value is 0 | the `--grow` random-fill variant ties the baseline while zero-fill loses; Zest's random tail; HypoFuzz's fresh fill | seeded fresh fill, materialized into the child before mutating | the fuzz arm's early curve no longer lags random; property draw order stops mattering |
| 5 | The hybrid needs two interpretations (RecordGen/FuzzGen) and judges novelty on the wrong specialization (REPORT) | separate random and fuzz decoders | HypoFuzz: "no prefix" *is* generation (`BlackBoxMutator`) | with fresh fill, an empty record list **is** random generation in the same interpretation; the random phase becomes "mutate nothing" | the hybrid keeps its early lead with one binary path; switching becomes operator scheduling |
| 6 | Structural edits scramble the suffix (positional) | positional replay | EI: smaller mutation distance, but the coverage gain on Closure is n.s.; checkRTL 100% vs 79% | address realignment (needs spans) | **unknown: measure first** (step 0) |
| 7 | No recombination of good substructures | no spans | Zeugma: inheritance rate 0.7–0.9 vs ~0.1, but its coverage gain is confounded by 2× speed; HypoFuzz's own crossover is unaligned and weak | same-label span crossover (needs spans) | edge-set union across trials (where pure fuzz beats the hybrid, 7,294 vs 7,224) closes |

So the combination I would defend is not "every feature in the literature". It is rows 1–5:
typed per-choice values, a constant/comparison pool, and seeded fresh fill, all in design A, which
needs no Basalt changes. Each answers a weakness Basalt measured, and each has a prediction the
Cedar harness can test. Rows 6–7 (spans, addresses, crossover) have literature support but no
Basalt evidence yet, and they are what requires B or C. Gate them on measurements:

- **Step 0 (diagnostic, before building):** log parent→child pairs for a Cedar fuzz campaign.
  Measure the share of children whose expression equals the parent's, and the tree-edit distance
  between the parent's and child's expressions (the Havoc Paradox histogram). That tells how much of
  rows 1 and 6 is real on Cedar.
- **Step 1:** build A with rows 1–5, then rerun the Cedar arms plus `chain-*`, `long-*` and a needle.
- **Step 2:** only if step 0 shows many large, structure-flip jumps among *saved* inputs, or step 1
  plateaus where pure fuzz's diversity suggests recombination would help, add spans (B/C) for rows 6–7.

### Q3.1 — How does `ChoiceFuzz` relate to `FuzzGen`?

It is a sibling interpretation of the same shape, and it gets `Gen` from the same blanket instance.
Only its state and its `choose` differ:

```lean
-- today
structure FuzzState   where buffer : ByteArray; cursor : Nat
abbrev FuzzGen := StateT FuzzState Option
-- choose: read bytesFor(range) bytes at cursor (0 past the end), return lo + raw % range

-- proposed
structure ChoiceState where
  records : Array Nat        -- decoded once from the libFuzzer buffer: stored values (value − lo)
  pos     : Nat
  fill    : SplitMix         -- seeded from hash(buffer); used past the end or on a misfit
  trace   : Array Draw       -- (lo, hi, value, fromFill), returned to C like `deficit` is today
abbrev ChoiceFuzz := StateT ChoiceState Option
-- choose: if pos < records.size ∧ records[pos] ≤ hi − lo then lo + records[pos]
--         else draw from `fill`;  push to trace;  pos += 1
```

`FuzzGen` stays as it is, as the baseline arm. One could generalize `FuzzGen` over a decoder, but
keeping two interpretations makes the comparison clean. As today, the property and the generator
both run at the interpretation.

### Q3.2 — The record format, and libFuzzer never touching metadata

Yes, that is the intent. My "byte havoc on the serialized records" operator contradicted it and is
dropped. The precise contract:

- **The buffer holds values only.** One record per non-unit `choose`, holding `value − lo` in a
  self-delimiting integer encoding (LEB128). No `lo`, `hi`, kind, span or length is ever stored, so
  there is no metadata for a mutation to corrupt.
- **The mutator gets metadata from the parent's trace.** It comes from the run that admitted the
  entry, cached by buffer hash, or from a re-run. So the mutator knows `(lo, hi)` and edits a value
  *within* its choice. Where libFuzzer's byte operators are reused, `LLVMFuzzerMutate` is applied to
  the bytes of **one value** (a sub-buffer, as Google's structure-aware guide recommends), and the
  result is mapped back into `[0, hi−lo]`.
- **libFuzzer cannot bypass the mutator.** Defining `LLVMFuzzerCustomMutator` replaces libFuzzer's
  whole default suite, including its own crossover. Crossover happens only if we define
  `LLVMFuzzerCustomCrossOver`.
- **When the stored sequence no longer matches the requests** (after a structural edit, a stored
  value can be out of range for the choice that now reads it), the reader takes a fresh value from
  `fill`. That is your "generate fresh choices when a match doesn't occur". The case that remains is
  a stored value that *fits* but now means something else (positional misalignment, Q2.3). Only
  addressing fixes that.
- **A raw buffer libFuzzer did not produce through us** (a seed file or `-dict` entry) still
  decodes, because the reader is total: a malformed varint ends the records and the rest is fill.

### Q3.3 — Hegel's "by address" approach

**What an address is.** `draw_address` (`hegel-c/src/native/core/state.rs:2428`) gives each draw a
list of frames:
- for each open span, outermost first, `(label, ordinal)`, where `ordinal` counts the earlier
  siblings with the same label under the same parent;
- then `(DRAW_LABEL, n)`, where `n` counts the direct draws so far in the innermost span.

`graph.rs:91` `draw_addresses` computes the same thing after the fact from a recorded span list. In
`genBST` with a span per recursive call, the right child's first draw is
`(genBST,0)/(genBST,1)/(draw,0)` whatever happened inside the left child. That is what makes it
stable under the Q2.3 mutation.

**Where Hegel uses it: only for nondeterministic tests, not for generation, mutation or
shrinking.** I overstated this in §2 and §3, and this corrects it.
- `hegel-c/docs/nondeterminism.md` describes the use. When the same choice prefix can lead to
  different draws, a failure is stored as a **graph**:
  - nodes are states, identified by an address prefix;
  - edges are draws `(address, value, next state)`;
  - several failing runs are merged by identity.
- Replay (`core/replay.rs`, `GraphWalk`) arrives at each draw by the identity its address reports.
  It serves the first edge *at that address* whose kind fits. No fit is a recorded **divergence**,
  after which the walk is rescued (`Rescue::Pun` / `Rescue::Continue`).
- Ordinary replay, span mutation (`try_span_mutation`, a port of Hypothesis's) and shrinking are
  **positional**. A misfit there is punned to the kind's simplest value, or to its "unit" value if
  the stale value was nontrivial (`resolve_choice`).

The precedent for addressing *during coverage-guided mutation* is therefore JQF EI, which uses
call-stack addresses, along with the probabilistic-programming trace-addressing literature
(Wingate et al.; Gen). Hegel contributes a clean address definition based on spans. That definition
suits Basalt if spans exist (B/C), and it is cheaper and more robust than call-stack indexing in
compiled Lean, where inlining erases call sites.

---

## Appendix B. Answers to questions (round 2)

New sources this round:
- the TOSEM Havoc Paradox paper (Li, Huang, Vikram, Lemieux, Padhye, 2025, the PDF you linked);
- JQF's `ZestGuidance.java` (`LinearInput`);
- Hypothesis `conjecture/utils.py` (`many`) and `providers.py`;
- Hegel `hegel-c/src/lib.rs` (`hegel_new_collection`) and `native/core/state.rs` (`ManyState`);
- MacIver & Donaldson, ECOOP 2020 (full text);
- `BasaltFuzz/Staged.lean` at `origin/hybrid-fuzz`.

**Corrections to earlier rounds.**
- *Zero mutations.* Round 1 cited EI's "much lower zero-mutation rate". The TOSEM version says the
  opposite (Finding #2): "context-aware mutation techniques exhibit a similar zero mutation rate as
  Zest". Only random generation is near zero.
- *Stored values.* Round 1's record format stored `value − lo`. It should store the **absolute**
  value. In `genBST` the bounds of a recursive call depend on the parent's `x`, so an offset means
  a different integer after any upstream change; an absolute value either stays meaningful or fails
  the bound check visibly (Q3.2b).
- *Row 5* of the Q2.4 table is retracted (Q2.4b).

### Q1.1 — Why `--grow` is no better, and possibly worse, than plain zero-extension; and random fill

Your framing is right. Both modes read the same zeros past the end. The *only* difference is that
`--grow` writes them into the buffer before mutating, so they become real bytes. Take `long-n`
(`Staged.lean:69`): each draw is `chooseNat 0 3`, and `0` or `stopAt i` ends the run. A starved run
reads all `L` bytes plus one zero, so the deficit is exactly 1.

- **Without `--grow`** the mutator sees `L` bytes, and position `L` does not exist yet.
  - The only way to progress is to create it. libFuzzer's `InsertByte` picks an index in
    `[0, L]`; at `L` it *appends* a random byte, which survives with probability ½. `CopyPart` and
    `InsertRepeatedBytes` at the end do the same.
  - Every length-extending mutation at the end therefore lands *at the frontier*.
- **With `--grow`** the mutator sees `L+1` bytes, the last being `0`, a **stop sign**.
  - An append now lands at `L+1`, *behind* the stop sign, and is dead: the run still stops at
    position `L`.
  - Progress needs a mutation at exactly position `L`: `ChangeByte` there (one position in `L+1`)
    or an insertion just before it.
  - So `--grow` turns the cheap, common way to make progress into a no-op and leaves one
    position-specific way.

That is the README's explanation ("plants a guaranteed-stopping byte at exactly the frontier
position — the one place where libFuzzer's own `InsertByte` would have put a random byte"),
restated as which mutations stop working.

How strong is the evidence?
- The effect on `long-*` is small: pooled −3.2 points, p = 0.15, significant on `long-16` alone.
- The random-fill variant ties the baseline. That is what the mechanism predicts: a random byte at
  the frontier is what `InsertByte`-at-end would have produced anyway.
- On Cedar the measurement ("half as many distinct expressions") is solid, but the mechanism is
  *not* established. Cedar's deficits span many bytes (an `Int64` alone is 8), so the grown region
  is a long run of "first branch / minimal fuel" choices. A plausible but unmeasured explanation is
  that each round's 1–5 edits are spread over that dead region.
- To settle it: log the mutation offsets relative to the old length, and whether the child decodes
  to a new expression, with and without `--grow`.

**Would random bytes past the end work even better? Probably yes, and it is the cheapest
experiment on the table.**
- **Zest does exactly this.** `LinearInput.getOrGenerateFresh` (`ZestGuidance.java:1250-1280`)
  draws `random.nextInt(256)` past the end *and appends it to the input's values*.
  `LinearInput.gc()` then trims values that were never requested. A saved Zest input is therefore
  exactly its realized choices: no ghost zeros and no unread tail.
- **Zest gets repeatability for free; libFuzzer does not.** Zest owns its loop and saves the
  realized input. Under libFuzzer the saved artifact is the buffer libFuzzer chose, so the fill
  must be a function of the buffer: e.g. `readByte i = byte i of SplitMix(hash(buffer), i)` past
  the end. Replay of artifacts stays deterministic and still needs no flag.
- **Variant 1: change `FuzzGen.readByte` to seeded random fill.**
  - Any edit to the head reshuffles the whole tail. That acts as a built-in "regenerate the suffix"
    mutation, which is destructive, and TOSEM Finding #5 (below) suggests that is not bad.
  - It should remove Cedar's draw-order pathology: an expression drawn past the end becomes random
    instead of "first branch everywhere".
- **Variant 2: variant 1 plus `--grow`, materializing the bytes actually read.** This is Zest's
  `LinearInput` behaviour: the tail becomes stable and mutable with values that were random, not
  zeros.
- **Caveat:** `long-n` stops measuring what it was built to measure. Its "deficit is exactly 1"
  design depends on zero-extension, so under random fill it needs redesign or replacement as the
  length benchmark.
- **Why it is cheap:** it needs no choice-sequence machinery and tests row 4 of Q2.4 in isolation.
  I would run it first.

### Q1.2 — (agreed)

### Q1.3 — Using the existing machinery in the choice sequence

Yes. Concretely:
- **`Tuning.Site` names** (`decl.site<i>`) are stable across runs and compile-time unique, so they
  can serve as **span labels** for branch sites. A span's label is then `(site, branch index)`.
  `Site.holes` (recursive calls per branch) also says which branches are structural.
- **`@[tunable]`'s rewrite** is the engine for design C: it finds the sites and recursive
  occurrences, re-proves fixpoint monotonicity, rewrites `_unsafe_rec`, and emits an `rfl`
  equation. Even under design B it is how spans get placed around *recursive calls*. Combinators
  can place their own spans, but nothing marks "this is a recursive call of `genBST`" except a
  rewrite of `genBST`'s body.
- **The `@[mix_shape]` taxonomy** is the list of choice kinds (Q2.2b). Under design B the
  per-combinator `@[gen_map]` lemmas are where the proof side learns that the new hooks are
  observationally `choose`.
- **Limit:** `@[tunable]` accepts only literal branch lists. CedarGen's dynamic
  `pick (… ++ if … then … else [])` and its `Fam`-record recursion need extensions. That cost
  falls on design C (and on B's recursion spans), not on B's combinator-level kinds.

### Q2.1 — The Havoc Paradox (TOSEM): what is justified, what is speculative

I retract "EI matters only if Cedar mutations are often 'structure flipped, suffix scrambled'".
The paper does not support it. Destructive mutations appear to be *useful*, as you say. Below, I
sort the paper's claims by how well its own data supports them. "Random" means generation with no
mutation. Benchmarks: Ant, Maven (XML), Closure, Rhino (JS), ChocoPy, Gson, Jackson (JSON).

**Well supported by the data:**
1. **Context-aware techniques (EI, BeDivFuzz, Zeugma) reduce mutation distance** on all seven
   benchmarks (Finding #1). They do what they claim mechanically.
2. **Mutation preserves validity better than random generation, and smaller mutations preserve it
   more** (Finding #3, Fig. 11).
3. **Where the generator is always valid, coverage guidance adds nothing on these targets.** On
   Gson and Jackson the validity check is syntactic, so the JSON generator is always valid. There
   *every* technique, including Random, ties: 321 / 1,121 branches (Table 2). Where validity is
   strict, Random is far behind Zest: Closure 11,227 vs 12,520, Maven 669.5 vs 1,138, Ant 755 vs
   920.5. This is the strongest evidence for your reading. Caveat: Gson and Jackson are small
   targets that saturate, unlike Cedar.
4. **Context-aware mutation is expensive** (Table 3): EI runs at 0.43–1.01× Zest's speed,
   BeDivFuzz at 0.20–2.11×, Zeugma at 0.56–0.96× of its own no-crossover variant.
5. **Destructive mutations produce a disproportionate share of coverage-increasing inputs** for EI
   and BeDivFuzz (Finding #5, Fig. 13). The median distance of saved inputs exceeds that of all
   inputs. Zeugma shows the opposite.
6. **Zero mutations are not reduced by context-aware techniques** (Finding #2): their rate is
   similar to Zest's. Mutating fewer bytes (Zest-Mini) *raises* it, and Random is near zero.

**Supported, but small or conditional:**
7. **EI beats Zest significantly on two of seven benchmarks** (24 h): ChocoPy 899 vs 889 (+1.1%)
   and Closure 12,853.5 vs 12,520 (+2.7%), and ties elsewhere.
8. **Zeugma beats Zest on four of seven in the fixed-trial comparison.** Normalized for its
   faster framework (Zeugmaᴺ), it falls below EI on Closure. Its measured advantage is partly
   engineering, as the authors say.

**Speculative or insufficient evidence:**
9. **That *reducing* havoc causes coverage gains.** BeDivFuzz reduces havoc the most and is
   significantly *worse* than Zest on five of seven benchmarks, even trial-bounded. The authors'
   explanation, that EI and Zeugma win by adding fine-grained mutations *while keeping* destructive
   ones, is introduced with "We believe". It is plausible, but it was not tested by an ablation.
10. **Anything about deep targets whose generators are always well formed.** No benchmark has a
    generator that always passes a *semantic* validity check on a deep target, which is the Cedar
    situation. The paper's conclusions do not transfer to us directly either way.
11. **The distance metric** is Levenshtein on serialized text. The authors flag it as a threat for
    tree-structured inputs.

**What this means for us:**
- **Your efficiency point is the right target, and TOSEM says EI does not address it.** Zero
  mutations come from how many raw inputs map to the same value, i.e. from the representation, not
  from locality. CEDAR.md's measure ("only ¼–½ of fuzz tests produce a new expression") is a
  stricter cousin of "zero mutation": a test can differ from its parent yet repeat an earlier
  expression. That rate is the number a typed choice representation should move. It is still
  unproven that it will.
- **Destructive operators must stay in the mix** (claims 5 and 9). Fine-grained operators should
  be *added*, not substituted.
- **Locality (EI / addressing) is not about removing havoc.** It adds an operator class: edit
  inside a subtree without disturbing its siblings. The literature cannot predict whether that
  class pays on Cedar; the only gains measured anywhere are +1–3% (claim 7). Your plan is right:
  defer it, then try it.
- **Step 0 should measure efficiency, not havoc.** Log the share of children equal to their parent
  and the share of new expressions, broken down by *why* a child repeats:
  - the mutation fell on bytes past the cursor;
  - it fell on a byte whose value is unchanged after `% range`;
  - it changed a choice whose effect was masked downstream.

  Each answer points to a different fix.

### Q2.2a — A primitive string kind

Agreed; I had no good reason to defer it.

**What Hegel and Hypothesis do.**
- A string is one choice with an alphabet (`IntervalSet`) and size bounds. Hegel's
  `generate_string` (`draws/mod.rs:345`) wraps that one `draw_string` choice in a `LABEL_STRING`
  span.
- Per-string operators then become possible:
  - edit, insert or delete a character;
  - copy a substring from another string choice;
  - inject a whole literal, as Hypothesis's constant pool does with strings from the user's source
    on about 5% of draws (`providers.py`, `_maybe_draw_constant`).

**For Basalt.**
- Add a library combinator, e.g. `stringOf (alphabet) (minLen maxLen)`. Its model is the
  `listOf`-style generator over characters, so proofs see an ordinary combinator.
- Give `ChoiceFuzz` a way to draw it as **one** record: a `.string` kind holding the whole string.
  Under design B that is a hook defaulting to the model; under design C it is a rewrite target.
- **Obligation to check:** the override must return only values in the model's support (characters
  in the alphabet, length within bounds). Otherwise the fuzzer could show the property inputs the
  generator can never produce. The same rule applies to every override, and it is cheap to pin with
  a test.
- **Cedar:** its strings come from `elements` lists (already one choice) or from
  `listOf genChar`, which would become `stringOf`.

### Q2.2b — How collections work in Hegel and Hypothesis, and the evidence for "more?" over length-first

You read it correctly. Neither engine draws a length and then the elements. A collection is a loop
that asks "another element?" before each one:

- **Hypothesis** (`conjecture/utils.py:262`, class `many`). Each `more()` call:
  - opens a span labelled `ONE_FROM_MANY`;
  - draws one weighted boolean with `p_continue` (computed from the average size);
  - leaves the element's own draws inside that span.

  `min_size` and `max_size` are enforced by *forced* draws, which are recorded but never mutated:
  true below the minimum, false at the maximum. A fixed size draws no booleans at all. Rejected
  elements have their span marked discarded.
- **Hegel** is the same: `hegel_new_collection(min, max)`, then `hegel_collection_more` per
  element (`lib.rs:3091-3170`), over `ManyState` (`state.rs:125`). Its
  `p_continue = length_p_continue(min, max)` targets an average size of
  `min(max(2·min, min+5), (min+max)/2)` (`state.rs:262`).

So "weighted more?" means a biased coin per element. Basalt's `listOf` is already this shape: a
`oneOf! [stop, cons]` per element, i.e. p = ½ and an average length of 1. `listOfMaxLength` and
`vectorOf` are length-first or fixed.

**The evidence is about reduction, not fuzzing.** MacIver & Donaldson, ECOOP 2020, p. 13:10–11,
Fig. 7: with a "more?" bit per element, "an element of the list can be deleted by deleting a
contiguous region of the choice sequence". With a length drawn first, "deleting an element of the
list would require first lowering that length parameter and then deleting a later part of the
choice sequence. Identifying all such pairs would require O(n²) transformations." Hypothesis has a
pass for the length-first pattern, "but its performance is comparatively poor". The same locality
also makes merging adjacent lists a simple deletion.

**For mutation the same argument applies, but untested.** Under positional replay:
- deleting, duplicating or splicing an element is a local edit with "more?" bits;
- with a length first it needs a coordinated two-site edit, or it misaligns everything after the
  list.

I know of no fuzzing study comparing the two directly, so for fuzzing this is a structural argument
from the reducer.

**Tradeoff to keep in mind:** "more?" fixes the length distribution to be geometric, tuned only by
`p`. Rewriting an existing combinator's encoding would change its SPMF model and so what its proofs
say. I would not rewrite `listOfMaxLength`. Instead:
- tag `listOf`'s coin as kind `.more` and its `cons` branch as an element span;
- give length-first lists a `.length` kind plus element spans, with a joint mutation operator
  (change the length and insert or delete an element span together).

### Q2.2c — "Kind and weights" per combinator

Your span formulation is right. In the **trace** (what a run produces, and what the mutator reads),
a branch choice opens a span around the chosen branch's draws, and the span closes when the branch
returns. In the **stored buffer** only `(kind tag, value)` per choice is kept. Spans are recomputed
by replay, as in Hypothesis, whose database format (`choices_to_bytes`) stores choices but not
spans.

| Combinator | Recorded choice | Span | Alignment check on replay (Q3.2b) |
|---|---|---|---|
| `frequency!` / `frequency` | `.branch i of N, weights` | `(site, i)` around branch `i` | same kind, `i < N`, `weight i > 0` |
| `oneOf!` / `oneOf` | `.branch i of N` (uniform) | `(site, i)` | same kind, `i < N` |
| `coin r` | `.bool b` (with `p = r`) | — | same kind |
| `elements xs` | `.index i of N` | — | same kind, `i < N` |
| `chooseInt lo hi` | `.int v` (absolute) | — | same kind, `lo ≤ v ≤ hi` |
| `chooseNat` / bare `choose` | `.nat v` (absolute) | — | same kind, `lo ≤ v ≤ hi` |
| `listOf g` | `.more b` per element (today a 2-way branch) | element span | same kind |
| `listOfMaxLength n g` | `.length k` | element spans | same kind, `k ≤ n` |
| `vectorOf n g` | — | element spans | — |
| `stringOf` (new) | `.string s` | — | same kind, chars in alphabet, length in bounds |
| recursive call of `f` | — | `(f, ordinal)` | — |

Two mechanisms put this information there. Combinator rows need hooks *inside* the combinators:
design B's defaulted `chooseAs`/`span` methods, or C's rewrite to traced twins. The last row needs a
rewrite of the user's body (`@[tunable]`'s machinery), in B and C alike. Weights matter to the
mutator in two ways: they bias branch flips toward or away from rare branches, and a zero-weight
branch is not permitted.

### Q2.3 — Is "by address" the EI framework?

Yes. Address-keyed replay is what JQF's EI does, using call-stack addresses. Hegel defines a
span-based address but uses it only for nondeterministic tests (round 1, Q3.3). Deferring it is
right. Hypothesis/Hegel-style positional replay with kinds and spans is simpler, it is what the
production engines use, and it avoids EI's measured 0.43–1.01× throughput cost.

### Q2.4a — Row 4, restated

Row 4 bundled three different things. Separated:
1. **Draw-order pathology (CEDAR.md):** an expression drawn after the request and entities read
   past the end, i.e. all zeros, i.e. "first branch everywhere". This is a property of
   **zero-valued reads past the end**, with or without `--grow`.
2. **The `--grow` penalty:** a property of **materializing** those zeros, the stop-sign effect in
   Q1.1.
3. **No canonical corpus entry:** libFuzzer admits an input only if it is new or smaller, so a
   longer, equivalent input never replaces a starved one (README, "Limitations").

**One fix covers 1 and 2: seeded random fill.** Without `--grow`, the frontier reads random values
instead of "stop". With `--grow`, the materialized bytes are those same random values, which is
Zest's behaviour. Item 3 is not fixed by any fill. It is why the design materializes at mutation
time from a cached trace (Q3.2c) rather than hoping the long form becomes the corpus entry.

**What would settle it:** the Q1.1 experiment, four arms {zero, seeded-random fill} × {`--grow`
off, on} on Cedar `gen-traced`. Measure edges and distinct expressions by tests, plus the
early-campaign distinct-expression count with the expression drawn *last* (the order that failed).

### Q2.4b — Row 5, retracted

You are right: it is not a weakness. The two-interpretation hybrid is the design, and it measures
well.

I had two small engineering points in mind, neither a design weakness:
- REPORT's notes that random-phase novelty is judged on the `RecordGen` specialization, and that
  the budget is counted in tests even though a random test is about 25% cheaper.
- An observation: with seeded random fill, `FuzzGen` on a fresh seed already *is* random
  generation. That could let one interpretation serve both phases. But the hybrid still needs the
  random phase's realized choices as corpus seeds, which is what `RecordGen` provides, so the
  simplification is small.

By "switching becomes operator scheduling" I meant viewing "generate afresh" as one more mutation
operator under a bandit. The measured switching rule already works, so there is no reason to
replace it. Drop the row.

### Q3.2a — Speed: why this need not be 2× slower

The per-test pipeline is decode, run the property, record the trace, then mutate. Costs:
- **Decoding** a record (a kind tag plus a varint) costs about the same as today's
  `bytesFor`/`readNat`.
- **Recording the trace** appends `(kind, value, lo, hi)` per choice to an array in Lean state,
  handed to C *once* per run as a `ByteArray`, not one FFI call per draw.
- **The mutator** is O(#choices) per call. libFuzzer's own mutators are O(size) too.
- The *generator and property execution* dominates: Cedar typechecks and evaluates every
  expression.

**The cost that could double the price is re-executing the parent to recover its trace. Avoid it:**
- **Iterations 1–4 of a round:** libFuzzer mutates the buffer that *just ran*
  (`-mutate_depth` = 5; README, `--grow` section), so its trace is the last one recorded. This is
  the same fact `--grow`'s `g_short` copy relies on.
- **Iteration 0:** libFuzzer copies a corpus unit, which was executed when it was admitted. Keep
  traces in a table keyed by buffer hash, written when a run hits a new feature. The hybrid's
  `basalt_hybrid_scan` already computes "hit a fresh feature" per run, which predicts admission.
  On a miss, re-run, which costs at most one extra execution per round.

**Target and measure:** report throughput (execs/s against the `fuzz` arm) and *count-based*
coverage alongside time-based. TOSEM's recommendation (2) exists because overhead hid or created
wins in their study. The bar: per-test overhead in the low tens of percent at most, with the
increase in new expressions per test comfortably larger than the slowdown.

### Q3.2b — Misalignment: kinds, and which values are safe

Agreed: bare `[lo, hi, v]` is too specific a key, and kinds are what make alignment robust.

**The safety test is on the value, not on the bounds.** Hypothesis's rule is `choice_permitted`:
the stored value is usable iff its *type* matches the request and the *value* satisfies the new
constraints (for integers, `lo ≤ v ≤ hi`). Your proposal, stored `[x, y] ⊆ [l, h]`, is sound but
stronger than needed: it rejects a stored `5` from `[0, 100]` for a request on `[0, 10]`. So:
- **Store** `(kind, absolute value)` per choice. The stored bounds are not needed for safety;
  they are available from the parent's trace if wanted.
- **Accept** iff the kinds match and the value is permitted by the *new* constraints (the table in
  Q2.2c).
- **Otherwise**, take a fresh value. The *policy* for that is a knob:
  - fresh random (HypoFuzz);
  - simplest (Hypothesis);
  - rescale `v` from the old bounds into the new ones (an alternative a Hypothesis source comment
    discusses but rejects);
  - pun to "nontrivial" (Hegel).

In design A every request has the same kind (`.nat`), so the check is just `lo ≤ v ≤ hi`, with
`v` absolute. That *will* misalign more: a stored branch index `1` is happily read as a `chooseNat`
value. That is the cost of A, and an argument for adding kinds early. It is also why A is best
treated as a step toward B or C rather than as a candidate to evaluate on its own (Q3.2d).

### Q3.2c — Is a filled value written back for later mutation? What do the engines do?

Yes, it must be.
- **Hypothesis:** `ConjectureData` records *every* drawn choice, prefix-served or provider-drawn,
  as the run's `choices`/`nodes`. Corpus entries, database entries and the span mutator
  (`generate_mutations_from`) all work on those realized choices.
- **HypoFuzz:** its corpus stores the realized nodes.
- **Hegel:** the same.
- **Zest:** fresh bytes are appended to the input, and `gc()` trims what was not read.
- **libFuzzer:** we cannot replace the saved buffer, because the admission rule forbids it (item 3
  of Q2.4a). So the mutator **materializes** the parent's realized trace, fill values included,
  into the child *before* mutating it. That is `--grow`'s mechanism, done with the values actually
  used.

The saved crash artifact is the buffer libFuzzer ran. Because fill is seeded by the buffer's hash,
it replays deterministically.

### Q3.2d — Which mutations make sense

I agree that value tweaks alone would tell us little. They would also contradict TOSEM claims 5
and 9, which say destructive operators carry much of the payoff. A useful first operator set has
five families, scheduled by a bandit rewarded by new features (MOpt-style; Kukucka ISSTA'24 shows
the operator mix changes which code is reached).

| Family | Operators | Needs | Rationale |
|---|---|---|---|
| **local value** | random-in-range; ±δ (geometric); boundary (`lo`, `hi`, `lo+1`, `hi−1`, 0); for wide ints, sign and bit flips | bounds | a guaranteed value change; boundary values |
| **constants** | replace a value by a pool constant that is permitted (literals harvested from target and property; untagged cmp operands) | bounds | Q1.2; the 32-bit needle |
| **structural, local** | branch flip at a `.branch`/`.more` choice, either keeping the rest positional or regenerating the branch's span; delete/duplicate an element span; change a `.length` jointly with its element spans; string edits | kinds, spans | the BeDivFuzz "structure-changing" class, done locally |
| **destructive** | truncate at position *k* (the rest is fresh: regenerate suffix); randomize *m* consecutive values; regenerate a whole span | — / spans | TOSEM claim 5; Gramatron's "aggressive" mutations; Zest's havoc |
| **recombination** | splice a donor's span with the same label (Zeugma-style); without spans, splice a run of records whose kind sequence matches | spans / kinds | Zeugma's inheritance-rate results; HypoFuzz's prefix+suffix crossover as the baseline |

**What design A alone can carry:** local value, constants, destructive, and the kind-agnostic
splice, which is still a real operator set. Branch flips, element operations and same-label splices
need kinds and spans.

That shifts my recommendation:
1. Build A's infrastructure (records, trace, cache, mutator, scheduler) as the substrate.
2. Bring in **kinds and spans for the library combinators early**, prototyping B's hooks on
   `frequency!`/`oneOf!`/`listOf`/`chooseInt`/`stringOf`, rather than evaluating A on its own.
3. Run the seeded-random-fill experiment on today's `FuzzGen` (Q1.1) first, in parallel, because
   it needs none of this.

---

## Appendix C. Answers to questions (round 3)

The body has been updated for all of these. This appendix only says what changed and where.

**Goal: a higher ceiling, not just efficiency.** Agreed, and my wording undervalued it. The body now
says (§2): the gains are assumed worth having; the aim is a higher fuzzing ceiling; efficiency is
the lever, expected to raise the ceiling by making more mutations productive. Effect on the plan:
- the gate criterion is now edges at the largest budget, by tests and by time, for the pure arm and
  the hybrid, with a 20M or 4 h confirmation run for a gate's winner (§4);
- the new-expression rate is demoted to a diagnostic;
- Phase 0.1's "masked downstream" branch no longer reads as "won't help" (§5);
- Gate 1 compares `choice` with `fuzz-noramp` directly and adds a branch for "pure arm better,
  hybrid not".

The phase order is unchanged.

**The kind tag is metadata; do we want spans and weights?** Right on both. The kind tag is metadata,
and it is safe because only our code writes the buffer; libFuzzer's own mutators are never invoked
(§3.1, §3.4). Spans and weights are wanted. By default they live in the per-run *trace*, recomputed
on every run, so they are always accurate for the input just run. Storing them in the buffer is now
an explicit variant, **self-describing records** (§3.1): it needs no trace cache and suits
multi-process campaigns, at the cost of larger buffers and possibly stale metadata. Gate 1 adopts
it if the cache shows up in throughput or memory.

**Repairing misalignment after the run: worth it, and at what cost?** Yes, it is what I meant by
"materialization", and it costs no extra run. The run of the mutated buffer *is* the moment
misalignment is discovered, and its trace records what each draw actually received. The repair is
lazy: the next time the mutator touches that input, it re-encodes the buffer from the trace before
mutating. That is the next iteration of the same libFuzzer round, or later from the corpus.
- **Cost:** O(draws) re-encoding, with no copy back into libFuzzer's saved unit, which is not
  possible and not needed.
- **Why it is worth it:** without it, every later edit also re-randomizes all fill-derived values,
  because the fill seed changes with the buffer's hash (§3.1).

**Is `ChoiceFuzz` built on `FuzzGen`?** No. It is a parallel interpretation sharing the runner and
`native.c` plumbing, and `FuzzGen` is kept as the baseline and Phase 0 testbed (§3.2).

**Are the §6 decisions still open? Where are B and C?** B and C are in §3.3: B puts hooks in
`RandomChoice`, C uses a separate class plus a rewrite. §6 now restates each in one line. Decision 1
is genuinely open but only gates Phase 2. Decisions 2 and 3 now have defaults I can proceed on.

**How the libFuzzer integration works and what it costs.** New §3.4: libFuzzer's round structure as
verified in its source; a table of what we do at each step against today; where the parent's
trace comes from with no re-run in steady state; and a cost summary. In steady state the extra
cost is no executions plus O(draws) bookkeeping per test. The constant is unmeasured, so a new
Phase 0.4 "cost probe" measures it on today's `FuzzGen` before Phase 1 is built, with branches for
≤10%, 10–20% and >20%.
