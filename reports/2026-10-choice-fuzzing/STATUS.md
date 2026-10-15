# Choice-sequence fuzzing: status

Live log of the plan in [`DESIGN-choice-sequences.md`](../../DESIGN-choice-sequences.md) §5. Newest
entries first. Raw data (not checked in): `/local/home/mwhicks/fuzz-data/`. Experiments run 7 trials
at a time on this 8-core machine.

## Current

- **Gate 1 + Gate 2, combined: running** since 07:15 UTC 2026-10-15 (100 trials, 5M tests, 7 at a
  time, ETA ~01:00 UTC 2026-10-16). One binary from `choice-design-b`; arms `random`,
  `fuzz-noramp`, `fuzz-noramp+trunc` (0.3's Cedar part), `auto-1`, `auto-1+trunc`,
  `choice+nokinds` and `choice-auto-1+nokinds` (Gate 1: design A), `choice` and `choice-auto-1`
  (Gate 2: kinds + spans), `choice+simplest` (fill policy); on `gen-traced` and `wide-traced`.
  Queue log: `fuzz-data/g12/queue.log`. Bug-finding rates for these arms are done
  (`fuzz-data/g12/rates/rates.txt`).
- **Phase 0 done**: [`PHASE0.md`](PHASE0.md).

## Log

- 2026-10-15 — **Phase 0 complete** ([`PHASE0.md`](PHASE0.md)). `wide-traced`: random fill
  6,643 vs 6,631 edges (p = 0.15), +23% distinct, 1.10× throughput; `--grow` worse (p = 0.008).
  Draw-last variant: random fill fixes the draw-order handicap (4,403 vs 2,090 edges at 100 tests;
  7,032 vs 6,959 at 1M). Verdicts: `FuzzGen` keeps zero fill (chain-n loss); materialization stays,
  low expectations; probe in the 10–20% band, `ChoiceFuzz`'s cheaper hand-off measured at 0.90×.
  A waiter script deadlocked the gate's start for ~10 minutes (its `pgrep -f` matched my own
  waiters); fixed by hand.

- 2026-10-15 — **Phase 3.2 (choice-level shrinking) done**, its trigger having fired (campaigns
  find bugs): `BASALT_SHRINK=1 basalt-fuzz --backend=choice replay <prop> <file>` writes
  `<file>.min` (`choice-design-b` @ `77b35cf`). `bst-buggy-insert2`: 13 records → 5 in 81 runs
  (`t = node leaf 1 leaf, k1 = 1, k2 = 2`); `bst-buggy-delete`: 24 → 10.

- 2026-10-15 — **0.2 / 0.4 on `gen-traced`** (5M × 5, `phase0-fill-gen.txt`). Edges: zero fill
  7,171; random fill 7,173 (p = 0.33, tie) with +21% distinct expressions (3.03M vs 2.50M);
  `--grow` 7,113 (p = 0.016, worse); random fill + `--grow` 7,161 (no better than random fill
  alone). Probe: 0.90× throughput (10.3% overhead), 171–243 draws per test, ~3,900 cached traces,
  17–21 MB at 5M. **Reading:** fill ties on coverage but loses badly on chain-n, so not "better with
  no loss elsewhere"; pending `wide-traced`, zero stays `FuzzGen`'s default, and both fill policies
  go into the gate for `choice`. Grow+random not better than random → materialization stays in
  Phase 1 with low expectations. Probe at the 10% line → 10–20% row ("profile first"); `ChoiceFuzz`
  already uses the cheaper `ByteArray` hand-off and measures 0.90–0.92×, which Gate 1 re-measures.

- 2026-10-15 — **Needle (Gate 1's constants check, run early):** `needle` at 2,000 tests: `fuzz`
  0/100, `choice` 84/100; `needle-2` at 10,000: 0/100 vs 26/100 → "found by `choice`, not by
  `fuzz`": the constants family stays on by default. **Fill policy within `choice`** on chain-n:
  simplest 56% / 64% / 55% vs fresh 49% / 59% / 55% (300 trials) — slightly better; Cedar decides.
  Throughput on one core at 100k tests: `--truncate` 0.94×, `choice --no-kinds` 0.92×, `choice`
  0.90× of `fuzz-noramp`, all above Gate 1's 0.8× bar.

- 2026-10-15 — **Phase 2.1/2.4 implemented on `choice-design-b`** (`9fcbb6c`, pins `+1`): records
  carry kinds, spans are trace events, and the mutator adds branch flip (keep / regenerate),
  span regeneration, same-label span splice, hoist and nested self-embedding. Recursion spans (2.3)
  look unnecessary for now: a recursive generator's calls sit inside `frequency`/`oneOf` branches,
  so branch spans already nest as its subtrees do. 20k-test smoke on `gen-traced`: with kinds cov
  10,356 vs 10,030 with `--no-kinds` (design A, same binary); the span operators have the highest
  reward rates (embed 13.5%, hoist 8.6%, regen 7.4%; trunc 6.3%). **Plan change:** Gate 1 and Gate 2
  share one binary built from `choice-design-b`, `--no-kinds` being the Phase 1 arm, so Gate 2 only
  adds the kinds arms to Gate 1's runs.

- 2026-10-14 — **Phase 2.0, kinds: continue with B.** The design-B kinds prototype builds the
  whole library, examples and tests (`choice-design-b` @ `0bb7ab1`). Fan-out: two `rfl`-defaulted
  fields each on `Obs` and `GenRel`; `chooseAs = choose` simp lemmas for `WP`/`WPC`/`SPMF`/
  `SPMF.Cost`; one `chooseAs` rule per relational judgment (4); ~10 one-line proof edits. No walker
  rule and no example proof changed — 2.0's "only hook plumbing breaks" row. Merging needs your
  approval (it changes `RandomChoice`). Spans next, as `spanOpen`/`spanClose` events (defaulted to
  `pure ⟨⟩`) rather than a wrapper, which would need a new monotonicity law in `Gen`.
- 2026-10-14 — **Incident:** editing `fuzz-run/run-trial.sh` while queue 1 ran made 4 finished
  trials re-execute part of the edited script and truncate their `.log`s (fill-gen `fuzz-noramp`
  #2, `+rfill` #2, `+rfill+grow` #1, `+probe` #1). Their coverage dumps are intact, so edge and
  throughput metrics are unaffected; their distinct-expression counts are missing. `queue.sh` now
  runs a snapshot of the script.

- 2026-10-14 — **chain-n, truncate and choice** (300 trials per cell): `fuzz-noramp` / `+trunc` /
  `choice` — chain-2 23% / 36% / 49%; chain-3 44% / 60% / 59%; chain-4 46% / 71% / 55%. Truncating
  to the cursor is a large win on the staged benchmarks; `choice` beats plain byte fuzzing too.
  Cedar 0.3 arms are queued behind 0.2.
- 2026-10-14 — **Phase 2.0 prototype of design B** started early, in worktree
  `/local/home/mwhicks/src/basalt-b` (branch `choice-design-b`): `RandomChoice.chooseAs` (defaulted
  to `choose`) with a `ChoiceKind`, used by `chooseInt`/`elements`/`oneOf`/`frequency`/`coin`/
  `listOfMaxLength`. `Obs` gains two defaulted fields (observations forget kinds; the specification
  monad's `chooseAs` is `choose`, `rfl` for every existing one), `GenRel` one. So far: four
  mechanical fixes in `GenRel` and `Obs/Combinators`. Spans are the open question — a `span` method
  needs a monotonicity law the `Gen` bundle does not have.

- 2026-10-14 — **0.1 done** (gen-traced-repr, 1M × 2 trials per arm). New expression: 46% of mutated
  children in both arms. Repeats of the parent: (a) unread bytes 20% (`fuzz-noramp`) / 24% (`auto-1`)
  of repeats; (b) same draws 24% / 19%; (c) draws changed 42% / 51%, but ~80% of (c) changed the
  request/entities, so truly masked repeats are ~5% of children. New-feature children are much
  further from their parents (median draw edit distance 26 vs 12; expression token distance 64 vs
  1). **Branches taken:** (a) ≥ 20% → 0.3 truncate-to-cursor (implemented, queued); (b) large →
  typed records as planned; (c) largest → structural/destructive/constants operators prioritized;
  saved children more distant → bandit starts with 2× prior on destructive operators (done).
  Table: `fuzz-data/p0/diag/causes.txt`.
- 2026-10-14 — **0.2, chain-n part** (300 trials per cell, fixed budgets): random fill is far worse
  for `FuzzGen` — chain-2 22% → 7%, chain-3 40% → 12%, chain-4 50% → 12%, and `--grow` does not
  rescue it (8%, 11%, 9%). Likely mechanism: libFuzzer saves an input whose progress came from
  *fill* luck, and the next edit changes the buffer hash and so reshuffles the fill — the hidden
  destruction §3.1 predicts; `--grow` materializes only the input just run, not corpus units.
  ChoiceFuzz materializes from the trace cache, which should avoid it (chain rates for `choice`
  running). Cedar arms still running.

- 2026-10-14 — **Phase 1 substrate done** (`765bff6`). Records = kind byte + LEB128 absolute value,
  positional replay, buffer-seeded fresh fill; the bridge keeps each run's realized records and
  bounds (last run + cache of new-feature and size-reducing runs; ~4% parent-trace misses on
  `gen-traced`), materializes before mutating, and picks one of 13 operators by bandit, through both
  `CustomMutator` and `CustomCrossOver`. **Finding:** the `trace-cmp` route to constants cannot see
  Lean `Nat` comparisons at all — they compile to tagged-*pointer* compares, which SanitizerCoverage
  does not instrument (checked in the needle's disassembly), so §1's "operand is tagged" is not the
  whole story. The hook still catches fixed-width ints (Cedar's `Int64`). Pulled §5 3.3 forward in
  minimal form: `harvested_literals%` collects the targets' `Nat` literals at elaboration time. With
  it `choice` finds `needle` in ~1k tests and `needle-2` in ~8.5k; `fuzz` finds neither in 200k.

- 2026-10-14 — Phase 0 instrumentation committed (`5b36b07`): `--fill=random` (replay with
  `BASALT_FILL=random`, verified on a `bst-buggy-insert` artifact), `--trace-probe`,
  `--diag-mutations`. Smoke run (20k tests, `gen-traced-repr`): of mutated children 40% give a new
  expression; repeats of the parent are 28% (a) unread bytes, 22% (b) same draws, 40% (c) draws
  changed (most of those changed the request/entities, not the expression); ~100 draws per test.
- 2026-10-14 — started. Branch `choice-fuzz` @ `9a906ed`.
