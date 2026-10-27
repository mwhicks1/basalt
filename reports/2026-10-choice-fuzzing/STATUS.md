# Choice-sequence fuzzing: status

Live log of the plan in [`DESIGN-choice-sequences.md`](../../DESIGN-choice-sequences.md) §5. Newest
entries first. Raw data (not checked in): `/local/home/mwhicks/fuzz-data/`. Experiments run 7 trials
at a time on this 8-core machine.

## Current

- **Gates 1 and 2 done** ([`GATES.md`](GATES.md)): negative on Cedar edges; §5's plan stops here.
- **Next:** a Cedar bug-finding target with injected faults, then broader Cedar properties and
  rare-edge reporting.
- **Phase 0 done**: [`PHASE0.md`](PHASE0.md).

## Log

- 2026-10-27 — **`--nat-cmp`** ([`../2026-10-nat-cmp/REPORT.md`](../2026-10-nat-cmp/REPORT.md)): a
  force-included `nat_hook.h` makes Lean `Nat` comparisons reach the comparison hook. Needles with
  literals off: 799 / 3,154 tests with the hook against 145k / 98k without (literals alone: 6.3k /
  8.6k). On Cedar (hooked via `BASALT_NAT_HOOK`, on `basalt-mutants`) it ties on coverage and faults
  (1 / 0) at no throughput cost: Cedar's relevant comparisons are `Int64` and strings.

- 2026-10-27 — **Stale-effort switching: results** ([`../2026-10-stale-switch/REPORT.md`](../2026-10-stale-switch/REPORT.md)).
  `auto-stale-corpus+cmp` (random until `L̄ · ln L̄` tests without a find, then fuzzing judged per
  corpus) ties the best on Cedar coverage at 1M and without `-runs`, and beats `auto-dw` 5 / 0 on the
  fault suite by handing over earlier (~30k vs ~65k). `4E` hands over late and is 0 / 5. On the needles
  every arm pays the 256-test floor, ~2× `auto-dw`. The per-seed variant was not run: libFuzzer's corpus
  membership is not observable.

- 2026-10-26 — **Branches consolidated.** One mainline, `hybrid-fuzzing` (`d5559f4`): `--cmp` replaces
  `--plant`/`--nudge`, the byte fuzzer always truncates, design B's trace-cache policy ported, and
  `policy-traced`, the kill tools and the size-reporting traced properties brought over; the choice
  backend (design A) stays. `cedar-mutants` (`9249d5c`) is now `hybrid-fuzzing` plus the faulty-Cedar
  path dependency and the `CEDAR_MUTANT` selector. Old branches are tags: `archive/choice-fuzz`,
  `archive/choice-design-b`, `archive/hybrid-gt-cmp`, `archive/cedar-mutants-design-b` (every fault
  binary through this date). Commits cited in the reports stay reachable through them.

- 2026-10-26 — **Planned: switching by stale effort** (branch `hybrid-stale`,
  [`../2026-10-stale-switch/REPORT.md`](../2026-10-stale-switch/REPORT.md)). Each mode is judged by
  "no new edge in a structure-scaled effort" `L̄ · ln L̄` (Driller-style), in both directions, with no
  budget dependence. Replaces `auto-1` + the doubling window. Not built yet.

- 2026-10-26 — **Switching rule and `--cmp`: results**
  ([`../2026-10-gt-cmp/REPORT.md`](../2026-10-gt-cmp/REPORT.md)). The doubling window switches at test
  258 on the needles (714k before) and never fires on Cedar: coverage ties, 0 / 0 on the 19 fault
  pairs; without `-runs` it alternates and beats the old rule (which switched at test 11) on
  `gen-traced`. `--cmp` solves both needles alone, costs pure fuzzing nothing on faults (0 / 0), and
  in the hybrid adds edges on `wide-traced` (p = 0.008). Supported configuration:
  `auto-dw+trunc+cmp`.

- 2026-10-25 — **Switching rule and `--cmp`** (branch `hybrid-gt-cmp`,
  [`../2026-10-gt-cmp/REPORT.md`](../2026-10-gt-cmp/REPORT.md)). Good-Turing over features never
  switches (`f₁` in the thousands on Cedar, stuck at 2 on the needle); over edges it needed one-time
  edges excluded by replay, judged brittle and replaced by a doubling-window exit on discovery
  events, with the old rule kept as the guaranteed switch. `--cmp` replaces `--plant`/`--nudge` and
  solves both needles alone. Evaluation queue running (~14 h).

- 2026-10-25 — **Planting in the byte fuzzer** ([`../2026-10-planting/REPORT.md`](../2026-10-planting/REPORT.md)).
  `--plant` (harvested literals and `trace-cmp` operands into recorded draws) plus `--nudge` (an
  aligned small delta) solve both needles 10/10, matching `choice`. On Cedar the planting hybrid
  ties the plain hybrid on coverage and on all 19 fault pairs (0–0), at 7–12% throughput. Pure
  fuzzing with planting is slightly slower on easy faults (0–2, 0–3). Found: the hybrid's switching
  rule stays random for 71% of the budget when random finds fewer than 10 things.

- 2026-10-23 — **Cedar faults, main run done** ([`../2026-10-cedar-faults/REPORT.md`](../2026-10-cedar-faults/REPORT.md)).
  19 pairs × 5 arms × 10 trials. Coverage guidance finds the capability faults (2, 3, 15, 16)
  that random misses (0–4/10 vs 10/10), but is 3–18× slower on shallow ones; the hybrids get both
  (`auto-1+trunc` 9–1 and `choice-auto-1` 7–0 against random). Pure `choice` loses to the byte
  fuzzer 1–7, and the two hybrids are even (2–1). Deep policy faults (6, 7, 13, 28,
  37, 40 on `policy-traced`, 10 trials × 300k): done, mostly ties; on fault 7 random beats both pure fuzzers.

- 2026-10-23 — **Rare edges (item 3)**: `fuzz-run/rare-edges.py`; tables in `GATES.md`. Per trial,
  edges beyond random: `fuzz-noramp+trunc` 55 / 98, `choice` 36 / 39 (p = 0.063 / 0.008).
  **Policy property (item 2)**: `policy-traced` (Basalt `cedar-mutants` @ `e9d5dc0`) checks
  Cedar's validation, level-slicing and authorization theorems over generated policy sets; 98%
  validate; at 100k random tests 8,571 Cedar edges against `gen-traced`'s 6,943. Faults 30–36
  (level checker, slicer, authorizer, policy slicer, validator; Cedar @ `3971469b`) are being
  screened on it.

- 2026-10-23 — **Cedar fault injection: screen done, main run started.** 26 faults, each one that
  `type_of_is_sound` can see (17 typechecker, 9 evaluator), selected at run time by `CEDAR_MUTANT`
  (Cedar `basalt-mutants` @ `c9adf7a7`, Basalt `cedar-mutants` @ `8031d21`, worktrees
  `../cedar-spec-m` and `../basalt-m`). Screen, one trial × 200k tests
  ([`../2026-10-cedar-faults/screen.txt`](../2026-10-cedar-faults/screen.txt)): 6 never killed
  (9, 11, 12, 14, 17, 26), 7 killed by every arm within ~2k tests. `fuzz-noramp+trunc` alone
  kills 3, 15, 24 and `gen`'s 8 and 16; `choice` alone kills `gen`'s 13. Main run: the 19
  non-trivial (fault, property) pairs × `random`, `fuzz-noramp+trunc`, `auto-1+trunc`, `choice`,
  `choice-auto-1` × 10 trials × 500k tests (`fuzz-data/mut/main`).

- 2026-10-23 — **Gates 1 and 2 written up: [`GATES.md`](GATES.md). Stop: negative result.**
  Next, per your direction: a Cedar bug-finding target (injected faults), broader Cedar
  properties, and rare-edge reporting.

- 2026-10-23 — **Re-gate final (5 trials per arm;** [`gate-gen.txt`](gate-gen.txt),
  [`gate-wide.txt`](gate-wide.txt)). Against `fuzz-noramp+trunc` (7,183 / 6,637 edges):
  `gen-traced` — `choice` 7,148 (p = 0.11), `choice-auto-1` 7,152 (p = 0.10), design A 7,063
  (p = 0.008, worse); `wide-traced` — `choice` 6,573 (p = 0.016, worse), `choice-auto-1` 6,624
  (p = 0.31). No choice arm beats byte fuzzing on either property. **Incident:** running two
  `gate-stats.py` at once over the 55-trial gate exhausted the host's 15 GB (no swap) and hung it
  twice; the script now keeps packed per-trial curves (`47b44f1`; 673 MB peak for 10 trials).

- 2026-10-16 02:20 — **Re-gate interim (1–2 trials per arm).** `gen-traced`: `choice` 7,164,
  `choice-auto-1` 7,156, design A 7,094 / hybrid 7,140, `posbits` 7,156, kinds without span
  operators 7,120 — against `fuzz-noramp+trunc` 7,183 and `auto-1+trunc` 7,185. `wide-traced`:
  `choice` 6,579, `choice-auto-1` 6,629 vs 6,637 / 6,661. Throughput 0.98–1.07×. Shape so far:
  kinds + spans beat design A, spans add to kinds, but nothing beats byte fuzzing's ceiling. If the
  remaining trials agree, this is §5's "Phase 2 also fails" → **stop** and write up.

- 2026-10-16 — **`wide-traced` baselines final (5 trials):** `fuzz-noramp` 6,628; `random` 6,520
  (p = 0.008); `+trunc` 6,637 (tie); `auto-1` and `auto-1+trunc` 6,661 (p = 0.008 by tests, but at
  0.39–0.49× throughput, so ties by time, p = 0.135 — the existing hybrid is slow on this property;
  not investigated here).

- 2026-10-15 — **`gen-traced` baselines final (5 trials):** `fuzz-noramp` 7,157; `random` 7,099
  (p = 0.008); `auto-1` 7,173; `auto-1+trunc` 7,185 and `fuzz-noramp+trunc` 7,183 (p = 0.15 each).
  **0.3 verdict:** truncation ties on Cedar and wins clearly on chain-n → adopted; the truncated arms
  are the rebaselined comparison. First re-gate trial with the fixed binary: `choice` 7,184 edges at
  0.98× throughput (was 0.69×); design A 7,063. A slot-filling scheduler (`g12r/fill.sh`) now starts a
  re-gate trial whenever fewer than 7 run, so slow baseline stragglers no longer idle cores.

- 2026-10-15 — **Gate round 1 complete (1 trial each)** — `gen-traced` / `wide-traced` edges:
  `fuzz-noramp` 7,196 / 6,619; `random` 7,097 / 6,536; `+trunc` 7,164 / 6,638; `auto-1` 7,164 /
  6,671; `auto-1+trunc` 7,208 / 6,664; design A 7,040 / 6,544, its hybrid 7,109 / 6,621; `choice`
  7,142 / 6,573, its hybrid 7,143 / 6,631; `choice+simplest` 6,922 / 6,388 with a fifth of the
  distinct inputs → **fresh fill stays `ChoiceFuzz`'s default**. **Throughput fix:** profiling
  (`BASALT_CHOICE_PROFILE`) shows the mutator costs ~7 µs per test against ~900 µs for the Lean
  run, and the run grows with the input (90 → 129 realized records, 858 → 1,102 µs by 1.5M):
  nested self-embedding, the best-rewarded operator, grows inputs. libFuzzer's `-len_control=100`
  holds it flat with the same coverage at 1M/2M, but its early limit would truncate the hybrid's
  seeds, so the mutator now caps its output at 3× the generator's median realized size (`e532801` on
  `choice-design-b`; 498 bytes on `gen-traced`). The kinds arms (and design A, for a like
  comparison) will be re-gated with this binary after the current gate.

- 2026-10-15 — **Gate round 1, first readings (1 trial each, `gen-traced`).** Edges at 5M:
  `fuzz-noramp` 7,196; `random` 7,091; `choice+nokinds` (design A) 7,040; `choice` (kinds+spans)
  7,142. **`choice`'s throughput is 0.69× `fuzz-noramp`** — under Gate 1's 0.8× bar, so its
  coverage cannot be judged yet: it runs at ~950 tests/s for the first million and slows to ~640
  after, while its corpus grows to 5× design A's (1,138 vs 212 KB). Profiling it now
  (`BASALT_CHOICE_PROFILE`, on the spare core) before the fix and a re-gate of the kinds arms.
  Cause logs (`fuzz-run/choice-causes.py`, 1M): new expressions 46% of children with kinds vs 32%
  without (byte fuzzing: 46%); the span operators carry it (embed 89%, hoist 80% new). Most
  record-level edits land in the request/entities, so 63–72% of their children repeat the
  parent's expression. Bandit flaw found and fixed for later binaries (`cbb639b`): failed
  attempts were not counted, so `flip`, which cannot apply under `--no-kinds`, kept its prior;
  effect on the running gate is small (1.5–2% of design-A mutations became random bytes).

- 2026-10-15 — **Phase 3.1 trigger checked (not met).** `BASALT_CHOICE_FLIPDIAG=1`, 50k tests on
  `gen-traced`: 1.8% of flips reach a new feature (embed: 13%), and the records after the flipped
  branch's span survive positional replay exactly in 67% of flips (21% of them change). Address
  replay is for "flips often rewarded *and* suffixes scrambled"; neither holds. Re-checked at gate
  scale later.

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
