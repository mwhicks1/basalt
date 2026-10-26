# Switching by stale effort: a structure-scaled rule for both directions

Follows [`../2026-10-gt-cmp/REPORT.md`](../2026-10-gt-cmp/REPORT.md), on branch `hybrid-stale` (off
`hybrid-gt-cmp`), cherry-picked to `cedar-mutants` for the Cedar fault runs.

## Why

The rules so far judge a mode against the wrong thing:

- `auto-1` (the window rule) compares random only with its own track record, `φ · F / H`, and sizes
  its windows by the budget left. A nearly unproductive mode gets a *low* bar and so a long stay (71%
  of the budget on the needles); without `-runs` it has no horizon at all.
- The doubling window (`auto-dw`) detects only saturation, "no new edge in the last doubling", which a
  target with logarithmic coverage growth (Cedar) never reaches. It needs `auto-1` beside it as a
  backstop, which is a patch, not a rule.
- Probing fuzzing in short bursts cannot measure fuzzing's yield either: a seed needs time before it
  pays (a start-up cost), and right after a switch fuzzing's rate is depressed by the coverage random
  already took.

## Plan (agreed 2026-10-26)

### Criteria (the user's)

1. Let random search in breadth until it is stale.
2. Give fuzzing a fair effort per input before judging it.
3. Account for each mode inheriting most of the coverage from the other: judge a mode by its own
   effort since it began, never by comparing its rate with the other's.

### The rule (`auto-stale`)

Following Driller (NDSS 2017: the fuzzer is "stuck" after a number of mutations, proportional to input
length, with no new state transition) and AFL's "cycles without finds", effort is scaled by structure
and each mode is judged by "stuck after a fair effort":

- **One yardstick,** `E = L̄ · ln L̄` tests, where `L̄` is the current corpus's mean size in bytes. Under
  `--truncate` a corpus input is exactly as long as its run read. In a random round the corpus is the
  seeds random is collecting.
  - Why size: the cheap neighbourhood of an input grows with its length (AFL's deterministic stage
    does a fixed set of mutations per position).
  - Why `ln`: libFuzzer has no deterministic stage. Its mutations land at random positions, so
    touching each of `L` positions once takes about `L · ln L` of them (the coupon-collector bound).
    So `E` is derived, not tuned.
  - Why bytes: libFuzzer's own mutations, the bulk of the mix, act on bytes. `--cmp` and truncation
    act on draws, but they change only how productive a mutation is, not the logic.
  - One mutation step is one test, since libFuzzer runs the property after every step, so random's
    tests and fuzzing's mutations are the same unit.
- **Random → fuzzing** when random has gone `E` tests without a find, within its round. Producing one
  more seed by breadth now costs more than fuzzing would spend on a seed's neighbourhood. Unlike any
  scale-free "nothing lately" test, this fires on logarithmic growth, where gaps between finds grow
  like `n`. A small floor (256 tests) guards a cold start.
- **Fuzzing → random** when fuzzing has gone `E` tests without a find, within its round. libFuzzer
  shares effort unevenly (its entropic schedule), so the test is global, as Driller's is.
- **A find** is a test that reached a feature (an edge and its hit-count bucket) no earlier test did:
  libFuzzer's own notion of progress, and exactly what it keeps as a corpus input and what the hybrid
  keeps as a seed. So "no find within `E`" means "no new material for fuzzing". (The previous round
  counted edges because Good-Turing's `f₁` is a *state* that hit-count buckets inflated; a gap-based
  rule has no such problem, since extra features only shorten the gaps.)
- **Expected placement on Cedar,** from the random-only traces: `L̄` is about 100–150 bytes, so `E` is
  about 460–750 tests. Finds arrive 1.5–2.5× as often as new edges (179 finds against ~70–110 new
  edges between tests 100k and 200k on `gen-traced`), so random should go stale around 60k–120k tests
  (with edges, ~30k–60k). That is the range of `auto-1` (100k–150k of 1M) and of the fixed warm-ups in
  `CEDAR.md` (10k–100k, similar results). On the needles it goes stale at the floor.
- **No budget dependence.** `-runs` only ends the campaign, so the same rule runs with or without it.
  Alternation in both directions falls out of the rule.
- **Switching back keeps libFuzzer's corpus and coverage,** as today.

### Arms

On one new binary, with `+trunc+cmp` throughout (the supported configuration):

- `auto-stale` (`E = L̄ · ln L̄`), at ¼× and 4× of `E`. These show the result does not hinge on the
  exact value; they are not for tuning.
- `auto-stale-edges`: the same rule counting new edges instead of finds, since edges are the reported
  metric.
- `auto-stale-corpus`: fuzzing judged per corpus pass, `E · |C|` (`|C|` the corpus size), as
  AFL's cycle effectively does. Criterion 2 for every seed, at the cost of much longer fuzzing rounds.
- References: `auto-1`, `auto-dw`, `fuzz-noramp`, `random`.

### Tidying, before the build

- **`--truncate` becomes unconditional** in fuzz mode, and its flag goes. It was never worse in any
  measurement (chain-n 21→37%, 40→64%, 50→64%; Cedar and the BST bugs tie), and the rule's `L̄`
  assumes truncated inputs.
- **`--plant` and `--nudge` are retired** in favour of `--cmp` (code, flags, `run-trial.sh` modifiers,
  `fuzz-run/README.md`); earlier reports keep naming them, as history.

### Calibrated variant (if `E` turns out poorly placed)

Measure fuzzing's start-up cost directly: the mutations from an input's entry into the corpus to its
first new edge, for inputs that produce one. After the first fuzzing round, use their 95th percentile
as `E` for both directions. Before then, use the structural `L̄ · ln L̄`.

### Measurements

As in the previous round: the needles; Cedar coverage and rare edges at 1M tests; Cedar without
`-runs` (30 min); the 19-pair Cedar fault suite, 10 trials × 500k. Also, per trial: switch points,
rounds per mode, and `L̄` over time.

## Later, not in this round

- **Switching back with a fresh start:** drop the corpus and coverage on the way back to random.
  libFuzzer keeps both inside the process, and restarting from the old corpus rebuilds its coverage on
  load, so a true reset is a new process with no corpus, an independent campaign run by a driver
  above libFuzzer. Prompted by `CEDAR.md`: three independent pure-fuzzing trials pooled reached 7,294
  edges against the hybrid's 7,224.
- **Retiring `--grow` and `--fill=random`,** measured worse (`--grow` on Cedar: repeats, half the
  distinct inputs; random fill on chain-n for the byte fuzzer), but documented with measurements in
  `fuzz-run/README.md` and `CEDAR.md`, which would become history.

## Results

TODO
