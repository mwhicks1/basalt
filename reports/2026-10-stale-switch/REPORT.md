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

### Amendments

- **2026-10-26, the floor applies to every round.** On tiny inputs `E` is tiny: the needles read about
  3 bytes, so `E = L̄ · ln L̄` is 1–4 tests, and without a minimum the modes would flip every few
  tests. The 256-test floor therefore bounds every round, in both directions, not just the first
  random one. On Cedar (`L̄` around 100 bytes, `E` around 460) it rarely binds.
- **Built** on `hybrid-fuzzing` (`2eebfc3`), with `cedar-mutants` rebased onto it (`ad0e2fa`); one
  binary for all of this round, `424bafda2341`. Arm names drop `+trunc` (truncation is built in).

- **2026-10-26, per-seed fuzzing (`auto-stale-seeds`).** The plain rule judges fuzzing stuck after
  `E` tests without a find anywhere, one input's effort for a corpus of ~900 seeds, which is why it
  flips back ~1,100 times on Cedar. The principle, as agreed: the unit of work is one seed's
  neighbourhood, priced `E = L̄ · ln L̄`, in both modes. Random's price for a new seed is its gap between
  finds, so random → fuzzing when that gap exceeds `E` (unchanged). Fuzzing's units are its seeds, each
  with a budget of `E` mutations; an input it finds is a new seed with a fresh budget. Fuzzing →
  random once no seed has budget left: at that price the only new material left is random's breadth.
  The corpus is the number of pending units, not a multiple of `E`. libFuzzer's entropic schedule
  does not round-robin, so the mutator counts mutations per cached corpus unit (`68fc2f4`).
  `auto-stale-corpus` was a crude stand-in. Built as `seeds-bin`, which differs from the round's
  binary only by this gated code. It runs after the queue in progress.

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

### Needles

10 trials per arm, 1M tests, median tests to the find ([`needles.txt`](needles.txt)). Every arm finds
both needles in 10/10.

| arm | `needle` | `needle-2` |
|---|---|---|
| `fuzz-noramp+cmp` | 6,276 | 8,391 |
| `auto-dw+cmp` | 6,558 | 8,156 |
| `auto-1+cmp` | 720,577 | 721,282 |
| `auto-stale+cmp`, all five variants | 12,668–12,714 | 14,228–15,038 |

The stale rule is about 2× slower here than `auto-dw` and pure fuzzing. Random finds nothing on a
needle, but every random round still runs its 256-test floor, so the modes alternate (about 50
switches before the find) and random takes half the tests: fuzzing's ~6k of its own tests become
~12k in all. The five variants are identical because `E` is 1–4 tests on 3-byte inputs, so the floor
decides everything. A random round that makes no find at all could end sooner; that refinement is
left for later.

### Cedar: coverage at 1M tests

5 trials per arm ([`cedar-coverage.txt`](cedar-coverage.txt)); p against `auto-dw+cmp`. Random's share
of tests and the switch count are from trial 1.

| arm | `gen-traced` | p | `wide-traced` | p (by time) | switches | random's share |
|---|---|---|---|---|---|---|
| `auto-dw+cmp` | 7,297 | – | 6,757 | – | 1 | ~11% |
| `auto-stale+cmp` | 7,280 | 0.14 | 6,728 | **0.008** (0.095) | ~1,100 | ~40% |
| `auto-stale-q+cmp` (`E/4`) | 7,280 | 0.14 | 6,745 | 0.056 | ~3,600 | |
| `auto-stale-x4+cmp` (`4E`) | 7,277 | 0.28 | 6,742 | 0.056 (0.84) | ~110 | ~27% |
| `auto-stale-edges+cmp` | 7,262 | 0.14 | 6,725 | **0.016** | ~1,600 | |
| `auto-stale-corpus+cmp` | 7,288 | 0.38 | 6,745 | 0.31 | 1 | ~3% |
| `auto-1+cmp` | 7,302 | 0.79 | 6,759 | 0.89 | 1 | |
| `fuzz-noramp+cmp` | 7,246 | 0.048 | 6,736 | 0.056 | – | – |
| `random` | 7,197 | 0.008 | 6,655 | 0.008 | – | – |

- **`E` is where the plan put it:** 496–559 tests, `L̄` 106–117 bytes (a traced run).
- **The first switch comes earlier than predicted,** at 28k–31k tests rather than 60k–120k, and below
  `auto-1`'s 100k–150k.
- **Fuzzing is judged stuck too eagerly.** On Cedar fuzzing's finds come in bursts, with gaps longer
  than one input's `L̄ · ln L̄`, so `auto-stale` flips back to random about 1,100 times in 1M tests and
  random takes ~40% of them. That costs ~29 edges on `wide-traced` by tests (p = 0.008; by time a tie)
  and ties on `gen-traced`. The variants that let fuzzing run longer, `4E` (~110 switches) and the
  corpus-scaled one (fuzzing never stuck: one switch at ~28k), tie the best references on both.
- **Edges instead of finds is the weakest variant:** with rarer events it goes stale sooner.
- Every hybrid beats both pure arms, as before.

TODO: no `-runs`, faults
