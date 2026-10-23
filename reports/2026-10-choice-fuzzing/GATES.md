# Gates 1 and 2: choice-sequence fuzzing against byte fuzzing on Cedar

Gates 1 and 2 of [`DESIGN-choice-sequences.md`](../../DESIGN-choice-sequences.md) §5, run together
on Linux x86_64 (8 cores, 7 trials at a time), 2026-10-15/16. Phase 0 is
[`PHASE0.md`](PHASE0.md); the running log is [`STATUS.md`](STATUS.md).

## What ran

- **One binary for every arm**, built from branch `choice-design-b` (design B's hooks in
  `RandomChoice`: `chooseAs` and `span`), so `FuzzGen` arms and choice arms share instrumentation.
  The baselines ran first (`fd`…`fuzz-data/g12`, binary `1b48366`); the choice arms were re-run
  (`fuzz-data/g12r`, binary `fd05b15`) after the round-1 throughput fix (below). The two binaries
  differ only in the choice mutator; `FuzzGen`'s code is the same.
- **Arms.** Baselines: `random` (`io-libfuzzer`), `fuzz-noramp`, `fuzz-noramp+trunc` (Phase 0.3's
  truncate-to-cursor), `auto-1`, `auto-1+trunc` (the adaptive hybrid). Gate 1, design A:
  `choice+nokinds` and its hybrid `choice-auto-1+nokinds` — records all `.nat`, no spans. Gate 2:
  `choice` and `choice-auto-1` — kinds and spans. Ablations: `choice+posbits` (records picked in
  proportion to their ranges' widths) and `choice-nospan` (kinds, span operators off). Round 1 also
  ran `choice+simplest` (the misfit fill takes the least value).
- **Targets and budget.** `gen-traced` and `wide-traced`, 5M tests, 5 trials per arm; Cedar edges
  (the `lp_Cedar_` functions, printing excluded) by tests and by the fastest trial's wall-clock;
  exact two-sided Mann-Whitney against `fuzz-noramp+trunc`, the rebaselined byte fuzzer.
  Bug-finding rates on chain-n, the BST suite and the needles: 300 campaigns per cell
  ([`gate-rates.txt`](gate-rates.txt)).

## The round-1 throughput fix

In round 1 (one trial per arm, binary `1b48366`) `choice` ran at 0.69× `fuzz-noramp`, under Gate 1's
0.8× bar, so its coverage could not be judged. Profiling (`BASALT_CHOICE_PROFILE`) put the mutator
at ~7 µs per test against ~900 µs for the Lean run; the cost was the run itself growing with the
input (90 → 129 realized records, 858 → 1,102 µs by 1.5M tests), driven by nested self-embedding,
the best-rewarded operator. libFuzzer's `-len_control` holds size flat with the same coverage, but
its early limit would truncate the hybrid's seeds, so the mutator instead caps its output at 3× the
generator's median realized size (`e532801` on `choice-design-b`; 498 bytes on `gen-traced`). With
it every choice arm runs at 0.98–1.07× `fuzz-noramp+trunc`, and all of them were re-gated.

Round 1 also settled the fill: `choice+simplest` (misfit records take the least value) reached
6,922 / 6,388 edges with a fifth of the distinct inputs, so fresh fill stays the default.

## Results

Cedar edges at 5M tests and at the fastest trial's wall-clock (61.2 / 51.7 min), medians of 5
trials; p against `fuzz-noramp+trunc` ([`gate-gen.txt`](gate-gen.txt),
[`gate-wide.txt`](gate-wide.txt)):

| arm | `gen-traced` edges@tests | p | @time | p | `wide-traced` edges@tests | p | @time | p | tests/s ratio (gen / wide) |
|---|---|---|---|---|---|---|---|---|---|
| `fuzz-noramp+trunc` | 7,183 | – | 7,153 | – | 6,637 | – | 6,613 | – | 1.00 / 1.00 |
| `fuzz-noramp` | 7,157 | 0.15 | 7,151 | 1.00 | 6,628 | 0.69 | 6,606 | 0.52 | 1.04 / 1.09 |
| `random` | 7,099 | 0.008 | 7,099 | 0.008 | 6,520 | 0.008 | 6,520 | 0.008 | 1.43 / 1.49 |
| `auto-1` | 7,173 | 0.58 | 7,157 | 0.55 | 6,661 | 0.008 | 6,617 | 0.48 | 1.00 / 0.43 |
| `auto-1+trunc` | 7,185 | 0.55 | 7,170 | 0.008 | 6,661 | 0.008 | 6,630 | 0.31 | 0.98 / 0.53 |
| design A: `choice+nokinds` | 7,063 | 0.008 | 7,048 | 0.008 | 6,520 | 0.008 | 6,498 | 0.008 | 1.02 / 1.07 |
| design A hybrid | 7,136 | 0.008 | 7,121 | 0.008 | 6,594 | 0.095 | 6,570 | 0.032 | 1.01 / 1.06 |
| `choice` (kinds + spans) | 7,148 | 0.11 | 7,140 | 0.41 | 6,573 | 0.016 | 6,555 | 0.008 | 1.02 / 1.03 |
| `choice-auto-1` | 7,152 | 0.095 | 7,140 | 0.52 | 6,624 | 0.31 | 6,580 | 0.18 | 0.98 / 1.02 |
| `choice+posbits` | 7,161 | 0.25 | 7,142 | 0.41 | 6,589 | 0.10 | 6,569 | 0.016 | 1.01 / 1.04 |
| `choice-nospan` | 7,129 | 0.008 | 7,113 | 0.008 | 6,544 | 0.016 | 6,532 | 0.008 | 0.98 / 1.01 |

Within the choice arms, by tests (p against `choice`): design A is worse on both properties
(p = 0.008); turning the span operators off is worse on `gen-traced` (p = 0.032) and not significant
on `wide-traced` (p = 0.53); `posbits` ties (0.31 / 0.14). The kinds hybrid against the design-A
hybrid: 7,152 vs 7,136 (p = 0.008) and 6,624 vs 6,594 (p = 0.095); against `auto-1+trunc`, 7,185
(p = 0.056) and 6,661 (p = 0.008).

Per-operator rewards on `choice` ([`gate-ops.txt`](gate-ops.txt)): nested self-embedding is 15% of
mutations and 37–39% of new-feature inputs, at about twice the next operator's rate; truncation,
span regeneration and havoc follow at 7–11% each. The span operators (embed, hoist, span and
flip-regenerate, same-label splice) together are 35–37% of mutations and 54–58% of finds.

Rare edges ([`gate-rare.txt`](gate-rare.txt), `fuzz-run/rare-edges.py`), since the totals are
saturated: per trial, the edges in no `random` trial ("beyond random"), and the edges reached by at
most a quarter of all 40 trials ("rare"), medians with p against `fuzz-noramp+trunc`:

| arm | `gen-traced` beyond random | p | rare | p | `wide-traced` beyond random | p | rare | p |
|---|---|---|---|---|---|---|---|---|
| `fuzz-noramp+trunc` | 55 | – | 22 | – | 98 | – | 4 | – |
| `fuzz-noramp` | 44 | 0.15 | 14 | 0.42 | 104 | 0.33 | 1 | 0.81 |
| `auto-1+trunc` | 58 | 0.60 | 22 | 0.98 | 108 | 0.10 | 8 | 0.024 |
| `choice` | 36 | 0.063 | 7 | 0.087 | 39 | 0.008 | 2 | 0.27 |
| `choice-auto-1` | 33 | 0.056 | 7 | 0.12 | 72 | 0.063 | 2 | 0.39 |
| design A | 14 | 0.008 | 1 | 0.048 | 7 | 0.008 | 0 | 0.14 |
| `choice+posbits` | 43 | 0.095 | 11 | 0.17 | 42 | 0.032 | 2 | 0.66 |

Of the 258 / 121 edges beyond random, the byte fuzzer's five trials reach 169 / 116 between them,
`choice`'s 104 / 78. Here the gap that totals show as 0.5–1% is a factor of 1.5–2.5, the same way
round.

Bug-finding rates, 300 campaigns per cell at fixed budgets ([`gate-rates.txt`](gate-rates.txt);
`choice` from the fixed binary):

| | `fuzz-noramp` | `fuzz-noramp+trunc` | `choice+nokinds` | `choice` |
|---|---|---|---|---|
| chain-2 (500) | 21% | 37% | 45% | 47% |
| chain-3 (1,000) | 40% | 64% | 49% | 53% |
| chain-4 (1,200) | 50% | 64% | 48% | 43% |
| `bst-buggy-insert` (5) | 37% | 36% | 19% | 11% |
| `bst-buggy-insert2` (45) | 32% | 38% | 99% | 100% |
| `bst-buggy-delete` (10) | 12% | 14% | 10% | 6% |
| needle (2,000) | 0% | 0% | 79% | 76% |
| needle-2 (10,000) | 0% | – | 25% | 26% |

## Verdicts

- **Gate 1 (design A): worse.** `choice+nokinds` loses to `fuzz-noramp+trunc` on both Cedar
  properties, by tests and by time, at equal throughput. Per §5 this sends Phase 2 in as a rescue.
- **Gate 2 (kinds and spans): better than Phase 1, not better than byte fuzzing.** Kinds and spans
  recover most of design A's loss (+85 / +53 edges, p = 0.008), and the span operators carry the
  gain (they earn most of the finds; dropping them costs edges on `gen-traced`). But `choice` only
  ties `fuzz-noramp+trunc` on `gen-traced` and is worse on `wide-traced`; its hybrid ties both and
  does not beat `auto-1+trunc`. This is §5's "Phase 2 also fails" → **stop** and report the
  negative result. The confirmation run at 20M tests (§4) applies to a gate's winner, so none was
  run.
- **Outside the ceiling criterion.** The choice backend wins where a target needs a specific value
  or structure: the needles (with the harvested literal pool) and `bst-buggy-insert2`. On chain-n
  it beats `fuzz-noramp` but not truncation, and on the other two BST bugs it is worse. These targets
  are small and specialized, so they show what each representation can do, not which is better on
  real code.
- **What the Cedar gate can resolve.** All arms finish within 2% of each other, and `random` reaches
  ~90% of its final coverage in the first 10k tests; the 5M-test ceiling is decided by ~100 edges
  out of ~7,100 hit and ~62,500 Cedar edges instrumented. Both properties exercise only expression
  typing and evaluation. A negative result here says that the choice representation does not raise
  the ceiling of a nearly saturated target; it does not say how either backend finds bugs in Cedar,
  which needs a target with known faults.
