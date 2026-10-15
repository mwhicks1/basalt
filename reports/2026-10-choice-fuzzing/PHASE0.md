# Phase 0: why fuzz tests are wasted, the fill, and the cost of a trace

Phase 0 of [`DESIGN-choice-sequences.md`](../../DESIGN-choice-sequences.md) §5, run on Linux x86_64
(8 cores, 7 trials at a time) on 2026-10-14/15, all on today's `FuzzGen` behind flags
(`--diag-mutations`, `--fill=random`, `--trace-probe`, `--truncate`; `5b36b07`, `e113526`). Raw
tables beside this file: [`phase0-causes.txt`](phase0-causes.txt),
[`phase0-fill-gen.txt`](phase0-fill-gen.txt), [`phase0-chain-rates.txt`](phase0-chain-rates.txt).

## 0.1 Why are fuzz tests wasted?

`gen-traced-repr` (`gen-traced`, also printing each expression), 1M tests, 2 trials per arm. Every
mutated input is compared with its parent: a repeat of the parent's expression is (a) a mutation
only of bytes the parent never read, (b) a change of bytes that decode to the same draws, or (c)
changed draws that build the same expression.

| | `fuzz-noramp` | `auto-1` |
|---|---|---|
| child's expression new to the campaign | 46% | 46% |
| (a) bytes read unchanged, share of repeats | 20% | 24% |
| (b) same draws | 24% | 19% |
| (c) draws changed | 42% | 51% |
| an earlier expression, not the parent's | 14% | 5% |
| draws per test (median) | 102 | 107 |
| draw edit distance to parent, all / new-feature children (median) | 12 / 26 | 17 / 42 |
| expression token distance, all / new-feature children (median) | 1 / 64 | 0 / 87 |

About 80% of (c) changed the request or entities and not the expression, so only ~5% of children
are masked outright. **Branches taken:** (a) at the 20% line → 0.3; (b) large → typed records as
planned; (c) the largest → structural, destructive and constants operators prioritized; new-feature
children much further from their parents than children overall (TOSEM's Finding #5) → the bandit
starts destructive operators at twice the prior.

## 0.2 Seeded random fill

`gen-traced`, 5M tests × 5 trials (median edges; p is an exact two-sided Mann-Whitney test against
zero fill):

| arm | edges | p | tests/s | distinct expressions |
|---|---|---|---|---|
| zero fill (`fuzz-noramp`) | 7,171 | – | 1,073 | 2.50M |
| random fill | 7,173 | 0.33 | 1,089 | 3.03M |
| zero fill + `--grow` | 7,113 | 0.016 | 1,049 | 1.41M |
| random fill + `--grow` | 7,161 | 0.69 | 1,035 | 1.89M |

chain-n, share of 300 campaigns finding the bug at a fixed budget:

| | zero | random | zero + grow | random + grow |
|---|---|---|---|---|
| chain-2 (500) | 22% | 7% | 26% | 8% |
| chain-3 (1,000) | 40% | 12% | 44% | 11% |
| chain-4 (1,200) | 50% | 12% | 48% | 9% |

On Cedar random fill ties on coverage and raises input diversity by a fifth; on chain-n it is far
worse, with or without `--grow`. The likely mechanism is the one §3.1 predicts for an unrepaired
fill: libFuzzer saves an input whose progress came from fill values, and the next edit changes the
buffer's hash and so redraws them. `--grow` materializes only the input that just ran, not a corpus
unit, so it does not repair it. `ChoiceFuzz` materializes from its trace cache, and on chain-n its
fresh fill is far from this loss (49–59%, [`phase0-chain-rates.txt`](phase0-chain-rates.txt)).
`wide-traced`, 5M × 5 ([`phase0-fill-wide.txt`](phase0-fill-wide.txt)): zero fill 6,631 edges,
random fill 6,643 (p = 0.15), zero + `--grow` 6,605 (p = 0.008), random + `--grow` 6,627; random fill
again +23% distinct expressions, at 1.10× the throughput. With the expression drawn *last*
(`gen-traced-last`, 1M × 3, [`phase0-fill-last.txt`](phase0-fill-last.txt)) random fill removes the
draw-order handicap §1 describes: 4,403 vs 2,090 edges at 100 tests, 6,436 vs 5,598 at 10k, and
7,032 vs 6,959 at 1M, with twice the distinct expressions throughout.

**Verdict:** not "better with no significant loss elsewhere", so `FuzzGen` keeps zero fill.
Random fill plus `--grow` does not beat random fill alone, so materialization stays in Phase 1 with
low expectations. `ChoiceFuzz`'s misfit fill is measured both ways in the gate (fresh and
`--fill-policy=simplest`).

## 0.3 Truncate to the cursor

chain-n, 300 campaigns: `fuzz-noramp` 23% / 44% / 46% → `--truncate` 36% / 60% / 71% (chain-2/3/4).
The Cedar measurement is folded into the gate, which runs `fuzz-noramp+trunc` and `auto-1+trunc`
beside the untruncated arms.

## 0.4 The cost of a trace

`--trace-probe` (every draw recorded as four words, handed to C once per run, new-feature runs'
traces cached), `gen-traced`, 5M × 5: 0.90× the throughput of the same binary without it (10.3%
overhead), 171–243 draws per test, ~3,900 cached traces, 17–21 MB at 5M. That is the 10–20% row:
profile before building. The built `ChoiceFuzz` hands its trace over as two `ByteArray`s rather
than an `Array UInt64`, and measures 0.90–0.92× `fuzz-noramp` on one core; the gate re-measures
it.
