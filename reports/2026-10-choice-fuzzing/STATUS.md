# Choice-sequence fuzzing: status

Live log of the plan in [`DESIGN-choice-sequences.md`](../../DESIGN-choice-sequences.md) §5. Newest
entries first. Raw data (not checked in): `/local/home/mwhicks/fuzz-data/`. Experiments run 7 trials
at a time on this 8-core machine.

## Current

- **Phase 0** — implementing the flags for 0.1 (waste diagnostics), 0.2 (seeded random fill) and
  0.4 (cost probe) in `FuzzGen`.

## Log

- 2026-10-14 — started. Branch `choice-fuzz` @ `9a906ed`.
