#!/usr/bin/env bash
# Copyright (c) 2026 Harrison Goldstein. All rights reserved.
# Released under MIT license as described in the file LICENSE.
# Authors: Michael Hicks
#
# Bug finding as a success rate at a fixed budget (DESIGN-choice-sequences.md §4): for each arm
# (`run-trial.sh`'s names), the share of TRIALS campaigns of BUDGET tests that report a
# counterexample, ±1 binomial SE.
#
#   ARMS="fuzz-noramp choice" TRIALS=300 fuzz-run/bug-rate.sh chain-3 1000 OUT
#
# Trials run on one queue of JOBS slots (`queue.sh`); OUT keeps their logs.
set -euo pipefail
cd "$(dirname "$0")/.."
PROP=$1; BUDGET=$2; OUT=$3
TRIALS=${TRIALS:-300}
ARMS=${ARMS:-fuzz-noramp choice}
mkdir -p "$OUT"
jobs="$OUT/rate-jobs.txt"; : > "$jobs"
for t in $(seq 1 "$TRIALS"); do for arm in $ARMS; do echo "$PROP $arm $t $OUT $BUDGET" >> "$jobs"; done; done
NOCOV=1 fuzz-run/queue.sh "$jobs" > "$OUT/rate-queue.log"
for arm in $ARMS; do
  case $arm in random*) be=io-libfuzzer ;; choice*) be=choice ;; *) be=fuzz ;; esac
  hits=$( (grep -la 'BASALT PROPERTY FAILED' "$OUT/$arm"/$be.*.log 2>/dev/null || true) | wc -l)
  python3 -c "
h,n=$hits,$TRIALS; p=h/n
print(f'$PROP  {\"$arm\":28} budget $BUDGET  {h}/{n}  {p*100:5.1f}% ±{(p*(1-p)/n)**.5*100:.1f}')"
done
