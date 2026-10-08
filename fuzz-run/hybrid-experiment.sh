#!/usr/bin/env bash
# Copyright (c) 2026 Harrison Goldstein. All rights reserved.
# Released under MIT license as described in the file LICENSE.
# Authors: Michael Hicks
#
# Re-run the hybrid-campaign measurement in CEDAR.md ("Random first, then mutation") and print its
# tables: Cedar edges and distinct expressions at budgets of tests and of time, the arms' edge sets
# compared, and where each hybrid trial switched.
#
#   fuzz-run/hybrid-experiment.sh                          # 3 trials × 5M tests, ~75 min on 12 cores
#   RUNS=1000000 TRIALS=6 fuzz-run/hybrid-experiment.sh    # the 1M round
#   PROP=wide-traced fuzz-run/hybrid-experiment.sh
#
# Everything goes to $OUT: the tables in tables.txt (also printed), the charts in curves.html, and
# the raw per-trial dumps. A time budget is only fair if every trial has a core to itself, so the
# script warns when there are more trials than cores; the test-budget tables are fair regardless.
set -euo pipefail
cd "$(dirname "$0")/.."
PROP=${PROP:-gen-traced}
RUNS=${RUNS:-5000000}
TRIALS=${TRIALS:-3}
ARMS=${ARMS:-random fuzz-noramp auto-1 back-1}
OUT=${OUT:-/tmp/hybrid-exp-$PROP}

cores=$(nproc 2>/dev/null || sysctl -n hw.ncpu)
jobs=$(( $(wc -w <<<"$ARMS") * TRIALS ))
JOBS=${JOBS:-$(( jobs < cores ? jobs : cores ))}
if [ "$jobs" -gt "$JOBS" ]; then
  echo "warning: $jobs trials on $JOBS parallel slots: trials run in waves, so the time tables" \
       "compare trials that ran under different loads" >&2
fi

# The analysis scripts count trials 1, 2, … until one is missing, so stale trials from an earlier
# run with more of them would be counted too. Only clear a directory this script made.
if [ -e "$OUT" ]; then
  if [ -e "$OUT/jobs.txt" ]; then rm -rf "$OUT"
  else echo "$OUT exists and is not an experiment directory; set OUT" >&2; exit 1; fi
fi

export PROP RUNS TRIALS ARMS OUT JOBS
fuzz-run/cedar-experiment.sh > "$OUT.experiment.log" 2>&1 \
  || { echo "cedar-experiment.sh failed; see $OUT.experiment.log" >&2; exit 1; }
mv "$OUT.experiment.log" "$OUT/experiment.log"

{
  echo "# $PROP, $TRIALS trials × $RUNS tests per arm, $(uname -sm), $JOBS parallel on $cores cores"
  echo "# arms: $ARMS"
  python3 fuzz-run/budget-table.py "$OUT" $ARMS
  echo
  echo "Edge sets, pooled over trials"
  python3 fuzz-run/edge-sets.py "$OUT" $ARMS
  echo
  echo "Switches (test at which each trial switched, and to what)"
  for arm in $ARMS; do
    case $arm in random) continue ;; esac
    for log in "$OUT/$arm"/fuzz.*.log; do
      t=${log##*/fuzz.}; t=${t%.log}
      # `|| true`: a trial that never switched matches nothing, and under `pipefail` that would end
      # the script here, silently, with the rest of the table unwritten.
      sw=$( (grep -a "switch to" "$log" || true) \
             | sed -E 's/.*switch to ([a-z]+) after test ([0-9]+).*/\1@\2/' | tr '\n' ' ')
      echo "  $arm trial $t: ${sw:-none}"
    done
  done
} | tee "$OUT/tables.txt"
echo
echo "tables: $OUT/tables.txt   charts: $OUT/curves.html"
