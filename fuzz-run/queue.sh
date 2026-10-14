#!/usr/bin/env bash
# Copyright (c) 2026 Harrison Goldstein. All rights reserved.
# Released under MIT license as described in the file LICENSE.
# Authors: Michael Hicks
#
# Run a list of trials, possibly of several properties and experiments, on one queue of JOBS slots:
#
#   JOBS=7 fuzz-run/queue.sh JOBFILE
#
# Each JOBFILE line is `PROP ARM TRIAL OUT RUNS` (`fuzz-run/run-trial.sh`'s arguments). Every OUT
# gets the current executable and its symbol table once, before any of its trials start, so the
# analysis scripts (`budget-table.py`, `edge-sets.py`, `coverage-curves.py`) read it as they read a
# `cedar-experiment.sh` directory. Lines are run in order, as slots free up.
set -euo pipefail
cd "$(dirname "$0")/.."
JOBFILE=$1
JOBS=${JOBS:-$(( $(nproc 2>/dev/null || sysctl -n hw.ncpu) - 1 ))}
[ -x fuzz-run/basalt-fuzz ] || { echo "build first: fuzz-run/build.sh" >&2; exit 1; }
for OUT in $(awk 'NF {print $4}' "$JOBFILE" | sort -u); do
  mkdir -p "$OUT"
  if [ ! -e "$OUT/cedar-exp-bin" ]; then
    cp fuzz-run/basalt-fuzz "$OUT/cedar-exp-bin"
    nm -n --defined-only "$OUT/cedar-exp-bin" | awk '$2 ~ /^[tTwW]$/ {print $1, $3}' > "$OUT/syms.txt"
  fi
  touch "$OUT/jobs.txt"
done
awk 'NF {print $4, $2}' "$JOBFILE" | sort -u | while read -r OUT arm; do
  mkdir -p "$OUT/$arm"; cp "$OUT/syms.txt" "$OUT/$arm/"
done
# A snapshot of the trial script: bash reads a script as it runs, so editing `run-trial.sh` under a
# running queue broke the trials then in flight at their last line.
snap=$(mktemp "${TMPDIR:-/tmp}/run-trial.XXXXXX.sh")
cp fuzz-run/run-trial.sh "$snap"
xargs -P "$JOBS" -L 1 "$snap" < "$JOBFILE"
rm -f "$snap"
