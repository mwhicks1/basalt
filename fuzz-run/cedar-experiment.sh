#!/usr/bin/env bash
# Copyright (c) 2026 Harrison Goldstein. All rights reserved.
# Released under MIT license as described in the file LICENSE.
# Authors: Michael Hicks
#
# The Cedar coverage experiment (CEDAR.md): run one traced property under several arms, several
# cold-start trials each, and chart Cedar code coverage and distinct inputs against tests run.
#
#   fuzz-run/cedar-experiment.sh                       # defaults below
#   PROP=wide-traced RUNS=200000 TRIALS=3 fuzz-run/cedar-experiment.sh
#
# Arms (ARMS, space-separated) are `fuzz-run/run-trial.sh`'s.
#
# Every arm runs the same binary, so instrumentation and counters are identical and only the source of
# the choices differs. Trials run in parallel (JOBS).
# Output: $OUT/curves.html (log x axes), $OUT/curves-linear.html (linear, with the first 100 s), and a table of coverage and distinct expressions at 10..RUNS tests.
set -euo pipefail
cd "$(dirname "$0")/.."
PROP=${PROP:-gen-traced}
RUNS=${RUNS:-1000000}
TRIALS=${TRIALS:-2}
ARMS=${ARMS:-random fuzz fuzz-noramp}
JOBS=${JOBS:-$(nproc 2>/dev/null || sysctl -n hw.ncpu)}
OUT=${OUT:-/tmp/cedar-exp-$PROP}

[ -n "${NOBUILD:-}" ] || fuzz-run/build.sh >/dev/null
mkdir -p "$OUT"
BIN="$OUT/cedar-exp-bin"
cp fuzz-run/basalt-fuzz "$BIN"
nm -n --defined-only "$BIN" | awk '$2 ~ /^[tTwW]$/ {print $1, $3}' > "$OUT/syms.txt"

jobs_file="$OUT/jobs.txt"; : > "$jobs_file"
for arm in $ARMS; do
  mkdir -p "$OUT/$arm"; cp "$OUT/syms.txt" "$OUT/$arm/"
  for t in $(seq 1 "$TRIALS"); do echo "$arm $t" >> "$jobs_file"; done
done

run_one() { fuzz-run/run-trial.sh "$PROP" "$1" "$2" "$OUT" "$RUNS" "$BIN"; }
export -f run_one; export OUT BIN PROP RUNS JOBS
xargs -P "$JOBS" -L 1 bash -c 'run_one "$0" "$1"' < "$jobs_file"

series=()
for arm in $ARMS; do
  case $arm in random*) be=io-libfuzzer ;; choice*) be=choice ;; *) be=fuzz ;; esac
  series+=("$arm=$OUT/$arm:$be")
done
python3 fuzz-run/coverage-curves.py --linear "$OUT/curves-linear.html" "${series[@]}" > /dev/null
python3 fuzz-run/coverage-curves.py "$OUT/curves.html" "${series[@]}"
