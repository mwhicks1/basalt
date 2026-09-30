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
# Arms (ARMS, space-separated):
#   random       random choices inside libFuzzer's loop (`--backend=io-libfuzzer`): the control
#   fuzz         coverage-guided `FuzzGen`, libFuzzer's defaults (its input-length ramp on)
#   fuzz-noramp  coverage-guided, `-max_len=65536 -len_control=0` (the best-measured setting)
#   fuzz-grow    coverage-guided with Basalt's `--grow`
#
# Every arm runs the same binary, so instrumentation and counters are identical and only the source of
# the choices differs. The binary is copied under a name without `basalt-fuzz` in it, so that another
# session's `pkill basalt-fuzz` cannot interrupt a trial (one did). Trials run in parallel (JOBS).
# Output: $OUT/curves.html and a table of coverage and distinct expressions at 10..RUNS tests.
set -euo pipefail
cd "$(dirname "$0")/.."
PROP=${PROP:-gen-traced}
RUNS=${RUNS:-1000000}
TRIALS=${TRIALS:-2}
ARMS=${ARMS:-random fuzz fuzz-noramp}
JOBS=${JOBS:-$(nproc)}
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

run_one() {
  arm=$1; t=$2
  case $arm in
    random)      be=io-libfuzzer; flags=() ;;
    fuzz)        be=fuzz; flags=() ;;
    fuzz-noramp) be=fuzz; flags=(-max_len=65536 -len_control=0) ;;
    fuzz-grow)   be=fuzz; flags=(--grow) ;;
    *) echo "unknown arm $arm" >&2; return 1 ;;
  esac
  BASALT_COV_OUT="$OUT/$arm/$be.$t.cov" "$BIN" --backend="$be" "$PROP" -runs="$RUNS" \
    -artifact_prefix="$OUT/$arm/" "${flags[@]}" > "$OUT/$arm/$be.$t.log" 2>&1 || true
  echo "[$arm trial $t] done"
}
export -f run_one; export OUT BIN PROP RUNS
xargs -P "$JOBS" -L 1 bash -c 'run_one "$0" "$1"' < "$jobs_file"

series=()
for arm in $ARMS; do
  case $arm in random) be=io-libfuzzer ;; *) be=fuzz ;; esac
  series+=("$arm=$OUT/$arm:$be")
done
python3 fuzz-run/coverage-curves.py "$OUT/curves.html" "${series[@]}"
