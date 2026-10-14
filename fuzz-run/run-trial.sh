#!/usr/bin/env bash
# Copyright (c) 2026 Harrison Goldstein. All rights reserved.
# Released under MIT license as described in the file LICENSE.
# Authors: Michael Hicks
#
# Run one trial of one arm on one property, writing `$OUT/<arm>/<backend>.<t>.{log,cov,cov.time}`:
#
#   fuzz-run/run-trial.sh PROP ARM TRIAL OUT RUNS [BIN]
#
# The layout and the arm names are `cedar-experiment.sh`'s, which calls this. An arm is a base arm
# optionally followed by `+modifier`s, each adding Basalt flags:
#   random       random choices inside libFuzzer's loop (`--backend=io-libfuzzer`): the control
#   fuzz         coverage-guided `FuzzGen`, libFuzzer's defaults (its input-length ramp on)
#   fuzz-noramp  coverage-guided, `-max_len=65536 -len_control=0` (the best-measured setting)
#   fuzz-grow    coverage-guided with Basalt's `--grow`
#   warm-<N>     a random warm-up of N tests (`--warmup=N`), then coverage-guided from its seeds
#   auto-<φ>     the same, but the random phase ends when coverage levels off (`--warmup-stall=0
#                --level=φ`)
#   back-<φ>     the same rule in both directions, switching back to random (`--switch-back`)
#   +rfill       seeded random fill past the end (`--fill=random`)
#   +grow        `--grow`
#   +probe       the trace cost probe (`--trace-probe`)
#   +diag        the mutation log (`--diag-mutations`)
# BIN defaults to `$OUT/cedar-exp-bin`, a copy of the executable under a name without `basalt-fuzz`
# in it, so that another session's `pkill basalt-fuzz` cannot interrupt a trial (one did).
set -euo pipefail
PROP=$1; arm=$2; t=$3; OUT=$4; RUNS=$5; BIN=${6:-$OUT/cedar-exp-bin}
base=${arm%%+*}
mods=${arm#"$base"}
case $base in
  random)      be=io-libfuzzer; flags=() ;;
  fuzz)        be=fuzz; flags=() ;;
  fuzz-noramp) be=fuzz; flags=(-max_len=65536 -len_control=0) ;;
  fuzz-grow)   be=fuzz; flags=(--grow) ;;
  warm-*)      be=fuzz; flags=(--warmup="${base#warm-}" -max_len=65536 -len_control=0) ;;
  auto-*)      be=fuzz; flags=(--warmup-stall=0 --level="${base#auto-}" -max_len=65536 -len_control=0) ;;
  back-*)      be=fuzz; flags=(--switch-back --level="${base#back-}" -max_len=65536 -len_control=0) ;;
  *) echo "unknown arm $arm" >&2; exit 1 ;;
esac
IFS=+ read -r -a ms <<<"${mods#+}"
for m in "${ms[@]}"; do
  case $m in
    "") ;;
    rfill) flags+=(--fill=random) ;;
    grow)  flags+=(--grow) ;;
    probe) flags+=(--trace-probe) ;;
    diag)  flags+=(--diag-mutations) ;;
    *) echo "unknown modifier $m in $arm" >&2; exit 1 ;;
  esac
done
mkdir -p "$OUT/$arm"
BASALT_COV_OUT="$OUT/$arm/$be.$t.cov" "$BIN" --backend="$be" "$PROP" -runs="$RUNS" \
  -artifact_prefix="$OUT/$arm/" "${flags[@]}" > "$OUT/$arm/$be.$t.log" 2>&1 || true
echo "[$PROP $arm trial $t] done $(date +%H:%M)"
