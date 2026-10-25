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
#   auto-dw      `auto-1`, plus the doubling-window exit (`--switch-rule=doubling`)
#   back-<φ>     the same rule in both directions, switching back to random (`--switch-back`)
#   choice       the choice-sequence backend (`--backend=choice`)
#   choice-auto-<φ>  the choice backend under `auto-<φ>`'s hybrid rule
#   +rfill       seeded random fill past the end (`--fill=random`)
#   +grow        `--grow`
#   +probe       the trace cost probe (`--trace-probe`)
#   +diag        the mutation log (`--diag-mutations`)
#   +trunc       cut an input to the bytes its run read before mutating it (`--truncate`)
#   +plant       plant harvested literals and comparison operands into recorded draws (`--plant`)
#   +nudge       move a recorded draw by a small signed delta (`--nudge`)
#   +cmp         plant compared operands into recorded draws, as libFuzzer's CMP mutation (`--cmp`)
#   +time=S      stop after S seconds (`-max_total_time=S`); with RUNS=-1 the campaign has no `-runs`
#   +simplest    the choice backend's misfit fill is the least value (`--fill-policy=simplest`)
#   +ops=a.b.c   the choice backend's operators restricted to a, b, c (`BASALT_CHOICE_OPS`)
#   +uniform     the choice backend's operators chosen uniformly (`BASALT_CHOICE_BANDIT=0`)
#   +costaware   the choice bandit charges an operator its children's run time (`BASALT_CHOICE_COSTAWARE=1`)
#   +posbits     the choice mutator picks records in proportion to their ranges' bits (`BASALT_CHOICE_POS=bits`)
#   +nocap       the choice mutator's input cap lifted (`BASALT_CHOICE_CAP=1000`)
#   +nokinds     the choice backend records every draw as `.nat` and no spans (`--no-kinds`)
# NOCOV=1 skips the coverage dump, for bug-finding trials that only need the verdict.
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
  auto-dw)     be=fuzz; flags=(--warmup-stall=0 --switch-rule=doubling -max_len=65536 -len_control=0) ;;
  auto-*)      be=fuzz; flags=(--warmup-stall=0 --level="${base#auto-}" -max_len=65536 -len_control=0) ;;
  back-*)      be=fuzz; flags=(--switch-back --level="${base#back-}" -max_len=65536 -len_control=0) ;;
  choice)      be=choice; flags=(-max_len=65536) ;;
  choice-auto-*) be=choice; flags=(--warmup-stall=0 --level="${base#choice-auto-}" -max_len=65536) ;;
  *) echo "unknown arm $arm" >&2; exit 1 ;;
esac
IFS=+ read -r -a ms <<<"${mods#+}"
envs=()
for m in "${ms[@]}"; do
  case $m in
    "") ;;
    rfill) flags+=(--fill=random) ;;
    grow)  flags+=(--grow) ;;
    probe) flags+=(--trace-probe) ;;
    diag)  flags+=(--diag-mutations) ;;
    trunc) flags+=(--truncate) ;;
    plant) flags+=(--plant) ;;
    nudge) flags+=(--nudge) ;;
    cmp) flags+=(--cmp) ;;
    time=*) flags+=(-max_total_time="${m#time=}") ;;
    simplest) flags+=(--fill-policy=simplest) ;;
    ops=*) envs+=(BASALT_CHOICE_OPS="$(tr . , <<<"${m#ops=}")") ;;
    uniform) envs+=(BASALT_CHOICE_BANDIT=0) ;;
    nokinds) flags+=(--no-kinds) ;;
    costaware) envs+=(BASALT_CHOICE_COSTAWARE=1) ;;
    nocap) envs+=(BASALT_CHOICE_CAP=1000) ;;
    posbits) envs+=(BASALT_CHOICE_POS=bits) ;;
    *) echo "unknown modifier $m in $arm" >&2; exit 1 ;;
  esac
done
mkdir -p "$OUT/$arm"
[ -n "${NOCOV:-}" ] || envs+=(BASALT_COV_OUT="$OUT/$arm/$be.$t.cov")
env "${envs[@]+"${envs[@]}"}" "$BIN" --backend="$be" "$PROP" -runs="$RUNS" \
  -artifact_prefix="$OUT/$arm/" "${flags[@]}" > "$OUT/$arm/$be.$t.log" 2>&1 || true
echo "[$PROP $arm trial $t] done $(date +%H:%M)"
