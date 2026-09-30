#!/bin/bash
# one.sh BUG GEN BACKEND TRIAL
cd "$(dirname "$0")/../.."
ART=${ART:-/tmp/mcexp/art}; mkdir -p "$ART"
b=$1; g=$2; be=$3; t=$4
if [ "$be" = io ]; then
  out=$(timeout 300 fuzz-run/basalt-fuzz --backend=io $g-bug-$b -runs=1000000 2>&1)
  runs=$(echo "$out" | grep -E "^runs +:" | head -1 | awk '{print $3}')
else
  out=$(timeout 300 fuzz-run/basalt-fuzz $g-bug-$b -runs=1000000 -seed=$((t*7919+1)) -artifact_prefix=$ART/$g-$b-$t- 2>&1)
  if echo "$out" | grep -q "deadly signal"; then runs=$(echo "$out" | grep -E "^\[basalt\] runs" | head -1 | awk '{print $3}' | tr -d ,); else runs=""; fi
fi
typed=$(echo "$out" | grep -oE "typed=(true|false)" | head -1 | cut -d= -f2)
if [ -n "$runs" ]; then found=1; else found=0; fi
echo "$b,$g,$be,$t,$found,$runs,$typed"
