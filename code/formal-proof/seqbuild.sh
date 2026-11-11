#!/bin/bash
# Builds the modules of the package one at a time, in dependency order, each by `lake build +M` inside the landrun
# sandbox that Comparator uses (read-only /, writable .lake only, executables: the Lean prefix and git), so that no
# step runs more than one Lean process. A module already built is replayed. Run from the package root under
# `lake env`. Usage: code/formal-proof/seqbuild.sh LANDRUN ROOT, ROOT the root namespace of the package.
set -u
landrun=$1; root=$2; pfx=$(lean --print-prefix); git=$(command -v git); pkg=$(pwd); log=$(mktemp)
find "$root" -name '*.lean' | LC_ALL=C sort | while read -r f; do
  m=${f%.lean}; m=${m//\//.}
  echo "$m $m"
  grep -oE "^(public )?import $root[A-Za-z0-9_.]*" "$f" | awk -v m="$m" '{ print $NF, m }'
done | tsort > seq-order.txt
n=$(wc -l < seq-order.txt)
while read -r m; do
  t0=$(date +%s)
  "$landrun" --best-effort --ro / --rw /dev -ldd -add-exec --env PATH --env HOME --env LEAN_ABORT_ON_PANIC \
    --env LAKE_CACHE_DIR --ro "$pkg" --rwx "$pkg/.lake" --rox "$pfx" --rox "$git" -- lake build "+$m" > "$log" 2>&1
  rc=$?
  echo "$m rc=$rc $(( $(date +%s) - t0 ))s"
  if [ "$rc" != 0 ]; then tail -30 "$log"; rm -f "$log"; exit "$rc"; fi
done < seq-order.txt
rm -f "$log"
echo "seqbuild: $n modules"
