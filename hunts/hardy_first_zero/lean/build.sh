#!/bin/bash
# Kernel-check this hunt's Lean, file by file, against the pinned Mathlib build.
#
#   LAKE_DIR=/path/to/zeta-lab/lean/.lake bash hunts/hardy_first_zero/lean/build.sh [OUT_DIR]
#
# LAKE_DIR needs only the pinned Mathlib build under packages/*/.lake/build/lib/lean
# (`lake exe cache get` in lean/ provides it). The four ZetaLean modules this hunt
# imports (Rigor, IntervalExp, IntervalCExp, HardyZ) are compiled here from this
# tree's own lean/ZetaLean sources, so the check is against the sources in this commit,
# not against whatever ZetaLean oleans LAKE_DIR happens to hold. Everything is written
# to OUT_DIR (default: a fresh temporary directory), nothing into the tree. One `lean`
# process at a time; never run beside heavy numerics or another Lean build
# (CLAUDE.md, compute discipline). Measured on a 4-core container: about 6 minutes.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
TREE_LEAN="$(cd "$HERE/../../../lean" && pwd)"
LAKE_DIR="${LAKE_DIR:-$TREE_LEAN/.lake}"
OUT="${1:-$(mktemp -d)}"
LEAN="${LEAN:-$(cd "$TREE_LEAN" && elan which lean)}"
LP="$OUT"
for p in "$LAKE_DIR"/packages/*/.lake/build/lib/lean; do LP="$LP:$p"; done
export LEAN_PATH="$LP"
mkdir -p "$OUT/ZetaLean" "$OUT/HardyFirstZero"
for m in Rigor IntervalExp IntervalCExp HardyZ; do
  echo "== ZetaLean.$m (from $TREE_LEAN)"
  ( cd "$TREE_LEAN" && "$LEAN" --root="$TREE_LEAN" "ZetaLean/$m.lean" -o "$OUT/ZetaLean/$m.olean" )
done
cd "$HERE"
for m in Spine Phase EulerMaclaurin BoxSupport Boxes FirstZero; do
  echo "== HardyFirstZero.$m"
  "$LEAN" --root="$HERE" "HardyFirstZero/$m.lean" -o "$OUT/HardyFirstZero/$m.olean"
done
echo "== statement and axioms"
"$LEAN" "$HERE/CheckAxioms.lean"
