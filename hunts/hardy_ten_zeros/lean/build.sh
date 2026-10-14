#!/bin/bash
# Kernel-check this hunt's Lean, file by file, against the pinned Mathlib build.
#
#   LAKE_DIR=/path/to/zeta-lab/lean/.lake bash hunts/hardy_ten_zeros/lean/build.sh [OUT_DIR]
#
# LAKE_DIR needs only the pinned Mathlib build under packages/*/.lake/build/lib/lean
# (`lake exe cache get` in lean/ provides it). Everything this hunt imports is compiled here
# from this tree's own sources: the four ZetaLean modules (Rigor, IntervalExp, IntervalCExp,
# HardyZ) from lean/ZetaLean, and the six HardyFirstZero modules from the sibling hunt
# directory hunts/hardy_first_zero/lean, so the check is against the sources in this commit
# and not against whatever oleans LAKE_DIR happens to hold. Then this hunt's two support
# files, the nine generated bracket files (one per bracket, so a failure names its bracket
# and a rerun can resume), the assembly and the axiom report. Everything is written to
# OUT_DIR (default: a fresh temporary directory), nothing into the tree. One `lean` process
# at a time; never run beside heavy numerics or another Lean build (CLAUDE.md, compute
# discipline). Measured on a 4-core container: about 17 minutes in all (RUNS.md).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
TREE_LEAN="$(cd "$HERE/../../../lean" && pwd)"
FIRST="$(cd "$HERE/../../hardy_first_zero/lean" && pwd)"
LAKE_DIR="${LAKE_DIR:-$TREE_LEAN/.lake}"
OUT="${1:-$(mktemp -d)}"
LEAN="${LEAN:-$(cd "$TREE_LEAN" && elan which lean)}"
LP="$OUT"
for p in "$LAKE_DIR"/packages/*/.lake/build/lib/lean; do LP="$LP:$p"; done
export LEAN_PATH="$LP"
mkdir -p "$OUT/ZetaLean" "$OUT/HardyFirstZero" "$OUT/HardyTenZeros"
for m in Rigor IntervalExp IntervalCExp HardyZ; do
  echo "== ZetaLean.$m (from $TREE_LEAN)"
  ( cd "$TREE_LEAN" && "$LEAN" --root="$TREE_LEAN" "ZetaLean/$m.lean" -o "$OUT/ZetaLean/$m.olean" )
done
for m in Spine Phase EulerMaclaurin BoxSupport Boxes FirstZero; do
  echo "== HardyFirstZero.$m (from $FIRST)"
  ( cd "$FIRST" && "$LEAN" --root="$FIRST" "HardyFirstZero/$m.lean" -o "$OUT/HardyFirstZero/$m.olean" )
done
cd "$HERE"
for m in PhaseShort TenSupport Box2102 Box2501 Box3042 Box3293 Box3758 Box4091 Box4332 \
    Box4800 Box4977 TenZeros; do
  echo "== HardyTenZeros.$m $(date -u +%H:%M:%S)"
  "$LEAN" --root="$HERE" "HardyTenZeros/$m.lean" -o "$OUT/HardyTenZeros/$m.olean"
done
echo "== statements and axioms $(date -u +%H:%M:%S)"
"$LEAN" "$HERE/CheckAxioms.lean"
echo "== done $(date -u +%H:%M:%S)"
