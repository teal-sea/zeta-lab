#!/bin/bash
# Kernel-check this hunt's Lean, file by file, against the pinned Mathlib build. No lake.
#
#   LAKE_DIR=/path/to/zeta-lab/lean/.lake bash hunts/rh_height_lean/lean/build.sh [OUT_DIR]
#   LAKE_DIR=/path/to/zeta-lab/lean/.lake bash hunts/rh_height_lean/lean/build.sh --assembly [OUT_DIR]
#   LAKE_DIR=/path/to/zeta-lab/lean/.lake bash hunts/rh_height_lean/lean/build.sh --full [OUT_DIR]
#   LAKE_DIR=/path/to/zeta-lab/lean/.lake bash hunts/rh_height_lean/lean/build.sh \
#       --file RHHeight/Statement.lean [OUT_DIR]
#
# The first form compiles the statement and the skeleton: the seven modules of the vendored
# zeta23 package (lean/vendor/zeta23) that `RHHeight.Skeleton` imports, with zeta23's own
# lakefile options, then RHHeight.Statement, RHHeight.Skeleton, the root module RHHeight, and
# the axiom report CheckAxioms.lean. The second does the same and then the assembly point:
# the four ZetaLean modules (Rigor, IntervalExp, IntervalCExp, HardyZ) from lean/ZetaLean, the
# six HardyFirstZero modules of hunt #132 and the twelve HardyTenZeros modules of hunt #133,
# all from this tree's sources, then RHHeight.Assembly and CheckAssembly.lean.
#
# The third, `--full`, does all of that and then the theorem: the 31 further zeta23 modules
# the pieces import (five for `gamma_increment`, through GammaFacts.StirlingVert, and the
# 26 of the import closure of RvM.MainTerm for `exact_argument`), the four pieces, each
# followed by its check file (RHHeight/Check*.lean), then RHHeight.Main, which proves
# `RHHeight.rh_height_fifty : RHHeight.RHHeight50`, and CheckMain.lean. That is 74 modules
# compiled from source and seven check files; `check_axioms.py --full` audits the log.
#
# The fourth compiles one file of the package against the modules already in OUT_DIR (run a
# full form once to fill it; `RHHeight/Statement.lean` imports Mathlib only and needs nothing
# there).
#
# LAKE_DIR needs only the pinned Mathlib build under packages/*/.lake/build/lib/lean (the
# root package `lean/` at Lean v4.35.0-rc2, Mathlib 065356127b1d; `lake exe cache get` in
# lean/ provides it). Everything is written to OUT_DIR (default: a fresh temporary
# directory), nothing into the tree.
#
# Like hunts #132 and #133 (hunts/hardy_*/lean/build.sh) this calls `lean` directly and never
# lake: running lake in a copied or shared .lake is how the campaign box's builds were
# damaged before (rule 7 of the campaign's compute rules). One `lean` process at a time; on a
# Linux host it waits while MemAvailable is below 30 GiB before starting each one.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
TREE_LEAN="$(cd "$HERE/../../../lean" && pwd)"
Z23="$TREE_LEAN/vendor/zeta23"
FIRST="$(cd "$HERE/../../hardy_first_zero/lean" && pwd)"
TEN="$(cd "$HERE/../../hardy_ten_zeros/lean" && pwd)"
LAKE_DIR="${LAKE_DIR:-$TREE_LEAN/.lake}"
ONE=""
ASSEMBLY=""
FULL=""
if [ "${1:-}" = "--file" ]; then
  ONE="${2:?--file needs a path relative to $HERE}"
  shift 2
elif [ "${1:-}" = "--assembly" ]; then
  ASSEMBLY=1
  shift
elif [ "${1:-}" = "--full" ]; then
  ASSEMBLY=1
  FULL=1
  shift
fi
OUT="${1:-$(mktemp -d)}"
LEAN="${LEAN:-$(cd "$TREE_LEAN" && elan which lean)}"
LP="$OUT"
for p in "$LAKE_DIR"/packages/*/.lake/build/lib/lean; do LP="$LP:$p"; done
export LEAN_PATH="$LP"
mkdir -p "$OUT"

mem_gate() {
  [ -r /proc/meminfo ] || return 0
  while [ "$(awk '/^MemAvailable/ {print int($2 / 1048576)}' /proc/meminfo)" -lt 30 ]; do
    echo "== waiting: MemAvailable below 30 GiB"
    sleep 30
  done
}

# compile ROOT MODULE [lean options...]: ROOT/Mod/Path.lean -> OUT/Mod/Path.olean
compile() {
  local root="$1" mod="$2"
  shift 2
  local rel="${mod//.//}"
  mkdir -p "$(dirname "$OUT/$rel")"
  mem_gate
  echo "== $mod $(date -u +%H:%M:%S)"
  ( cd "$root" && "$LEAN" --root="$root" "$@" "$rel.lean" -o "$OUT/$rel.olean" )
}

# check FILE: run a check file of this package (pins and axiom reports) against OUT
check() {
  mem_gate
  echo "== check $1 $(date -u +%H:%M:%S)"
  ( cd "$HERE" && "$LEAN" -DautoImplicit=false -DrelaxedAutoImplicit=false "$1" )
}

hunt() {
  compile "$HERE" "$1" -DautoImplicit=false -DrelaxedAutoImplicit=false
}

zeta23() {
  compile "$Z23" "$1" -DrelaxedAutoImplicit=false -Dpp.unicode.fun=true
}

if [ -n "$ONE" ]; then
  mod="${ONE%.lean}"
  hunt "${mod//\//.}"
  exit 0
fi

for m in Zeta23.Defs Zeta23.Defs.Counting Zeta23.Hypotheses Zeta23.Statement \
    Zeta23.Statement.Seam Zeta23.ZetaReflect Zeta23.Statement.SeamClosed; do
  zeta23 "$m"
done
for m in RHHeight.Statement RHHeight.Skeleton RHHeight; do
  hunt "$m"
done
mem_gate
echo "== statements and axioms $(date -u +%H:%M:%S)"
"$LEAN" "$HERE/CheckAxioms.lean"

if [ -n "$ASSEMBLY" ]; then
  for m in Rigor IntervalExp IntervalCExp HardyZ; do
    compile "$TREE_LEAN" "ZetaLean.$m"
  done
  for m in Spine Phase EulerMaclaurin BoxSupport Boxes FirstZero; do
    compile "$FIRST" "HardyFirstZero.$m"
  done
  for m in PhaseShort TenSupport Box2102 Box2501 Box3042 Box3293 Box3758 Box4091 Box4332 \
      Box4800 Box4977 TenZeros; do
    compile "$TEN" "HardyTenZeros.$m"
  done
  hunt RHHeight.Assembly
  mem_gate
  echo "== assembly statements and axioms $(date -u +%H:%M:%S)"
  "$LEAN" "$HERE/CheckAssembly.lean"
fi

if [ -n "$FULL" ]; then
  # gamma_increment: the vertical Stirling bound and what it rests on
  for m in GammaFacts GammaFacts.Series Analytic.Stirling GammaFacts.Mu \
      GammaFacts.StirlingVert; do
    zeta23 "Zeta23.$m"
  done
  hunt RHHeight.GammaIncrement
  check RHHeight/CheckGammaIncrement.lean
  # horizontal_legs: the segment lemma, three generated leg files, the corner boxes
  for m in LegSupport LegsBottom LegsTop1 LegsTop2 LegsArg HorizontalLegs; do
    hunt "RHHeight.$m"
  done
  check RHHeight/CheckHorizontalLegs.lean
  # exact_argument: the rest of the import closure of Zeta23.RvM.MainTerm, in import order
  for m in RvM.Defs Prelude.InstancePriorities FromPNTPlus.StrongPNTPrefix \
      FromPNTPlus.Auxiliary FromPNTPlus.Sobolev FromPNTPlus.Fourier \
      FromPNTPlus.Mathlib.Analysis.SpecialFunctions.Log.Basic FromPNTPlus.Rectangle \
      FromPNTPlus.Tactic.AdditiveCombination FromPNTPlus.ResidueCalcOnRectangles \
      FromPNTPlus.EulerMaclaurin FromPNTPlus.ZetaBounds RvM.ZetaGrowth RvM.Halving \
      RvM.LocalCount WeilEF.XiLogDeriv Analytic.RectangleLogDeriv RvM.GammaSide \
      RvM.BacklundDefs RvM.ReZeroCount RvM.Backlund RvM.CountByIntegral \
      FromPNTPlus.ZetaConj RvM.Fold RvM.NcountWindow RvM.MainTerm; do
    zeta23 "Zeta23.$m"
  done
  hunt RHHeight.ExactArgument
  check RHHeight/CheckExactArgument.lean
  # low_height: hunt #132's Euler-Maclaurin representation only (built in the assembly stage)
  hunt RHHeight.LowHeight
  check RHHeight/CheckLowHeight.lean
  # the theorem
  hunt RHHeight.Main
  mem_gate
  echo "== the theorem: statements and axioms $(date -u +%H:%M:%S)"
  "$LEAN" "$HERE/CheckMain.lean"
fi
echo "== done $(date -u +%H:%M:%S)"
