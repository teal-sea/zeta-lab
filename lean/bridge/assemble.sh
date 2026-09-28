#!/bin/bash
# Assemble this package and report whether it builds. ONE command, because a
# step that takes several is a step that gets skipped.
#
# This package exists so that the Palomar submission surface has a project that
# builds AT ITS ROOT: the registry replays the selected project, not a module
# named by hand. `lake build` here builds the development (`Zeta23Ext`), the
# Challenge and the Solution.
#
# It needs no Mathlib compile. The pin here (v4.33.0-rc2, mathlib
# 51e6992efd06) is bit-identical to the one `lean/` already has built, and the
# upstream `Zeta23` dependency is already fetched and built under
# `hunts/frontier_math/zeta23ext`, so both stores are symlinked in rather than
# re-cloned. A cold `lake build` here would cost hours and gigabytes.
#
#   usage: bash lean/bridge/assemble.sh [repo-root]
#
# Exit status is lake's: zero means the package assembles.

set -u

REPO_ROOT="${1:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)}"
PKG="$REPO_ROOT/lean/bridge"

# The prebuilt dependency stores. Build artifacts are gitignored, so in a git
# WORKTREE the local `.lake` directories do not exist and the stores live in
# the primary checkout, find it through the common git dir rather than
# guessing a path, so this works from any worktree.
find_store() {
  # $1 = repository-relative path of a package's `.lake/packages`
  local rel="$1"
  if [ -d "$REPO_ROOT/$rel" ]; then echo "$REPO_ROOT/$rel"; return 0; fi
  local common_dir primary
  common_dir=$(cd "$REPO_ROOT" && git rev-parse --path-format=absolute --git-common-dir 2>/dev/null)
  if [ -n "$common_dir" ]; then
    primary=$(dirname "$common_dir")
    if [ -d "$primary/$rel" ]; then echo "$primary/$rel"; return 0; fi
  fi
  return 1
}

MATHLIB_STORE=$(find_store "lean/.lake/packages") || {
  echo "no prebuilt Mathlib found (looked in this checkout and in the primary one)" >&2
  echo "build it once:  cd lean && lake build" >&2
  exit 2
}
[ -d "$MATHLIB_STORE/mathlib" ] || { echo "no mathlib under $MATHLIB_STORE" >&2; exit 2; }
echo "== mathlib store: $MATHLIB_STORE =="

mkdir -p "$PKG/.lake/packages"
for p in mathlib batteries aesop Qq proofwidgets plausible importGraph LeanSearchClient Cli; do
  [ -d "$MATHLIB_STORE/$p" ] && ln -sfn "$MATHLIB_STORE/$p" "$PKG/.lake/packages/$p"
done

# The upstream formalization. Already fetched and built for the extension
# package; reuse it rather than cloning a second copy.
if [ ! -e "$PKG/.lake/packages/Zeta23" ]; then
  if Z23_STORE=$(find_store "hunts/frontier_math/zeta23ext/.lake/packages") \
     && [ -d "$Z23_STORE/Zeta23" ]; then
    echo "== reusing the upstream Zeta23 clone: $Z23_STORE/Zeta23 =="
    ln -sfn "$Z23_STORE/Zeta23" "$PKG/.lake/packages/Zeta23"
  fi
fi

export PATH="$HOME/.elan/bin:$PATH"
cd "$PKG" || exit 2

if [ ! -e "$PKG/.lake/packages/Zeta23" ]; then
  echo "== fetching the upstream Zeta23 dependency (once) =="
  lake update -R || exit $?
fi

echo "== lake build =="
lake build
status=$?

echo
if [ $status -eq 0 ]; then
  echo "ASSEMBLES: every module in this package builds under $(cat lean-toolchain)"
else
  echo "DOES NOT ASSEMBLE (lake exit $status), do not land Lean on top of this"
fi
exit $status
