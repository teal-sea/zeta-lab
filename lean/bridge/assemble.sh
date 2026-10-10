#!/bin/bash
# Assemble this package and report whether it builds. ONE command, because a
# step that takes several is a step that gets skipped.
#
# This package exists so that the Palomar submission surface has a project that
# builds AT ITS ROOT: the registry replays the selected project, not a module
# named by hand. `lake build` here builds the development (`Zeta23Ext`), the
# Challenge and the Solution.
#
# It needs no Mathlib compile. The pin here (v4.35.0-rc2, mathlib
# 065356127b1d) is bit-identical to the one `lean/` already has built, so that
# store is symlinked in rather than re-cloned, and the upstream `Zeta23` is
# vendored at `lean/vendor/zeta23` and required by path. A cold `lake build`
# here would cost hours and gigabytes.
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

export PATH="$HOME/.elan/bin:$PATH"
cd "$PKG" || exit 2

# Zeta23 (the upstream formalization) is required by path since the 4.35 port:
# it is vendored at lean/vendor/zeta23 and never appears under .lake/packages,
# so the old "fetch once" step fired on every run, and its `lake update` would
# re-resolve the symlinked store above, which belongs to `lean/`. The same
# step was removed from zeta23ext/assemble.sh in #293.
if [ ! -f "$REPO_ROOT/lean/vendor/zeta23/lakefile.toml" ]; then
  echo "the vendored Zeta23 dependency is missing at lean/vendor/zeta23" >&2
  exit 2
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
