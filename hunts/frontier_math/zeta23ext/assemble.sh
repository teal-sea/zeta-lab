#!/bin/bash
# Assemble this package and report whether it builds. ONE command, because a
# step that takes several is a step that gets skipped.
#
# Run this BEFORE landing any Lean module into this package, and again after.
# The whole reason it exists: three separate module sets were landed here
# without ever being built (BandCert/, EForm/, PairEnergy.lean), and each time
# the failure was invisible to reading the proofs. `tests/test_zeta23ext_imports.py`
# catches the cheapest of those failure classes in the fast tier; this catches
# the rest.
#
# It needs no Mathlib compile. This package's pin (v4.33.0-rc2, mathlib rev
# 51e6992efd06) is bit-identical to the one `lean/` already has built, so the
# prebuilt packages are symlinked in rather than re-cloned. A cold `lake build`
# here would cost hours and gigabytes; this costs minutes.
#
#   usage: bash hunts/frontier_math/zeta23ext/assemble.sh [repo-root]
#
# Exit status is lake's: zero means the package assembles.

set -u

REPO_ROOT="${1:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)}"
PKG="$REPO_ROOT/hunts/frontier_math/zeta23ext"

# The prebuilt dependency store. `lean/` is the laboratory's own Lean package
# and is what makes this cheap. Build artifacts are gitignored, so in a git
# WORKTREE the local `lean/.lake` does not exist and the store lives in the
# primary checkout, find it through the common git dir rather than guessing a
# path, so this works from any worktree.
STORE="$REPO_ROOT/lean/.lake/packages"
if [ ! -d "$STORE/mathlib" ]; then
  common_dir=$(cd "$REPO_ROOT" && git rev-parse --path-format=absolute --git-common-dir 2>/dev/null)
  if [ -n "$common_dir" ]; then
    primary=$(dirname "$common_dir")
    if [ -d "$primary/lean/.lake/packages/mathlib" ]; then
      STORE="$primary/lean/.lake/packages"
      echo "== using the primary checkout's prebuilt store: $STORE =="
    fi
  fi
fi

if [ ! -d "$STORE/mathlib" ]; then
  echo "no prebuilt Mathlib found (looked in $REPO_ROOT/lean/.lake/packages" >&2
  echo "and in the primary checkout's lean/.lake/packages)" >&2
  echo "build it once:  cd lean && lake build" >&2
  exit 2
fi

mkdir -p "$PKG/.lake/packages"
for p in mathlib batteries aesop Qq proofwidgets plausible importGraph LeanSearchClient Cli; do
  [ -d "$STORE/$p" ] && ln -sfn "$STORE/$p" "$PKG/.lake/packages/$p"
done

export PATH="$HOME/.elan/bin:$PATH"
cd "$PKG" || exit 2

# Zeta23 (the upstream formalization) is a real dependency and is fetched once.
if [ ! -d "$PKG/.lake/packages/Zeta23" ]; then
  echo "== fetching the upstream Zeta23 dependency (once) =="
  lake update -R || exit $?
fi

echo "== lake build =="
lake build
status=$?

echo
if [ $status -eq 0 ]; then
  echo "ASSEMBLES: every module in Zeta23Ext builds under $(cat lean-toolchain)"
else
  echo "DOES NOT ASSEMBLE (lake exit $status), do not land Lean on top of this"
fi
exit $status
