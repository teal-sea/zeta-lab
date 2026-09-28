#!/usr/bin/env bash
# Does this statement elaborate in the bridge package? Run by the runner in the trunk worktree
# before any prover is spawned on the item, with the statement in OSTOYAE_STATEMENT. Not a judge
# of truth: a false statement elaborates fine. It is the compiler's word on whether the words
# are Lean at all, in the vocabulary the bridge actually has (Zeta23Ext and V2Challenge). AXLE
# cannot see those types, so this gate is local.
#
#   gate-lean.sh <decl>      exit 0 = elaborates; 1 = does not, errors on stdout;
#                            2 = cannot tell (no stores, or the bridge does not build here)
set -uo pipefail
DECL="${1:?usage: gate-lean.sh <decl>}"
STMT="${OSTOYAE_STATEMENT:-}"
[ -n "$STMT" ] || { echo "gate: no OSTOYAE_STATEMENT"; exit 2; }
[ -d lean/bridge ] || { echo "gate: cannot tell, no lean/bridge here"; exit 2; }
export PATH="$HOME/.elan/bin:$PATH"

find_store() {
  local rel="$1"
  if [ -d "$PWD/$rel" ]; then echo "$PWD/$rel"; return 0; fi
  local common primary
  common=$(git rev-parse --path-format=absolute --git-common-dir 2>/dev/null)
  if [ -n "$common" ]; then
    primary=$(dirname "$common")
    if [ -d "$primary/$rel" ]; then echo "$primary/$rel"; return 0; fi
  fi
  return 1
}
MATHLIB_STORE=$(find_store "lean/.lake/packages") || { echo "gate: cannot tell, no prebuilt Mathlib store"; exit 2; }
Z23_STORE=$(find_store "hunts/frontier_math/zeta23ext/.lake/packages") || { echo "gate: cannot tell, no Zeta23 store"; exit 2; }
mkdir -p lean/bridge/.lake/packages
for p in mathlib batteries aesop Qq proofwidgets plausible importGraph LeanSearchClient Cli; do
  [ -d "$MATHLIB_STORE/$p" ] && ln -sfn "$MATHLIB_STORE/$p" "lean/bridge/.lake/packages/$p"
done
[ -e lean/bridge/.lake/packages/Zeta23 ] || ln -sfn "$Z23_STORE/Zeta23" lean/bridge/.lake/packages/Zeta23

cd lean/bridge || exit 2
# Built once, cached in the trunk's .lake. The first time is the whole development; after that
# it is seconds. Neither is a prover's time.
timeout 3600 lake build Zeta23Ext V2Challenge >/dev/null 2>&1 || { echo "gate: cannot tell, Zeta23Ext or V2Challenge does not build here"; exit 2; }
D=$(mktemp -d "${TMPDIR:-/tmp}/outband-gate.XXXXXX"); trap 'rm -rf "$D"' EXIT
F="$D/Gate.lean"
{
  echo "import Zeta23Ext"
  echo "import V2Challenge"
  echo "open Zeta23Ext.PalomarV2"
  echo
  printf '%s\n' "$STMT"
} > "$F"
OUT=$(lake env lean "$F" 2>&1)
# `declaration uses 'sorry'` is the statement's own `:= by sorry` and is fine; any other error
# line is a failure to elaborate.
ERR=$(echo "$OUT" | grep -i 'error' | grep -vi "declaration uses 'sorry'" || true)
if [ -z "$ERR" ]; then echo "gate: $DECL elaborates in the bridge"; exit 0; fi
echo "$OUT"
exit 1
