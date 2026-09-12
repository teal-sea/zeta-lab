#!/usr/bin/env bash
# The check for one Lean declaration on the outband certificate board: a lemma, a definition,
# or one side of the root question. The runner fills the name in from the item's claim, so this
# judges the exact thing the claim names, not whatever the attempt happened to touch.
#
#   check-lean.sh <fully.qualified.decl>    judges the current directory: the repo root of a
#                                           fresh checkout of the attempt's branch
#
# Four things, and the last is the one that matters:
#   1. the attempt added or changed a module under lean/bridge/Zeta23Ext/Outband/ against the
#      graph's trunk (it did work)
#   2. every module it touched builds in the bridge package, with the prebuilt Mathlib and
#      Zeta23 stores symlinked in the way lean/bridge/assemble.sh does it
#   3. no literal `sorry` on any line the attempt added
#   4. `#print axioms <decl>` reports ONLY propext, Classical.choice, Quot.sound. A proof can be
#      textually sorry-free and rest on a sorried lemma; sorryAx propagates and the kernel says so.
#
# Adapted from lean-eval-board/check-task.sh (2026-09-03..05), which found every defect below
# the hard way: bare-directory pathspecs, namespaces the mapper did not write, wrapped axiom
# lists, and a case-sensitive grep for "unknown constant".
set -uo pipefail
[ -d lean/bridge ] || { echo "CHECK FAIL: run from the zeta-lab repo root, no lean/bridge here" >&2; exit 3; }
DECL="${1:?usage: check-lean.sh <fully.qualified.decl>}"
ALLOWED='propext|Classical.choice|Quot.sound'
fail() { echo "CHECK FAIL: $*" >&2; exit 1; }
export PATH="$HOME/.elan/bin:$PATH"

BASE=$(git merge-base HEAD "${OSTOYAE_TRUNK:-HEAD~1}" 2>/dev/null || git rev-parse HEAD~1)
CHANGED=$(git diff --name-only "$BASE" HEAD -- 'lean/bridge/Zeta23Ext/Outband/*' 'lean/bridge/Zeta23Ext/Outband.lean' | grep '\.lean$' || true)
[ -n "$CHANGED" ] || fail "$DECL: the attempt changed nothing under lean/bridge/Zeta23Ext/Outband against ${OSTOYAE_TRUNK:-the trunk}"
echo "== changed: $(echo "$CHANGED" | tr '\n' ' ')"

# The prebuilt stores, found the way assemble.sh finds them: this checkout first, then the
# primary checkout through the common git dir, because a worktree carries no .lake of its own.
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
MATHLIB_STORE=$(find_store "lean/.lake/packages") || { echo "CHECK FAIL: no prebuilt Mathlib store found" >&2; exit 2; }
Z23_STORE=$(find_store "hunts/frontier_math/zeta23ext/.lake/packages") || { echo "CHECK FAIL: no Zeta23 store found" >&2; exit 2; }
mkdir -p lean/bridge/.lake/packages
for p in mathlib batteries aesop Qq proofwidgets plausible importGraph LeanSearchClient Cli; do
  [ -d "$MATHLIB_STORE/$p" ] && ln -sfn "$MATHLIB_STORE/$p" "lean/bridge/.lake/packages/$p"
done
[ -e lean/bridge/.lake/packages/Zeta23 ] || ln -sfn "$Z23_STORE/Zeta23" lean/bridge/.lake/packages/Zeta23

MODS=$(echo "$CHANGED" | sed 's|^lean/bridge/||; s|\.lean$||' | tr / .)
echo "== building in lean/bridge: $(echo "$MODS" | tr '\n' ' ')"
# shellcheck disable=SC2086
( cd lean/bridge && timeout 3600 lake build $MODS 2>&1 | tail -30; exit "${PIPESTATUS[0]}" ) || fail "lake build did not succeed for the changed modules"

echo "== literal sorry scan of the lines the attempt added"
# shellcheck disable=SC2086
ADDED_SORRY=$(git diff "$BASE" HEAD -- $CHANGED | grep '^+' | grep -v '^+++' | grep -nE '(^|[^[:alnum:]_])sorry([^[:alnum:]_]|$)' || true)
if [ -n "$ADDED_SORRY" ]; then echo "$ADDED_SORRY"; fail "the attempt added a literal sorry"; fi

echo "== axiom audit of $DECL"
AX="lean/bridge/.check_axioms_decl.lean"
# The task's decl is what a mapper proposed; the name Lean elaborates is the decl prefixed by
# whatever `namespace` the attempt wrote it in. Try the decl itself, then under each namespace
# the changed files open, longest first. Whichever resolves goes through the identical audit.
NSPACES=$(grep -hE '^namespace[[:space:]]+[A-Za-z0-9_.]+' $CHANGED 2>/dev/null | sed -E 's/^namespace[[:space:]]+([A-Za-z0-9_.]+).*/\1/' | sort -u)
CANDS="$DECL"
for ns in $NSPACES; do CANDS="$CANDS $ns.$DECL"; done
OUT=""; TARGET=""
for cand in $CANDS; do
  { for m in $MODS; do echo "import $m"; done; echo "#print axioms $cand"; } > "$AX"
  TRY=$( cd lean/bridge && lake env lean "$(basename "$AX")" 2>&1 )
  if ! echo "$TRY" | grep -qi "unknown constant\|unknown identifier"; then OUT="$TRY"; TARGET="$cand"; break; fi
done
rm -f "$AX"
[ -n "$TARGET" ] || fail "$DECL resolves to nothing in the changed modules (tried: $CANDS)"
[ "$TARGET" = "$DECL" ] || echo "== $DECL elaborates as $TARGET (namespace of the file it was written in)"
echo "$OUT"
echo "$OUT" | grep -qi '^.*error' && fail "$DECL: audit did not run cleanly"
echo "$OUT" | grep -q 'sorryAx' && fail "$TARGET depends on sorryAx, the proof is hollow"
# Flatten before extracting: Lean wraps the list at about 120 columns, and a regex that needs
# `[` and `]` on one line passed a proof resting on a planted axiom on 2026-09-04. Fails closed:
# a marker with no parseable list is a failure, not a pass.
FLAT=$(echo "$OUT" | tr '\n' ' ' | tr -s ' ')
if echo "$FLAT" | grep -q 'depends on axioms'; then
  LIST=$(echo "$FLAT" | sed -nE 's/.*depends on axioms: \[([^]]*)\].*/\1/p')
  [ -n "$LIST" ] || fail "$TARGET: axiom list present but unparseable: $FLAT"
  EXTRA=$(echo "$LIST" | tr ',' '\n' | tr -d ' ' | grep -vE "^($ALLOWED)$" || true)
  [ -z "$EXTRA" ] || fail "$TARGET rests on axioms outside the permitted three: $(echo "$EXTRA" | tr '\n' ' ')"
elif echo "$FLAT" | grep -q "does not depend on any axioms"; then
  :
else
  fail "$TARGET: no axiom report found in the audit output"
fi
echo "CHECK PASS: $TARGET builds sorry-free on axioms [$ALLOWED] only"
