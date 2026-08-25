#!/usr/bin/env bash
# Stage a Palomar submission: verify everything checkable, then print the exact
# values to paste. Run it immediately before submitting.
#
#   bash scripts/palomar_stage.sh                       # V2 bridge, the default
#   bash scripts/palomar_stage.sh lean/comparator.json  # any registered surface
#
# It refuses rather than warns. If it prints values, every mechanical
# precondition held at the commit you are on; what it cannot see is whether a
# submission is already in progress at Palomar, which is one per repository and
# visible only through the owner's access link. That check is the last line.
set -uo pipefail
cd "$(dirname "$0")/.."

CMP="${1:-lean/bridge/comparator-v2.json}"
PY="${PYTHON:-.venv/bin/python}"
[ -x "$PY" ] || PY=python3

red() { printf '\033[31m%s\033[0m\n' "$*"; }
grn() { printf '\033[32m%s\033[0m\n' "$*"; }

fail=0
note() { printf '  %-58s %s\n' "$1" "$2"; }

echo
echo "Staging a Palomar submission for $CMP"
echo "────────────────────────────────────────────────────────────────────────"

# 1. The tree must be clean and pushed: Palomar fetches a public commit, so
#    anything uncommitted or unpushed is simply not what gets verified.
if [ -n "$(git status --porcelain)" ]; then
  note "working tree" "$(red 'DIRTY — Palomar fetches the pushed commit')"; fail=1
else
  note "working tree" "$(grn clean)"
fi

COMMIT=$(git rev-parse HEAD)
BRANCH=$(git rev-parse --abbrev-ref HEAD)
git fetch -q origin 2>/dev/null || true
if git merge-base --is-ancestor "$COMMIT" origin/main 2>/dev/null; then
  note "commit on origin/main" "$(grn yes)"
else
  note "commit on origin/main" "$(red 'NO — push before submitting')"; fail=1
fi

# 2. The verified tree. lean/bridge has been identical since 8bd9bb04, whose
#    mechanical verification passed on both kernels. If this hash changes, that
#    inheritance is broken and the surface needs its own build again.
VERIFIED_BRIDGE_TREE=858418471411ab49f26e463968eeb67ab6b92b00
if [ "$CMP" = "lean/bridge/comparator-v2.json" ]; then
  got=$(git rev-parse "HEAD:lean/bridge" 2>/dev/null || echo missing)
  if [ "$got" = "$VERIFIED_BRIDGE_TREE" ]; then
    note "lean/bridge tree" "$(grn 'identical to the kernel-verified tree')"
  else
    note "lean/bridge tree" "$(red "CHANGED  $got")"
    echo "      The surface no longer matches what Palomar verified on 2026-08-24."
    echo "      It needs a fresh whole-package build before submission."
    fail=1
  fi
fi

# 3. The correspondence guard. This is the check that would have caught the
#    2026-08-25 refusal, and it derives the metadata path instead of trusting a
#    form default.
out=$("$PY" scripts/palomar_precheck.py . "$CMP" 2>&1)
if printf '%s' "$out" | grep -q "0 FAIL"; then
  note "precheck" "$(grn "$(printf '%s' "$out" | grep -o '[0-9]* pass, [0-9]* warn, 0 FAIL')")"
else
  note "precheck" "$(red FAILED)"
  printf '%s\n' "$out" | grep -E "FAIL" | sed 's/^/      /'
  fail=1
fi

META=$("$PY" -c "
import sys; sys.path.insert(0,'scripts')
import palomar_correspondence as c; print(c.resolve('$CMP','.'))" 2>/dev/null)
PROJ=$("$PY" -c "
import sys; sys.path.insert(0,'scripts')
import palomar_correspondence as c; print(c.resolve_project('$CMP','.'))" 2>/dev/null)

echo "────────────────────────────────────────────────────────────────────────"
if [ "$fail" -ne 0 ]; then
  red "NOT READY. Fix the red lines above; nothing below would be valid."
  exit 1
fi

grn "Ready. Paste these four values; do not pick any of them from a dropdown."
echo
echo "  repository           teal-sea/zeta-lab"
echo "  commit               $COMMIT"
echo "  project directory    $PROJ"
echo "  comparator           $CMP"
echo "  metadata             $META"
echo
echo "  Existing Palomar ID  leave BLANK — V1 never registered, so this is the"
echo "                       initial registration, not a new version."
echo
echo "The metadata field is the one that gets this refused. The form's default"
echo "resolves to lean/bridge/formalization.yaml (V1) and there is a lookalike"
echo "at lean/bridge/formalization-v2.yaml. Neither is the path above."
echo
echo "Last check, and only you can make it: Palomar permits ONE submission in"
echo "progress per repository. Confirm none is open before you submit."
echo
