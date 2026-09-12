#!/usr/bin/env bash
# The check for the root question. A question is a task with two finishes: the true side is the
# declaration itself (a certificate above the record), the false side is `<decl>_ceiling` (every
# certificate in the strip class stays at or below Theorem D). Either one, sorry-free on the three
# permitted axioms, is done; the attempt's handback says which with `answer: true|false`.
#
#   check-question.sh <fully.qualified.decl>    from the repo root of a fresh checkout
#
# Prints ANSWER_SIDE: true|false on success so a reader of the check output can compare it with
# what the attempt claimed. The check does not read the handback; the judge and the operator do.
set -uo pipefail
DECL="${1:?usage: check-question.sh <fully.qualified.decl>}"
HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
if bash "$HERE/check-lean.sh" "$DECL"; then echo "ANSWER_SIDE: true"; exit 0; fi
echo "== the true side did not pass; trying the ceiling"
if bash "$HERE/check-lean.sh" "${DECL}_ceiling"; then echo "ANSWER_SIDE: false"; exit 0; fi
echo "CHECK FAIL: neither $DECL nor ${DECL}_ceiling passes" >&2
exit 1
