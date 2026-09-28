#!/usr/bin/env bash
# The check for a Python instrument on the outband certificate board. The instrument is judged
# against numbers already on the record, not against tests the attempt wrote for itself.
#
#   check-tool.sh falsify     from the repo root of a fresh checkout of the attempt's branch
#
# For `falsify`: `--control` must reproduce hunt #110 section 2 exactly. The witness
# Q = t[[0,1],[1,0]], S = diag(1,-1), c = 2 has slack +2.0 at t = 1 and -0.5 at t = 1.5 under
# the indefinite-S weakening, and the standard inequality is never violated over 4000 seeded
# random positive semidefinite pairs. A tool that prints anything else, or nothing, fails.
set -uo pipefail
NAME="${1:?usage: check-tool.sh <name>}"
fail() { echo "CHECK FAIL: $*" >&2; exit 1; }
[ -f "hunts/outband_certificate/$NAME.py" ] || fail "hunts/outband_certificate/$NAME.py is not in the checkout"

# The lab's venv lives in the primary checkout; a worktree has none of its own.
common=$(git rev-parse --path-format=absolute --git-common-dir 2>/dev/null) || fail "not a git checkout"
PRIMARY=$(dirname "$common")
PY="$PRIMARY/.venv/bin/python"
[ -x "$PY" ] || PY="$PWD/.venv/bin/python"
[ -x "$PY" ] || { echo "CHECK FAIL: no .venv/bin/python in $PRIMARY or here; cannot tell" >&2; exit 2; }

case "$NAME" in
  falsify)
    OUT=$(timeout 1800 "$PY" "hunts/outband_certificate/$NAME.py" --control 2>&1) || { echo "$OUT"; fail "falsify.py --control exited non-zero"; }
    echo "$OUT"
    echo "$OUT" | grep -qE '^WITNESS t=1\.0+ slack=\+?2\.0+$'  || fail "witness at t=1.0 must print slack=2.0 (hunt #110 section 2)"
    echo "$OUT" | grep -qE '^WITNESS t=1\.5 slack=-0\.50*$'    || fail "witness at t=1.5 must print slack=-0.5 (hunt #110 section 2)"
    RP=$(echo "$OUT" | grep -E '^RANDOM_PSD ' | tail -1)
    [ -n "$RP" ] || fail "no RANDOM_PSD line"
    echo "$RP" | grep -qE 'n=4000 ' || fail "RANDOM_PSD must run 4000 pairs: $RP"
    echo "$RP" | grep -qE 'violations=0( |$)' || fail "the standard inequality must never be violated on PSD pairs: $RP"
    MIN=$(echo "$RP" | sed -nE 's/.*min_slack=([-+0-9.eE]+).*/\1/p')
    [ -n "$MIN" ] || fail "RANDOM_PSD carries no min_slack: $RP"
    awk -v m="$MIN" 'BEGIN { exit !(m > 0) }' || fail "min_slack must be positive: $RP"
    echo "CHECK PASS: falsify reproduces hunt #110 section 2"
    ;;
  *)
    echo "CHECK FAIL: no check is written for tool '$NAME'; cannot tell" >&2; exit 2 ;;
esac
