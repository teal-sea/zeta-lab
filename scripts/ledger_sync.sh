#!/usr/bin/env bash
# Sync the private discovery ledger between machines.
#
# The ledger (conjectures/ledger.jsonl, conjectures/ledger.runs.jsonl) is a
# notebook of unreviewed leads and must never enter the public zeta-lab repo
# -- see discovery/README.md, "The ledger is private". It is instead kept in a
# separate PRIVATE repository, cloned in place at conjectures/. The public repo
# ignores conjectures/*, so it never sees that clone or its data.
#
#   scripts/ledger_sync.sh init   # first run on a new machine: clone it in place
#   scripts/ledger_sync.sh pull   # fetch the other machine's records
#   scripts/ledger_sync.sh push   # publish this machine's records
#   scripts/ledger_sync.sh sync   # pull, then push
#
# The record files are append-only JSONL and carry `merge=union`, so two
# machines that both ran the funnel merge without conflict; this script then
# drops any exactly-duplicated lines that a union merge left behind.

set -euo pipefail

REMOTE="https://github.com/teal-sea/zeta-conjectures.git"
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEDGER="$ROOT/conjectures"

die() { printf 'ledger_sync: %s\n' "$1" >&2; exit 1; }

# Union merges concatenate both sides verbatim, which can repeat a line that
# both machines already had. Records are unique by id, so exact-duplicate lines
# are always redundant; drop them while preserving first-seen order.
dedup() {
    local f
    for f in "$LEDGER"/*.jsonl; do
        [ -e "$f" ] || continue
        awk '!seen[$0]++' "$f" > "$f.tmp" && mv "$f.tmp" "$f"
    done
}

require_clone() {
    [ -d "$LEDGER/.git" ] || die "no ledger clone at $LEDGER -- run 'ledger_sync.sh init' first"
}

case "${1:-sync}" in
init)
    if [ -d "$LEDGER/.git" ]; then
        echo "ledger clone already present at $LEDGER"; exit 0
    fi
    mkdir -p "$LEDGER"
    # Clone in place: the directory already exists (.gitkeep is tracked by the
    # public repo), so fetch into a fresh repo rather than `git clone <dir>`.
    git -C "$LEDGER" init -q -b main
    printf '.gitkeep\n' > "$LEDGER/.git/info/exclude"
    git -C "$LEDGER" remote add origin "$REMOTE"
    git -C "$LEDGER" fetch -q origin main
    git -C "$LEDGER" checkout -q -B main --track origin/main
    echo "ledger cloned into $LEDGER"
    ;;
pull)
    require_clone
    git -C "$LEDGER" pull -q --no-rebase origin main
    dedup
    echo "ledger pulled ($(wc -l < "$LEDGER/ledger.jsonl" | tr -d ' ') candidate records)"
    ;;
push)
    require_clone
    dedup
    if [ -z "$(git -C "$LEDGER" status --porcelain)" ]; then
        echo "ledger unchanged, nothing to push"; exit 0
    fi
    git -C "$LEDGER" add -A
    git -C "$LEDGER" commit -q -m "Ledger update from $(hostname -s)"
    git -C "$LEDGER" push -q origin main
    echo "ledger pushed"
    ;;
sync)
    "$0" pull
    "$0" push
    ;;
*)
    die "unknown command '${1}' (expected init, pull, push or sync)"
    ;;
esac
