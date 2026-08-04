#!/usr/bin/env bash
# Sync the private discovery ledger between machines.
#
# The ledger (conjectures/ledger.jsonl, conjectures/ledger.runs.jsonl) is a
# notebook of unreviewed leads and must never enter the public zeta-lab repo
# -- see discovery/README.md, "The ledger is private". It is instead kept in a
# separate PRIVATE repository, cloned in place at conjectures/. The public repo
# ignores conjectures/*, so it never sees that clone or its data.
#
#   scripts/ledger_sync.sh init     # first run on a new machine: clone it in place
#   scripts/ledger_sync.sh status   # what is wired up, and is this machine authorised
#   scripts/ledger_sync.sh pull     # fetch the other machine's records
#   scripts/ledger_sync.sh push     # publish this machine's records
#   scripts/ledger_sync.sh sync     # pull, then push
#
# The remote is PRIVATE: a machine that is not authenticated to GitHub as its
# owner cannot init. Run `status` first on a new machine -- it says so plainly.
#
# The record files are append-only JSONL and carry `merge=union`, so two
# machines that both ran the funnel merge without conflict; this script then
# drops any exactly-duplicated lines that a union merge left behind.

set -euo pipefail

# Overridable so the merge behaviour can be tested against a throwaway remote.
REMOTE="${ZETA_LEDGER_REMOTE:-https://github.com/teal-sea/zeta-conjectures.git}"
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

# A clone counts as usable only once it has main -- a bare `git init` that never
# reached the remote leaves a .git that would otherwise look like success.
is_clone() {
    [ -d "$LEDGER/.git" ] && git -C "$LEDGER" rev-parse --verify -q main >/dev/null 2>&1
}

require_clone() {
    if [ -d "$LEDGER/.git" ] && ! is_clone; then
        die "half-initialised clone at $LEDGER (a previous init failed) -- rerun 'ledger_sync.sh init'"
    fi
    is_clone || die "no ledger clone at $LEDGER -- run 'ledger_sync.sh init' first"
}

auth_hint() {
    cat >&2 <<HINT
ledger_sync: could not reach $REMOTE

That repository is PRIVATE, so this machine has to be authenticated to GitHub
as the account that owns it. Check with:

    gh auth status          # then, if needed: gh auth login
    gh auth setup-git       # let git reuse the gh credential over https

HINT
}

case "${1:-sync}" in
init)
    if is_clone; then
        echo "ledger clone already present at $LEDGER"; exit 0
    fi
    # A previous failed init leaves a .git with no main; start clean rather than
    # reporting success over an empty directory.
    rm -rf "$LEDGER/.git"
    mkdir -p "$LEDGER"

    # A machine that ran the funnel before it was ever synced has records here
    # that exist nowhere else. Checking the remote out over them would either
    # abort on the untracked files or destroy them, so set them aside first and
    # merge them back in below -- init must never lose a record.
    keep="$(mktemp -d)"
    had_local=0
    for f in "$LEDGER"/*.jsonl; do
        [ -e "$f" ] || continue
        mv "$f" "$keep/"
        had_local=1
    done

    # Clone in place: the directory already exists (.gitkeep is tracked by the
    # public repo), so fetch into a fresh repo rather than `git clone <dir>`.
    git -C "$LEDGER" init -q -b main
    printf '.gitkeep\n' > "$LEDGER/.git/info/exclude"
    git -C "$LEDGER" remote add origin "$REMOTE"
    if ! git -C "$LEDGER" fetch -q origin main; then
        rm -rf "$LEDGER/.git"          # leave no half-repo behind
        for f in "$keep"/*.jsonl; do   # and put the local records back
            [ -e "$f" ] || continue
            mv "$f" "$LEDGER/"
        done
        rmdir "$keep" 2>/dev/null || true
        auth_hint
        exit 1
    fi
    git -C "$LEDGER" checkout -q -B main --track origin/main

    if [ "$had_local" = 1 ]; then
        # Same rule as a union merge: concatenate, then drop exact duplicates.
        for f in "$keep"/*.jsonl; do
            [ -e "$f" ] || continue
            cat "$f" >> "$LEDGER/$(basename "$f")"
        done
        dedup
        if [ -n "$(git -C "$LEDGER" status --porcelain)" ]; then
            git -C "$LEDGER" add -A
            git -C "$LEDGER" commit -q -m "Merge pre-existing local ledger from $(hostname -s)"
            git -C "$LEDGER" push -q origin main
            echo "merged this machine's pre-existing records into the shared ledger"
        fi
        echo "a copy of the pre-merge local files is in $keep"
    else
        rmdir "$keep" 2>/dev/null || true
    fi
    echo "ledger cloned into $LEDGER ($(wc -l < "$LEDGER/ledger.jsonl" | tr -d ' ') candidate records)"
    ;;
status)
    echo "remote:  $REMOTE"
    echo "path:    $LEDGER"
    if is_clone; then
        echo "clone:   ok"
        echo "records: $(wc -l < "$LEDGER/ledger.jsonl" | tr -d ' ') candidates, $(wc -l < "$LEDGER/ledger.runs.jsonl" | tr -d ' ') run records"
        echo "local:   $(git -C "$LEDGER" status --porcelain | wc -l | tr -d ' ') uncommitted change(s)"
    elif [ -d "$LEDGER/.git" ]; then
        echo "clone:   HALF-INITIALISED -- rerun 'ledger_sync.sh init'"
    else
        echo "clone:   absent -- run 'ledger_sync.sh init'"
    fi
    if git ls-remote -q --heads "$REMOTE" >/dev/null 2>&1; then
        echo "access:  ok (authenticated to the private remote)"
    else
        echo "access:  FAILED -- not authenticated; see 'gh auth status'"
    fi
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
    die "unknown command '${1}' (expected init, status, pull, push or sync)"
    ;;
esac
