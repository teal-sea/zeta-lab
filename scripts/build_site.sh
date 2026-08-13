#!/usr/bin/env bash
# Build the public reading surface for a host, with history the counts need.
#
# `scripts/72_site.py` derives every figure from the tree, and several of them
# come from git: the commit total, the date of the first commit, the elapsed
# span in the headline, and the branches ahead of main. A shallow checkout
# cannot answer any of those. The generator already refuses to guess — it drops
# the count and falls back to a plain headline rather than publishing the clone
# depth as if it were the history — but the honest fallback is still a worse
# page, so this gets the history first where it can.
#
# The host's git integration checks out at depth 10. `--unshallow` is enough on
# some hosts and silently is not on others, so the depth is re-checked rather
# than assumed, and a full clone is the fallback. Both paths end with a tree
# that can answer the questions; the `SRC` indirection exists because the
# generator reads the repository relative to its own file.
set -euo pipefail

git fetch --unshallow --quiet origin 2>/dev/null || true

SRC="."
if [ "$(git rev-parse --is-shallow-repository 2>/dev/null || echo true)" = "true" ]; then
    echo "checkout is shallow after fetch; cloning for full history"
    rm -rf .deep
    git clone --quiet https://github.com/teal-sea/zeta-lab.git .deep
    SRC=".deep"
fi

echo "generating from ${SRC} at $(git -C "$SRC" rev-parse --short HEAD)" \
     "($(git -C "$SRC" rev-list --count HEAD) commits)"

python3 "${SRC}/scripts/72_site.py" --out _site
cp interactive_lab/prime_genesis.html _site/prime_genesis.html

find _site -name '*.html' | sort
