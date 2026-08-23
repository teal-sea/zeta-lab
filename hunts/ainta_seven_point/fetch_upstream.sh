#!/usr/bin/env bash
# Fetch the upstream verifier at the pinned commit this hunt reproduced, into a
# gitignored directory, and print the path to export as ZSZ_SRC for the Modal scripts.
#   source <(hunts/ainta_seven_point/fetch_upstream.sh)
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
DEST="${HERE}/../../.upstream/zeta-simple-zeros"   # repo root, gitignored, outside hunts/
PIN="040c5e899e658aed7b56a2a87f501798fe10761d"
if [ ! -d "${DEST}/.git" ]; then
  git clone --quiet https://github.com/ainta/zeta-simple-zeros.git "${DEST}"
fi
git -C "${DEST}" checkout --quiet "${PIN}"
echo "export ZSZ_SRC=${DEST}/src/zeta_simple_zeros"
