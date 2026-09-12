#!/usr/bin/env bash
# Fetch the Zenodo archive this hunt reproduces into a gitignored directory
# outside hunts/, verify its sha256, unpack it, and print the path to export
# as BLOCH_SRC for the Modal scripts.
#   source <(hunts/bloch_ceiling/fetch_upstream.sh)
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
DEST="${HERE}/../../.upstream/bloch"          # repo root, gitignored (.upstream/)
ZIP="bloch-computations-1.0.0.zip"
URL="https://zenodo.org/records/21975862/files/${ZIP}?download=1"
SHA="bdaa1ff347043a00733ca40d5db46c5418810d1f4e5c472d0bcb9de48ef408e7"
mkdir -p "${DEST}"
if [ ! -f "${DEST}/${ZIP}" ]; then
  curl -sL -o "${DEST}/${ZIP}" "${URL}"
fi
echo "${SHA}  ${DEST}/${ZIP}" | shasum -a 256 -c - >&2
if [ ! -d "${DEST}/zenodo-bloch-computations/src" ]; then
  (cd "${DEST}" && unzip -q -o "${ZIP}")
fi
(cd "${DEST}/zenodo-bloch-computations" && shasum -a 256 -c CHECKSUMS.sha256 >/dev/null) && echo "CHECKSUMS.sha256: 28 files OK" >&2
echo "export BLOCH_SRC=${DEST}/zenodo-bloch-computations/src"
