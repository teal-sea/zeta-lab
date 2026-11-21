#!/usr/bin/env bash
# restore_chunks.sh <shard.json> <destination>
#
# Restore the build outputs a shard needs. The shard's "fetch" map names, per
# bundle artifact, the chunk members to unpack: {"<artifact id>": ["chunk-r3-s7.tar.zst", ...]}.
# Several bundles are downloaded at once (fetch_artifact.sh: time limit and
# retries), and of each bundle several members are unpacked at once. Done one
# after the other this took up to half an hour per shard by round 12, on a
# runner with four hardware threads, three of them idle.
#
# With RESTORE_NEED set to a file of module names, only the outputs of those
# modules are unpacked (untar_needed.py): a shard needs a fraction of what
# the chunks hold. RESTORE_SUFFIX narrows that to one kind of file, .olean
# for the replay. Without RESTORE_NEED everything is unpacked with tar.
#
# Environment: GITHUB_REPOSITORY and GH_TOKEN as on a runner.
#   RESTORE_BUNDLES  bundles in flight at once (default 3)
#   RESTORE_JOBS     members unpacked at once, per bundle (default 2)
#   RESTORE_NEED     file of module names, one per line (optional)
#   RESTORE_SUFFIX   with RESTORE_NEED: keep only members with this suffix
# Prints one line: bundles, chunks, seconds, and with RESTORE_NEED the files
# kept and skipped.
set -euo pipefail

if [ "$#" -ne 2 ]; then
  echo "usage: restore_chunks.sh <shard.json> <destination>" >&2
  exit 2
fi
export R_SHARD="$1"
export R_DEST="$2"
R_HERE="$(cd "$(dirname "$0")" && pwd)"
export R_HERE
export R_JOBS="${RESTORE_JOBS:-2}"
export R_NEED="${RESTORE_NEED:-}"
export R_SUFFIX="${RESTORE_SUFFIX:-}"
R_WORK="$(mktemp -d)"
export R_WORK
trap 'rm -rf "$R_WORK"' EXIT
mkdir -p "$R_WORK/log"

# One member of one bundle: zip member -> zstd -> files.
unpack_member() {
  set -euo pipefail
  local zip="$1" member="$2"
  if [ -n "$R_NEED" ]; then
    local filter=()
    if [ -n "$R_SUFFIX" ]; then filter=(--suffix "$R_SUFFIX"); fi
    unzip -p "$zip" "$member" | zstd -dc \
      | python3 "$R_HERE/untar_needed.py" "$R_DEST" "$R_NEED" "${filter[@]}" 2> "$R_WORK/log/$member.log"
  else
    unzip -p "$zip" "$member" | zstd -dc | tar -x -f - -C "$R_DEST" 2> "$R_WORK/log/$member.log"
  fi
}
export -f unpack_member

# One bundle: download, unpack its listed members, delete.
restore_bundle() {
  set -euo pipefail
  local id="$1"
  local zip="$R_WORK/bundle-$id.zip"
  bash "$R_HERE/fetch_artifact.sh" "$id" "$zip"
  jq -r --arg id "$id" '.fetch[$id][]' "$R_SHARD" > "$R_WORK/members-$id.txt"
  # One failed member fails the bundle: xargs returns 123.
  xargs -a "$R_WORK/members-$id.txt" -P "$R_JOBS" -I{} bash -c 'unpack_member "$1" "$2"' _ "$zip" {}
  rm -f "$zip"
}
export -f restore_bundle

start=$(date +%s)
jq -r '.fetch | keys[]' "$R_SHARD" > "$R_WORK/bundles.txt"
# One failed bundle fails the restore, and the logs of what failed are shown.
if ! xargs -a "$R_WORK/bundles.txt" -P "${RESTORE_BUNDLES:-3}" -I{} bash -c 'restore_bundle "$1"' _ {}; then
  cat "$R_WORK"/log/*.log >&2 2>/dev/null || true
  echo "restore_chunks: a bundle or one of its members could not be restored" >&2
  exit 1
fi
bundles=$(wc -l < "$R_WORK/bundles.txt")
members=$(cat "$R_WORK"/members-*.txt 2>/dev/null | wc -l)
files=""
if [ -n "$R_NEED" ]; then
  files=", $(cat "$R_WORK"/log/*.log 2>/dev/null | awk '/untar_needed: kept/ {k += $3; s += $5} END {printf "files kept %d, skipped %d", k, s}')"
fi
echo "restore: $bundles bundles, $members chunks, wall_seconds=$(( $(date +%s) - start )), ${RESTORE_BUNDLES:-3} bundles and $R_JOBS members at once$files"
