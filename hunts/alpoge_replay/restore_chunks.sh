#!/usr/bin/env bash
# restore_chunks.sh <shard.json> <destination> [extra tar arguments...]
#
# Restore the build outputs a shard needs. The shard's "fetch" map names, per
# bundle artifact, the chunk members to unpack: {"<artifact id>": ["chunk-r3-s7.tar.zst", ...]}.
# Each bundle is downloaded once (fetch_artifact.sh: time limit and retries)
# and its members are unpacked several at a time. Unpacking one after the
# other took up to half an hour per shard by round 12, on a runner with four
# cores, three of them idle.
#
# With RESTORE_NEED set to a file of module names, only the outputs of those
# modules are unpacked (untar_needed.py): a shard needs a fraction of what
# the chunks hold. RESTORE_SUFFIX narrows that to one kind of file, .olean
# for the replay. Without RESTORE_NEED everything is unpacked with tar, and
# extra arguments go to tar.
#
# Environment: GITHUB_REPOSITORY and GH_TOKEN as on a runner.
#   RESTORE_JOBS    members unpacked at once (default 3)
#   RESTORE_NEED    file of module names, one per line (optional)
#   RESTORE_SUFFIX  with RESTORE_NEED: keep only members with this suffix
# Prints one line: bundles, members, seconds.
set -euo pipefail

if [ "$#" -lt 2 ]; then
  echo "usage: restore_chunks.sh <shard.json> <destination> [tar arguments...]" >&2
  exit 2
fi
shard="$1"
dest="$2"
shift 2
here="$(cd "$(dirname "$0")" && pwd)"
jobs="${RESTORE_JOBS:-3}"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

start=$(date +%s)
bundles=0
members=0
mkdir -p "$work/log"
for id in $(jq -r '.fetch | keys[]' "$shard"); do
  bash "$here/fetch_artifact.sh" "$id" "$work/bundle.zip"
  jq -r --arg id "$id" '.fetch[$id][]' "$shard" > "$work/members.txt"
  # One failed member fails the restore: xargs returns 123 and set -e ends it.
  if [ -n "${RESTORE_NEED:-}" ]; then
    filter=()
    if [ -n "${RESTORE_SUFFIX:-}" ]; then filter=(--suffix "$RESTORE_SUFFIX"); fi
    xargs -a "$work/members.txt" -P "$jobs" -I{} \
      bash -c 'set -euo pipefail; unzip -p "$1" "$2" | zstd -dc | python3 "$3" "$4" "$5" "${@:7}" 2>"$6/$2.log"' \
      _ "$work/bundle.zip" {} "$here/untar_needed.py" "$dest" "$RESTORE_NEED" "$work/log" "${filter[@]}" \
      || { cat "$work"/log/*.log >&2; exit 1; }
  else
    xargs -a "$work/members.txt" -P "$jobs" -I{} \
      bash -c 'set -euo pipefail; unzip -p "$1" "$2" | zstd -dc | tar -x -f - -C "$3" "${@:4}"' \
      _ "$work/bundle.zip" {} "$dest" "$@"
  fi
  members=$(( members + $(wc -l < "$work/members.txt") ))
  bundles=$(( bundles + 1 ))
  rm -f "$work/bundle.zip"
done
files=""
if [ -n "${RESTORE_NEED:-}" ]; then
  files=", $(cat "$work"/log/*.log 2>/dev/null | awk '/untar_needed: kept/ {k += $3; s += $5} END {printf "files kept %d, skipped %d", k, s}')"
fi
echo "restore: $bundles bundles, $members chunks, wall_seconds=$(( $(date +%s) - start )), $jobs at once$files"
