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
# Extra arguments go to tar, e.g. --wildcards '*.olean' for the replay,
# which reads nothing else.
#
# Environment: GITHUB_REPOSITORY and GH_TOKEN as on a runner.
#   RESTORE_JOBS  members unpacked at once (default 3)
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
for id in $(jq -r '.fetch | keys[]' "$shard"); do
  bash "$here/fetch_artifact.sh" "$id" "$work/bundle.zip"
  jq -r --arg id "$id" '.fetch[$id][]' "$shard" > "$work/members.txt"
  # One failed member fails the restore: xargs returns 123 and set -e ends it.
  xargs -a "$work/members.txt" -P "$jobs" -I{} \
    bash -c 'set -euo pipefail; unzip -p "$1" "$2" | zstd -dc | tar -x -f - -C "$3" "${@:4}"' \
    _ "$work/bundle.zip" {} "$dest" "$@"
  members=$(( members + $(wc -l < "$work/members.txt") ))
  bundles=$(( bundles + 1 ))
  rm -f "$work/bundle.zip"
done
echo "restore: $bundles bundles, $members chunks, wall_seconds=$(( $(date +%s) - start )), $jobs at once"
