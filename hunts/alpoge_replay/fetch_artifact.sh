#!/usr/bin/env bash
# fetch_artifact.sh <artifact id> <output zip>
#
# Download one Actions artifact as a zip with `gh api`, under a time limit,
# and try again when the transfer stalls, fails, or leaves a zip that does
# not list. `gh api` has no time limit of its own: on 2026-11-21 one
# transfer stalled and held a replay shard, and with it the whole check
# round, for more than two and a half hours.
#
# Environment: GITHUB_REPOSITORY and GH_TOKEN as on a runner.
#   FETCH_TIMEOUT_S  seconds allowed per attempt (default 900)
#   FETCH_TRIES      attempts (default 4)
#   FETCH_BACKOFF_S  seconds slept after attempt n, times n (default 20)
set -uo pipefail

if [ "$#" -ne 2 ]; then
  echo "usage: fetch_artifact.sh <artifact id> <output zip>" >&2
  exit 2
fi
id="$1"
out="$2"
case "$id" in
  ''|*[!0-9]*) echo "fetch_artifact: artifact id must be a number, got '$id'" >&2; exit 2 ;;
esac
limit="${FETCH_TIMEOUT_S:-900}"
tries="${FETCH_TRIES:-4}"
backoff="${FETCH_BACKOFF_S:-20}"

attempt=1
while [ "$attempt" -le "$tries" ]; do
  rm -f "$out"
  start=$(date +%s)
  timeout --signal=TERM --kill-after=30 "$limit" \
    gh api "repos/$GITHUB_REPOSITORY/actions/artifacts/$id/zip" < /dev/null > "$out"
  rc=$?
  if [ "$rc" -eq 0 ] && unzip -l "$out" > /dev/null 2>&1; then
    exit 0
  fi
  size=$(stat -c %s "$out" 2>/dev/null || echo 0)
  echo "fetch_artifact: artifact $id, attempt $attempt of $tries failed: exit $rc after $(( $(date +%s) - start )) s, $size bytes" >&2
  sleep $(( attempt * backoff ))
  attempt=$(( attempt + 1 ))
done
rm -f "$out"
echo "fetch_artifact: artifact $id could not be fetched in $tries attempts" >&2
exit 1
