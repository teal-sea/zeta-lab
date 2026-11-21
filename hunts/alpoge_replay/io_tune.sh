#!/usr/bin/env bash
# io_tune.sh <read_ahead_kb> <fault_around_bytes> <directory>...
#
# Shrink the two windows the kernel uses on a page fault in a mapped file:
# how much it reads from disk around the page (read_ahead_kb, per filesystem:
# set for the one holding each <directory>) and how much of what is already
# in memory around the page it maps as well (fault_around_bytes, one value
# for the machine). lean maps the .olean of every module under the one it
# compiles and reads a few scattered places in each; with the defaults, 128
# KB and 64 KB, each of those places costs memory for far more than was
# read, and a runner's memory is what a module near the top runs out of.
#
# Prints what was there and what is there now. A file that is missing or
# cannot be written is reported and nothing more: the build runs either way.
#
# Environment (for tests): IO_TUNE_SYS replaces /sys, IO_TUNE_SUDO replaces
# sudo (empty for none).
set -uo pipefail

if [ "$#" -lt 3 ]; then
  echo "usage: io_tune.sh <read_ahead_kb> <fault_around_bytes> <directory>..." >&2
  exit 2
fi
ra="$1"; fa="$2"; shift 2
for n in "$ra" "$fa"; do
  case "$n" in ''|*[!0-9]*) echo "io_tune: both sizes must be numbers" >&2; exit 2;; esac
done
sys="${IO_TUNE_SYS:-/sys}"
sudo="${IO_TUNE_SUDO-sudo}"

put() {  # put <value> <file>: write, and say what changed
  local value="$1" file="$2" before after
  before=$($sudo cat "$file" 2>/dev/null || echo "?")
  printf '%s\n' "$value" | $sudo tee "$file" >/dev/null 2>&1 || true
  after=$($sudo cat "$file" 2>/dev/null || echo "?")
  echo "io_tune: $file $before -> $after"
}

seen=""
for dir in "$@"; do
  # findmnt pads its columns
  fstype=$(findmnt -n -o FSTYPE --target "$dir" 2>/dev/null | tr -d ' ' || true)
  majmin=$(findmnt -n -o MAJ:MIN --target "$dir" 2>/dev/null | tr -d ' ' || true)
  files=()
  if [ "$fstype" = "btrfs" ]; then   # btrfs keeps a device of its own for this
    for f in "$sys"/class/bdi/btrfs-*/read_ahead_kb; do
      if [ -e "$f" ]; then files+=("$f"); fi
    done
  else                               # the device's queue, or the queue of the disk a partition is on
    for f in "$sys/dev/block/$majmin/queue/read_ahead_kb" "$sys/dev/block/$majmin/../queue/read_ahead_kb"; do
      if [ -e "$f" ]; then files+=("$f"); break; fi
    done
  fi
  if [ "${#files[@]}" -eq 0 ]; then
    echo "io_tune: no read_ahead_kb found for $dir ($fstype, device $majmin)"
    continue
  fi
  for f in "${files[@]}"; do
    case " $seen " in *" $f "*) continue;; esac
    seen="$seen $f"
    put "$ra" "$f"
  done
done

fafile="$sys/kernel/debug/fault_around_bytes"
if $sudo test -e "$fafile" 2>/dev/null; then
  put "$fa" "$fafile"
else
  echo "io_tune: no fault_around_bytes (debugfs not mounted?)"
fi
exit 0
