#!/usr/bin/env bash
# build_volume.sh <directory> <modules it will hold> [limit]
#
# Where a runner keeps restored build outputs.
#
# Up to `limit` modules (default 90,000, about 47 GB) they go in a plain
# directory on the runner's disk. Above that they need the compressed
# volume: a btrfs image with zstd, mounted through a loop device.
#
# The compressed volume is not free. Round 13 measured it: every lean process
# maps 8 to 10 GB of .olean files, the loop device keeps the image's
# compressed blocks in the page cache beside btrfs's decompressed pages, and
# with three compiles at once one runner took 12.5 million major page faults
# in an hour and built 227 modules. So it is used only when the outputs would
# not fit otherwise, and then the loop device is asked for direct I/O, which
# keeps the compressed copy out of the cache; if that is refused the mount
# falls back to the buffered loop device used until now.
#
# Prints one line saying what it did.
set -euo pipefail

if [ "$#" -lt 2 ]; then
  echo "usage: build_volume.sh <directory> <modules> [limit]" >&2
  exit 2
fi
dir="$1"
modules="$2"
limit="${3:-90000}"
case "$modules$limit" in
  *[!0-9]*) echo "build_volume: modules and limit must be numbers, got '$modules' and '$limit'" >&2; exit 2 ;;
esac

mkdir -p "$dir"
if [ "$modules" -le "$limit" ]; then
  echo "volume: plain directory, $modules modules (compressed above $limit)"
  exit 0
fi

sudo apt-get install -y -q btrfs-progs >/dev/null
img=/mnt/alpoge-build.img
if ! sudo test -d /mnt; then img="$HOME/alpoge-build.img"; fi
sudo truncate -s 600G "$img"
sudo mkfs.btrfs -q "$img"
dev=""
if dev=$(sudo losetup --find --show --direct-io=on "$img" 2>/dev/null) && [ -n "$dev" ] \
    && sudo mount -o compress-force=zstd:3,noatime "$dev" "$dir" 2>/dev/null; then
  dio=$(sudo losetup --list --noheadings --output DIO "$dev" 2>/dev/null | tr -d ' ' || true)
  echo "volume: btrfs with zstd on $dev for $modules modules, direct I/O flag ${dio:-unknown}"
else
  if [ -n "$dev" ]; then sudo losetup -d "$dev" 2>/dev/null || true; fi
  sudo mount -o loop,compress-force=zstd:3,noatime "$img" "$dir"
  echo "volume: btrfs with zstd on a buffered loop device for $modules modules"
fi
sudo chown -R "$(id -u):$(id -g)" "$dir"
