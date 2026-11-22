#!/usr/bin/env bash
# cgroup_cap.sh <high_mb> <pid> [name]
#
# Put process <pid> (the calling shell: pass $$), and so everything it starts
# from then on, in a memory cgroup of its own with memory.high set. Memory
# here means what the kernel charges to the group: the processes' own memory
# and the pages of the files they read or map. Over memory.high the kernel
# takes pages back from the group itself and slows it down; it kills nothing.
#
# Why. A replay process high in the import graph maps a hundred thousand
# .olean files and its working set is larger than the runner's memory, so the
# page cache turns over for the whole of the replay. Without a group of its
# own that turnover is the machine's: every idle process loses its pages to
# it, the runner's own agent among them. From check round 12 on, a quarter to
# a half of the replay shards ended with a runner that had stopped answering
# and left no log (RUNS.md, "The lost runners are not a module"); the shards
# that survived beside them had memory to spare by MemAvailable, which counts
# page cache as available. With the cap the turnover stays inside the group
# and the rest of the machine keeps a few gigabytes to itself. Whether that
# is what was killing runners is a guess this cap tests; it costs nothing
# when it is wrong.
#
# Pages already in the cache when the group is made stay charged to whoever
# read them first, so the caller drops the cache before it starts the work.
#
# It never fails the job: where there is no cgroup v2, no memory controller
# or no permission, it says so and exits 0 with nothing capped.
#
# Environment, for tests: CGROUP_ROOT (default /sys/fs/cgroup), CGROUP_SUDO
# (the prefix for writes, default "sudo"; empty for none).
set -uo pipefail

if [ "$#" -lt 2 ]; then
  echo "usage: cgroup_cap.sh <high_mb> <pid> [name]" >&2
  exit 2
fi
high_mb="$1"
pid="$2"
name="${3:-alpoge-replay}"
root="${CGROUP_ROOT:-/sys/fs/cgroup}"
sudo_cmd="${CGROUP_SUDO-sudo}"

case "$high_mb" in ''|*[!0-9]*) echo "cgroup_cap: high_mb must be a whole number, got '$high_mb'" >&2; exit 2 ;; esac
case "$pid" in ''|*[!0-9]*) echo "cgroup_cap: pid must be a whole number, got '$pid'" >&2; exit 2 ;; esac

put() {  # put <text> <file>: write a kernel setting, through sudo where the runner needs it
  # shellcheck disable=SC2086
  printf '%s\n' "$1" | $sudo_cmd tee "$2" > /dev/null 2>&1
}

if [ ! -f "$root/cgroup.controllers" ]; then
  echo "cgroup_cap: no cgroup v2 at $root; nothing capped"
  exit 0
fi
if ! tr ' ' '\n' < "$root/cgroup.controllers" | grep -qx memory; then
  echo "cgroup_cap: no memory controller at $root; nothing capped"
  exit 0
fi
if ! tr ' ' '\n' < "$root/cgroup.subtree_control" 2>/dev/null | grep -qx memory; then
  put "+memory" "$root/cgroup.subtree_control" || {
    echo "cgroup_cap: could not enable the memory controller for children of $root; nothing capped"
    exit 0
  }
fi
# shellcheck disable=SC2086
$sudo_cmd mkdir -p "$root/$name" 2>/dev/null || {
  echo "cgroup_cap: could not make $root/$name; nothing capped"
  exit 0
}
put "$(( high_mb * 1024 * 1024 ))" "$root/$name/memory.high" || {
  echo "cgroup_cap: could not set memory.high in $root/$name; nothing capped"
  exit 0
}
put "$pid" "$root/$name/cgroup.procs" || {
  echo "cgroup_cap: could not move pid $pid into $root/$name; nothing capped"
  exit 0
}
echo "cgroup_cap: pid $pid is in $name, memory.high $(cat "$root/$name/memory.high" 2>/dev/null || echo '?') bytes"
