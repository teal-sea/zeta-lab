#!/usr/bin/env python3
"""Planner for the sharded replay of the Alpöge archive (stdlib only).

The archive is one Lake package of 175,187 modules whose final theorem imports
all of them. No hosted runner can build that in one six-hour job, so the build
is cut into rounds. In each round every shard is a set of unbuilt modules that
is closed downward relative to what earlier rounds built: every import of a
module in the shard is either already built or in the same shard. Shards of one
round therefore do not depend on each other and can run on separate runners.

Subcommands
  dag       parse the import graph of the extracted archive into a JSON file
  plan      given the graph and the campaign state, write the next round
  status    print how much is built and how much is left
  simulate  plan round after round under a cost model, to count rounds

Everything here is deterministic: no hashing of unordered sets reaches the
output, so two runs on the same inputs write the same plan.
"""
from __future__ import annotations

import argparse
import json
import os
import sys


# --------------------------------------------------------------------------
# the import graph
# --------------------------------------------------------------------------

def header_imports(txt: str) -> list[str]:
    """Module names imported by a Lean file, read from its header only.

    Lean accepts imports only before the first command, so this walks the
    header and stops at the first token that is not part of an import. A line
    starting with the word import inside a later comment is not an import.
    """
    n = len(txt)
    out: list[str] = []

    def skip(i: int) -> int:
        while i < n:
            c = txt[i]
            if c in " \t\r\n":
                i += 1
            elif txt.startswith("--", i):
                j = txt.find("\n", i)
                i = n if j < 0 else j + 1
            elif txt.startswith("/-", i):
                depth, i = 1, i + 2
                while i < n and depth:
                    if txt.startswith("/-", i):
                        depth, i = depth + 1, i + 2
                    elif txt.startswith("-/", i):
                        depth, i = depth - 1, i + 2
                    else:
                        i += 1
            else:
                break
        return i

    def word(i: int) -> tuple[str, int]:
        j = i
        while j < n and not txt[j].isspace():
            j += 1
        return txt[i:j], j

    i = 0
    while True:
        i = skip(i)
        w, j = word(i)
        if w in ("module", "prelude", "public", "private", "meta"):
            i = j
            continue
        if w == "import":
            i = skip(j)
            w2, j2 = word(i)
            if w2 == "all":
                i = skip(j2)
                w2, j2 = word(i)
            # `import A.«B'»` and `import A.B'` name the same module
            out.append(w2.replace("\u00ab", "").replace("\u00bb", ""))
            i = j2
            continue
        break
    return out


def build_dag(src: str) -> dict:
    mods: dict[str, str] = {}
    for root, dirs, files in os.walk(src):
        dirs.sort()
        for f in sorted(files):
            if f.endswith(".lean"):
                p = os.path.join(root, f)
                mods[os.path.relpath(p, src)[:-5].replace(os.sep, ".")] = p
    deps: dict[str, list[str]] = {}
    size: dict[str, int] = {}
    external: set[str] = set()
    for m in sorted(mods):
        with open(mods[m], "rb") as fh:
            raw = fh.read()
        size[m] = len(raw)
        d = []
        for name in header_imports(raw.decode("utf-8", errors="replace")):
            if name in mods:
                d.append(name)
            else:
                external.add(name.split(".")[0])
        deps[m] = sorted(set(d))
    return {"deps": deps, "size": size, "external_roots": sorted(external)}


def topo_levels(deps: dict[str, list[str]]) -> tuple[list[str], dict[str, int]]:
    """Topological order (imports first) and level = longest chain below."""
    order: list[str] = []
    state: dict[str, int] = {}
    for s in sorted(deps):
        if s in state:
            continue
        stack = [(s, 0)]
        state[s] = 1
        while stack:
            m, i = stack.pop()
            ds = deps[m]
            if i < len(ds):
                stack.append((m, i + 1))
                c = ds[i]
                st = state.get(c)
                if st is None:
                    state[c] = 1
                    stack.append((c, 0))
                elif st == 1:
                    raise SystemExit(f"import cycle through {c} and {m}")
            else:
                state[m] = 2
                order.append(m)
    level: dict[str, int] = {}
    for m in order:
        level[m] = 1 + max((level[d] for d in deps[m]), default=0)
    return order, level


def heights(deps: dict[str, list[str]], order: list[str]) -> dict[str, int]:
    """height = longest chain above a module, up to a module nothing imports."""
    h = {m: 0 for m in order}
    for m in reversed(order):
        hm = h[m] + 1
        for d in deps[m]:
            if h[d] < hm:
                h[d] = hm
    return h


# --------------------------------------------------------------------------
# one round
# --------------------------------------------------------------------------

def plan_round(deps, cost, order, height, done, n_shards, budget, max_modules):
    """Return (shards, deferred_count). Each shard is a list of modules.

    Clusters grow upward from the built frontier. A module joins the cluster
    of its unbuilt imports; if those sit in several clusters the clusters are
    merged, unless the merged cost would pass the per-shard budget, in which
    case the module and everything above it waits for a later round. Clusters
    are then packed into at most n_shards shards, tallest first, so the long
    import chain moves every round.
    """
    parent: dict[str, str] = {}
    load: dict[str, float] = {}
    count: dict[str, int] = {}
    top: dict[str, int] = {}
    deferred: set[str] = set()

    def find(x: str) -> str:
        r = x
        while parent[r] != r:
            r = parent[r]
        while parent[x] != r:
            parent[x], x = r, parent[x]
        return r

    for m in order:
        if m in done:
            continue
        unbuilt = [d for d in deps[m] if d not in done]
        if any(d in deferred for d in unbuilt):
            deferred.add(m)
            continue
        roots = sorted({find(d) for d in unbuilt})
        tot = cost[m] + sum(load[r] for r in roots)
        cnt = 1 + sum(count[r] for r in roots)
        if tot > budget or cnt > max_modules:
            deferred.add(m)
            continue
        parent[m] = m
        for r in roots:
            parent[r] = m
        load[m] = tot
        count[m] = cnt
        top[m] = max([height[m]] + [top[r] for r in roots])

    clusters: dict[str, list[str]] = {}
    for m in order:
        if m in parent:
            clusters.setdefault(find(m), []).append(m)
    # tallest first, then heaviest, then by name for determinism
    reps = sorted(clusters, key=lambda r: (-top[r], -load[r], r))
    bins: list[list[str]] = [[] for _ in range(n_shards)]
    bin_load = [0.0] * n_shards
    bin_count = [0] * n_shards
    left = 0
    for r in reps:
        placed = False
        # least-loaded bin that still fits
        for b in sorted(range(n_shards), key=lambda b: (bin_load[b], b)):
            if bin_load[b] + load[r] <= budget and bin_count[b] + count[r] <= max_modules:
                bins[b].extend(clusters[r])
                bin_load[b] += load[r]
                bin_count[b] += count[r]
                placed = True
                break
        if not placed:
            left += count[r]
    shards = [b for b in bins if b]
    return shards, len(deferred) + left, bin_load


def _bits(x: int):
    """Indices of the set bits of x, lowest first."""
    while x:
        low = x & -x
        yield low.bit_length() - 1
        x ^= low


def fill_idle(deps, cost, order, done, shards, n_shards: int, budget: float):
    """A second pass over a round's plan: use the capacity the first pass left idle.

    The cluster pass never builds a module twice, so a module whose unbuilt
    imports ended up in different shards waits for the next round. Early in
    the campaign that costs nothing, every shard is full. Late, the unbuilt
    part is one tangle joined near the top: a round then fills two or three
    shards and leaves the rest idle, although almost every module left would
    fit a shard together with all it still needs (measured on this archive
    after round 11: with shards of four compiles for an hour, five rounds
    would do where the cluster pass alone takes seven).

    This pass walks the modules not yet planned, in topological order, and
    gives each to the shard that lacks the fewest of its unbuilt imports, if
    that shard has room for the lacking part. What it lacks is built there
    too, although another shard already builds it: an "extra". A shard stays
    closed downward, which is the property that makes shards independent.

    Returns (owned, extra, loads). owned[i]: the modules shard i is first to
    build; it packs and reports those. extra[i]: modules it builds only to
    reach its own, owned by another shard of the same round.
    """
    unbuilt = [m for m in order if m not in done]
    idx = {m: j for j, m in enumerate(unbuilt)}
    n = max(n_shards, len(shards))
    builds = [0] * n                     # everything shard i builds, as a bit set over `unbuilt`
    loads = [0.0] * n
    owner: dict[int, int] = {}
    planned = 0
    for i, sh in enumerate(shards):
        for m in sh:
            j = idx[m]
            builds[i] |= 1 << j
            owner[j] = i
            loads[i] += cost[m]
        planned |= builds[i]
    closure = [0] * len(unbuilt)         # a module and every unbuilt module below it
    hopeless = 0                         # did not fit anywhere: nothing above it can either
    for j, m in enumerate(unbuilt):
        k = 1 << j
        for d in deps[m]:
            dj = idx.get(d)
            if dj is not None:
                k |= closure[dj]
        closure[j] = k
        if planned >> j & 1:
            continue
        if k & hopeless:
            hopeless |= 1 << j
            continue
        placed = False
        # the shards that lack the least of it, then the emptiest
        for i in sorted(range(n), key=lambda i: ((k & ~builds[i]).bit_count(), loads[i], i))[:3]:
            lacking = k & ~builds[i]
            add = sum(cost[unbuilt[b]] for b in _bits(lacking))
            if loads[i] + add <= budget:
                for b in _bits(lacking & ~planned):
                    owner[b] = i
                builds[i] |= k
                loads[i] += add
                planned |= k
                placed = True
                break
        if not placed:
            hopeless |= 1 << j
    owned: list[list[str]] = [[] for _ in range(n)]
    extra: list[list[str]] = [[] for _ in range(n)]
    for i in range(n):
        for b in _bits(builds[i]):
            (owned if owner[b] == i else extra)[i].append(unbuilt[b])
    return owned, extra, loads


def sinks_of(shard: list[str], deps) -> list[str]:
    """Modules of the shard that no other module of the shard imports."""
    inside = set(shard)
    imported = set()
    for m in shard:
        for d in deps[m]:
            if d in inside:
                imported.add(d)
    return [m for m in shard if m not in imported]


def built_closure(shard: list[str], deps, done) -> list[str]:
    """Every already-built module the shard needs on disk, transitively."""
    inside = set(shard)
    seen: set[str] = set()
    stack = list(shard)
    while stack:
        x = stack.pop()
        for d in deps[x]:
            if d in inside or d in seen:
                continue
            seen.add(d)
            stack.append(d)
    missing = sorted(d for d in seen if d not in done)
    if missing:
        raise SystemExit(f"plan is not closed: {missing[:5]} needed but not built")
    return sorted(seen)


# --------------------------------------------------------------------------
# inputs shared by the subcommands
# --------------------------------------------------------------------------

def load_state(path: str | None):
    """Read the campaign state written by `replay_shard.py merge`.

    Returns (module -> chunk name, module -> seconds, failed, crashed counts,
    round -> artifact id of that round's bundle of chunks).
    """
    if not path or not os.path.exists(path):
        return {}, {}, {}, {}, {}
    st = json.load(open(path))
    return (st.get("where", {}), st.get("seconds", {}), st.get("failed", {}),
            st.get("crashed", {}), st.get("bundles", {}))


def usable(where, deps, order) -> set[str]:
    """The built modules whose imports, all the way down, are built too.

    Only those are of use to a later shard: Lean cannot load a module without
    every module under it. The two sets are the same unless a round stranded
    something. Round 16 did: a shard built modules on top of prerequisites it
    did not own and did not pack, their owner ran out of time, and 255 built
    modules were left standing on 72 that no chunk held. A stranded module
    counts as not built until what it stands on is.
    """
    ok: set[str] = set()
    for m in order:
        if m in where and all(d in ok for d in deps[m]):
            ok.add(m)
    return ok


def cost_model(size, overhead_s: float, s_per_kb: float) -> dict[str, float]:
    return {m: overhead_s + s_per_kb * (b / 1000.0) for m, b in size.items()}


def fit_rate(size, secs, overhead_s: float, default: float) -> float:
    """Seconds per KB of source measured on modules already built."""
    if len(secs) < 200:
        return default
    num = sum(max(0.0, s - overhead_s) for s in secs.values())
    den = sum(size[m] for m in secs if m in size) / 1000.0
    return max(0.01, num / den) if den else default


def recent_timings(where, secs, rounds: int = 2, enough: int = 200):
    """The timings of the modules built in the last `rounds` rounds.

    A module costs more the more it imports, and each round builds higher in
    the graph than the one before, so the rate measured over every module
    built so far lags what the next round will cost: after round 11 it said
    10 s for a module that took 15. Falls back to every timing when the last
    rounds are too few to fit.
    """
    by_round: dict[int, list[str]] = {}
    for m in secs:
        chunk = where.get(m, "")
        try:
            by_round.setdefault(int(chunk.split("-")[0][1:]), []).append(m)
        except (ValueError, IndexError):
            continue
    picked: dict[str, float] = {}
    for r in sorted(by_round, reverse=True)[:rounds]:
        for m in by_round[r]:
            picked[m] = secs[m]
    return picked if len(picked) >= enough else secs


def closure_sizes(deps, order) -> dict[str, int]:
    """How many modules each module imports all the way down, itself included.

    Exact, by one bit set per module, built in import order and dropped once
    every module importing it has taken it: 175,187 modules in a few seconds.
    """
    idx = {m: i for i, m in enumerate(order)}
    pending = dict.fromkeys(order, 0)
    for m in order:
        for d in deps[m]:
            pending[d] += 1
    bits: dict[str, int] = {}
    out: dict[str, int] = {}
    for m in order:
        b = 1 << idx[m]
        for d in deps[m]:
            b |= bits[d]
            pending[d] -= 1
            if pending[d] == 0:
                del bits[d]
        out[m] = b.bit_count()
        if pending[m]:
            bits[m] = b
    return out


def import_cost(closure, size, timings, bin_size: int = 5000, enough: int = 5):
    """Seconds per module from how much it imports and how long its source is.

    Before a module elaborates a line, lean maps the .olean of every module
    under it. While those fit in the runner's memory that is cheap. Past it
    every start reads them back from disk, and it becomes the whole cost:
    round 17 measured about 10 s for a module on 10,000 others, 20 s on
    20,000, and 130 to 200 s on 30,000 to 50,000. The model by source size
    alone priced those at 10 s too, so the planner packed a shard with twenty
    times what it could do, the deadline cut it off, and the rest waited a
    round each time.

    The model is seconds = a(bin of the import count) + r * KB of source, with
    one r for all bins, fitted on `timings` (the last rounds: the cost moves
    as the build climbs). a never falls as the count grows, a bin with fewer
    than `enough` timings takes the value below it, and above the highest
    measured bin a grows in proportion to the count: nothing up there has been
    measured. Returns (module -> seconds, table for the record), or None when
    the timings are too few to fit.
    """
    pts = [(closure[m] // bin_size, size[m] / 1000.0, s) for m, s in timings.items() if m in closure and m in size]
    if len(pts) < 200:
        return None
    n: dict[int, int] = {}
    sx: dict[int, float] = {}
    sy: dict[int, float] = {}
    for b, x, y in pts:
        n[b] = n.get(b, 0) + 1
        sx[b] = sx.get(b, 0.0) + x
        sy[b] = sy.get(b, 0.0) + y
    num = den = 0.0
    for b, x, y in pts:   # the slope inside the bins, shared
        dx = x - sx[b] / n[b]
        num += dx * (y - sy[b] / n[b])
        den += dx * dx
    r = min(5.0, max(0.0, num / den)) if den else 0.0
    measured = {b: max(1.0, sy[b] / n[b] - r * sx[b] / n[b]) for b in n if n[b] >= enough}
    if not measured:
        return None
    last = max(measured)
    table: list[float] = []
    a = measured[min(measured)]
    for b in range(last + 1):
        a = max(a, measured.get(b, 0.0))
        table.append(a)

    def base(k: int) -> float:
        b = k // bin_size
        return table[b] if b <= last else table[last] * k / ((last + 0.5) * bin_size)

    cost = {m: base(closure[m]) + r * size[m] / 1000.0 for m in closure if m in size}
    return cost, {"bin_modules": bin_size, "s_per_kb": round(r, 4), "seconds_by_bin": [round(t, 1) for t in table],
                  "timings": len(pts), "measured_bins": sorted(measured)}


# --------------------------------------------------------------------------
# subcommands
# --------------------------------------------------------------------------

def cmd_dag(a) -> None:
    g = build_dag(a.src)
    order, level = topo_levels(g["deps"])
    g["modules"] = len(order)
    g["edges"] = sum(len(v) for v in g["deps"].values())
    g["max_level"] = max(level.values())
    json.dump(g, open(a.out, "w"))
    print(f"modules={g['modules']} edges={g['edges']} max_level={g['max_level']} "
          f"bytes={sum(g['size'].values())} external_roots={g['external_roots']}")


def cmd_status(a) -> None:
    g = json.load(open(a.dag))
    where, secs, failed, crashed, _ = load_state(a.state)
    tot_b = sum(g["size"].values())
    done_b = sum(g["size"][m] for m in where if m in g["size"])
    print(json.dumps({
        "modules_total": len(g["deps"]),
        "modules_built": len(where),
        "bytes_total": tot_b,
        "bytes_built": done_b,
        "percent_modules": round(100.0 * len(where) / len(g["deps"]), 2),
        "failed": sorted(failed),
        "crashed": crashed,
        "complete": len(where) == len(g["deps"]),
        "main_built": "Main" in where,
    }))


def cmd_plan(a) -> None:
    g = json.load(open(a.dag))
    deps, size = g["deps"], g["size"]
    order, _ = topo_levels(deps)
    height = heights(deps, order)
    where, secs, failed, crashed, bundles = load_state(a.state)
    done = usable(where, deps, order)
    stranded = sum(1 for m in where if m in deps) - len(done)
    recent = recent_timings(where, secs)
    rate = fit_rate(size, recent, a.overhead_s, a.s_per_kb)
    cost = cost_model(size, a.overhead_s, rate)
    # once there are timings, price a module by what it imports as well
    by_imports = None if a.size_only else import_cost(closure_sizes(deps, order), size, recent)
    table = None
    if by_imports:
        cost, table = by_imports
    # a module that failed to elaborate, and everything above it, is out of
    # reach; so is one that crashed the runner three times running
    blocked = set(failed) | {m for m, n in crashed.items() if n >= a.max_crashes}
    failed = sorted(blocked)
    if blocked:
        for m in order:
            if m not in blocked and any(d in blocked for d in deps[m]):
                blocked.add(m)
    open_order = [m for m in order if m not in blocked]
    shards, waiting, loads = plan_round(
        deps, cost, open_order, height, done, a.shards, a.budget_s, a.max_modules)
    extras: list[list[str]] = [[] for _ in shards]
    if a.fill:
        # second pass: idle shards take modules together with the unbuilt
        # imports another shard already builds (see fill_idle). Idle means
        # short of what a shard can really do, not short of the generous
        # budget the first pass plans to: in round 16 the two were the same
        # number, every shard looked idle, and a quarter of the round went
        # into building modules a second time while their owners ran out of
        # time.
        shards, extras, loads = fill_idle(deps, cost, open_order, done, shards, a.shards,
                                          a.fill_budget_s if a.fill_budget_s else a.budget_s)
        keep = [i for i, sh in enumerate(shards) if sh]
        shards = [shards[i] for i in keep]
        extras = [extras[i] for i in keep]
        owned_all = {m for sh in shards for m in sh}
        waiting = sum(1 for m in open_order if m not in done and m not in owned_all)
    times: dict[str, int] = {}
    for sh, ex in zip(shards, extras):
        for m in sh + ex:
            times[m] = times.get(m, 0) + 1
    os.makedirs(a.out, exist_ok=True)
    summary = {"round": a.round, "rate_s_per_kb": round(rate, 4), "overhead_s": a.overhead_s,
               "budget_s": a.budget_s, "built_before": len(done), "blocked": len(blocked),
               "failed": failed, "waiting_after": waiting, "fill": bool(a.fill), "stranded": stranded,
               "built_twice": sum(1 for n in times.values() if n > 1),
               "cost_by_imports": table, "shards": []}
    position = {m: i for i, m in enumerate(order)}
    for i, owned in enumerate(shards):
        # what the shard builds: its own modules and the extras, in import order
        sh = sorted(owned + extras[i], key=position.__getitem__)
        need = built_closure(sh, deps, done)
        chunks = sorted({where[m] for m in need})
        fetch: dict[str, list[str]] = {}
        for c in chunks:  # a chunk is named r<round>-s<shard>
            rnd = c.split("-")[0][1:]
            if rnd not in bundles:
                raise SystemExit(f"state has no bundle for round {rnd}, needed for chunk {c}")
            fetch.setdefault(str(bundles[rnd]), []).append(f"chunk-{c}.tar.zst")
        # "modules" are the shard's own: it packs and reports those. "extra"
        # it builds only to reach them; "shared" are the modules of either
        # kind that another shard builds too, whose .olean hashes are compared.
        rec = {"round": a.round, "shard": i, "modules": owned, "extra": extras[i],
               "shared": [m for m in sh if times[m] > 1], "sinks": sinks_of(sh, deps),
               "need": need, "chunks": chunks, "fetch": fetch,
               "est_s": round(sum(cost[m] for m in sh), 1),
               "bytes": sum(size[m] for m in sh)}
        json.dump(rec, open(os.path.join(a.out, f"shard-{i}.json"), "w"))
        summary["shards"].append({"shard": i, "modules": len(owned), "extra": len(extras[i]),
                                  "sinks": len(rec["sinks"]),
                                  "need": len(need), "chunks": len(chunks), "est_s": rec["est_s"],
                                  "kb": rec["bytes"] // 1000})
    summary["n_shards"] = len(shards)
    summary["planned_modules"] = sum(len(s) for s in shards)
    summary["extra_modules"] = sum(len(e) for e in extras)
    json.dump(summary, open(os.path.join(a.out, "plan.json"), "w"), indent=1)
    print(json.dumps({k: v for k, v in summary.items() if k != "shards"}))
    for s in summary["shards"]:
        print("  ", json.dumps(s))


def cmd_simulate(a) -> None:
    g = json.load(open(a.dag))
    deps, size = g["deps"], g["size"]
    order, _ = topo_levels(deps)
    height = heights(deps, order)
    cost = cost_model(size, a.overhead_s, a.s_per_kb)
    total = sum(cost.values())
    print(f"model: {a.overhead_s}s + {a.s_per_kb}s/KB -> {total/3600:.0f} CPU-hours total; "
          f"budget {a.budget_s/3600:.1f} CPU-hours per shard, {a.shards} shards per round")
    done: set[str] = set()
    r = 0
    while len(done) < len(order) and r < a.max_rounds:
        shards, waiting, loads = plan_round(deps, cost, order, height, done, a.shards,
                                            a.budget_s, a.max_modules)
        n = sum(len(s) for s in shards)
        if not n:
            print("stuck: nothing plannable")
            break
        need = [len(built_closure(s, deps, done)) for s in shards]
        print(f"round {r:2d}: shards={len(shards):2d} modules={n:6d} "
              f"cpu_h={sum(loads)/3600:7.1f} max_shard_h={max(loads)/3600:5.2f} "
              f"max_need={max(need):6d} built_after={len(done)+n:6d} ({100*(len(done)+n)/len(order):5.1f}%)")
        for s in shards:
            done.update(s)
        r += 1
    print(f"rounds: {r}; built {len(done)} of {len(order)}")


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("dag"); s.add_argument("--src", required=True); s.add_argument("--out", required=True)
    s.set_defaults(fn=cmd_dag)
    s = sub.add_parser("status"); s.add_argument("--dag", required=True); s.add_argument("--state")
    s.set_defaults(fn=cmd_status)
    for name, fn in (("plan", cmd_plan), ("simulate", cmd_simulate)):
        s = sub.add_parser(name)
        s.add_argument("--dag", required=True)
        s.add_argument("--shards", type=int, default=12)
        s.add_argument("--budget-s", type=float, default=4 * 3600 * 3.2,
                       help="CPU-seconds one shard may be planned for")
        s.add_argument("--max-modules", type=int, default=12000)
        s.add_argument("--overhead-s", type=float, default=4.0)
        s.add_argument("--s-per-kb", type=float, default=0.5)
        if name == "plan":
            s.add_argument("--state"); s.add_argument("--round", type=int, required=True)
            s.add_argument("--out", required=True); s.add_argument("--max-crashes", type=int, default=3)
            s.add_argument("--fill", action="store_true",
                           help="second pass: idle shards also build modules whose unbuilt imports another shard owns")
            s.add_argument("--fill-budget-s", type=float, default=0.0,
                           help="what a shard can really do; the second pass fills up to this, not to --budget-s")
            s.add_argument("--size-only", action="store_true",
                           help="price a module by its source size alone, as the planner did up to round 18")
        else:
            s.add_argument("--max-rounds", type=int, default=80)
        s.set_defaults(fn=fn)
    a = p.parse_args()
    a.fn(a)


if __name__ == "__main__":
    main()
