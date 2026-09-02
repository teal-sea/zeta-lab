"""Erdős 617, case r: every r-colouring of K_{r^2+1} has an (r+1)-set missing a colour.

Equivalent SAT question: is there an r-colouring of the edges of K_{r^2+1} in which every
(r+1)-set of vertices sees all r colours?  SAT = counterexample, UNSAT = the case holds.

Cube-and-conquer, one Modal container per cube.  A cube fixes how vertex 0's r^2 edges are
split among the r colours (d_0 >= d_1 >= ... >= d_{r-1}, sum r^2).  Sorting is lossless:
relabel colours so the counts are nonincreasing, then order vertices 1..r^2 by the colour of
their edge to vertex 0.  Inside each block, vertices are also sorted by the colour of their
edge to vertex 1 (vertex 1 sits in block 0 and is left out of that sort), which is a second
lossless break.

Run:  modal run e617_modal.py --r 4 --tlimit 600
"""
import itertools, subprocess, time, os
import modal

app = modal.App("erdos-617")
image = (
    modal.Image.debian_slim(python_version="3.12")
    .apt_install("git", "build-essential")
    .run_commands(
        "git clone --depth 1 https://github.com/arminbiere/kissat /opt/kissat",
        "cd /opt/kissat && ./configure && make -j4 && cp build/kissat /usr/local/bin/kissat",
    )
)
vol = modal.Volume.from_name("erdos-617", create_if_missing=True)


def cubes(r):
    n2 = r * r
    def parts(n, k, mx):
        if k == 0:
            return [[]] if n == 0 else []
        return [[p] + rest for p in range(min(n, mx), -1, -1) for rest in parts(n - p, k - 1, p)]
    return parts(n2, r, n2)



def turan_min_edges(r):
    """Each colour class has independence number <= r, so its complement is K_{r+1}-free
    and has at most ex(n, K_{r+1}) = |T(n,r)| edges.  What is left is a lower bound on the
    class itself.  n = r^2+1, so the Turan graph has one part of size r+1 and r-1 of size r."""
    n = r * r + 1
    parts = [r + 1] + [r] * (r - 1)
    total = n * (n - 1) // 2
    turan = total - sum(p * (p - 1) // 2 for p in parts)
    return total - turan


def atleast_k(lits, k, top):
    """Sequential counter, only-if direction, enough to assert at least k of lits."""
    n = len(lits)
    if k <= 0:
        return [], top
    S = {}
    for i in range(1, n + 1):
        for j in range(1, min(k, i) + 1):
            top += 1
            S[(i, j)] = top
    def sv(i, j):
        if j <= 0: return None          # trivially true
        if i <= 0 or j > i: return 0    # false
        return S[(i, j)]
    cl = [[sv(n, k)]]
    for i in range(1, n + 1):
        for j in range(1, min(k, i) + 1):
            a, b, c = sv(i, j), sv(i - 1, j), sv(i - 1, j - 1)
            c1 = [-a] + ([] if b == 0 else [b]) + [lits[i - 1]]
            cl.append(c1)
            c2 = [-a] + ([] if b == 0 else [b]) + ([] if c is None else ([] if c == 0 else [c]))
            if c is None:
                pass                    # s[i-1][j-1] trivially true, clause satisfied
            else:
                cl.append(c2)
    return cl, top


def build_cnf(r, degs, card=False):
    n = r * r + 1
    edges = list(itertools.combinations(range(n), 2))
    eid = {e: i for i, e in enumerate(edges)}
    var = lambda e, c: eid[e] * r + c + 1
    cl = []
    for e in edges:
        cl.append([var(e, c) for c in range(r)])
        for c1 in range(r):
            for c2 in range(c1 + 1, r):
                cl.append([-var(e, c1), -var(e, c2)])
    for S in itertools.combinations(range(n), r + 1):
        es = [var(e, 0) for e in itertools.combinations(S, 2)]
        for c in range(r):
            cl.append([x + c for x in es])
    # the cube: vertex 0's edges, block by block
    block = {}
    v = 1
    for c, d in enumerate(degs):
        for _ in range(d):
            cl.append([var((0, v), c)])
            block[v] = c
            v += 1
    assert v == n
    # inside a block, sort by colour of the edge to vertex 1 (vertex 1 itself excluded)
    for u in range(2, n - 1):
        if block[u] == block[u + 1]:
            for c1 in range(r):
                for c2 in range(c1):
                    cl.append([-var((1, u), c1), -var((1, u + 1), c2)])
    nv = len(edges) * r
    if card:
        kmin = turan_min_edges(r)
        top = nv
        for c in range(r):
            extra, top = atleast_k([var(e, c) for e in edges], kmin, top)
            cl.extend(extra)
        nv = top
    return nv, cl, edges, var


@app.function(image=image, cpu=1, memory=3072, timeout=4 * 3600 + 600, volumes={"/out": vol})
def solve_cube(r: int, degs: list, tlimit: int, card: bool = False):
    nv, cl, edges, var = build_cnf(r, degs, card)
    path = f"/tmp/e617_r{r}_{'-'.join(map(str, degs))}.cnf"
    with open(path, "w") as f:
        f.write(f"p cnf {nv} {len(cl)}\n")
        f.write("\n".join(" ".join(map(str, c)) + " 0" for c in cl))
        f.write("\n")
    t = time.time()
    p = subprocess.run(["kissat", "-q", f"--time={tlimit}", path], capture_output=True, text=True)
    dt = time.time() - t
    out = p.stdout
    if "s SATISFIABLE" in out:
        status = "SAT"
        lits = set()
        for ln in out.splitlines():
            if ln.startswith("v "):
                lits.update(int(x) for x in ln[2:].split() if int(x) > 0)
        col = {e: next(c for c in range(r) if var(e, c) in lits) for e in edges}
        n = r * r + 1
        ok = all(len({col[e] for e in itertools.combinations(S, 2)}) == r
                 for S in itertools.combinations(range(n), r + 1))
        name = f"/out/e617_r{r}_counterexample_{'-'.join(map(str, degs))}.txt"
        with open(name, "w") as f:
            f.write(f"# r={r} n={n} verified_balanced={ok}\n")
            for e in edges:
                f.write(f"{e[0]} {e[1]} {col[e]}\n")
        vol.commit()
        return {"degs": degs, "status": status, "secs": round(dt, 1), "verified": ok, "file": name}
    if "s UNSATISFIABLE" in out:
        status = "UNSAT"
    else:
        status = "UNKNOWN"
    return {"degs": degs, "status": status, "secs": round(dt, 1), "clauses": len(cl)}


@app.local_entrypoint()
def main(r: int = 4, tlimit: int = 600, only: str = "", card: bool = False):
    cs = cubes(r)
    if only:
        cs = [[int(x) for x in c.split("-")] for c in only.split(",")]
    print(f"r={r}: {len(cs)} cubes, {tlimit}s each", flush=True)
    t0 = time.time()
    res = []
    for k in solve_cube.map([r] * len(cs), cs, [tlimit] * len(cs), [card] * len(cs), order_outputs=False):
        res.append(k)
        print(f"  {k['status']:<7} {k['secs']:>8.1f}s  degs={k['degs']}" + (f"  VERIFIED={k['verified']} {k['file']}" if k['status'] == 'SAT' else ""), flush=True)
    from collections import Counter
    c = Counter(k["status"] for k in res)
    tot = sum(k["secs"] for k in res)
    print(f"\nr={r} summary: {dict(c)}  cube-seconds={tot:.0f}  wall={time.time()-t0:.0f}s")
    if c.get("SAT"):
        print("COUNTEREXAMPLE FOUND: Erdős 617 is false at r=%d" % r)
    elif c.get("UNKNOWN"):
        print("UNFINISHED: %d cubes hit the time limit; no conclusion for r=%d" % (c["UNKNOWN"], r))
    else:
        print("ALL CUBES UNSAT: the r=%d case of Erdős 617 holds (kissat, no proof certificate kept)" % r)
    unk = [k["degs"] for k in res if k["status"] == "UNKNOWN"]
    if unk:
        print("unfinished cubes:", unk)
