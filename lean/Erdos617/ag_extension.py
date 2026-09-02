# Erdős 617: does the affine-plane counterexample on K_{q^2} extend by one vertex?
# Answer: no, for any prime q >= 3 (verified here for q = 3, 5; the hand proof in
# README.md covers every prime power q >= 3).
#
# Needs python-sat:  pip install python-sat
import itertools
from pysat.solvers import Cadical195


def ag_colouring(q):
    """AG(2,q): points = F_q^2, q+1 parallel classes of lines.  Colour 0 = classes 0 and q
    (slope 0 and vertical) merged, giving the rook's graph with independence number q;
    colours 1..q-1 = the remaining classes, each a disjoint union of q copies of K_q.
    Every colour class has independence number exactly q, so no (q+1)-set misses a colour.
    q must be prime here (F_q arithmetic is mod q)."""
    pts = [(x, y) for x in range(q) for y in range(q)]
    idx = {p: i for i, p in enumerate(pts)}

    def pclass(p, r):
        dx, dy = (r[0] - p[0]) % q, (r[1] - p[1]) % q
        if dx == 0:
            return q                        # vertical
        return (dy * pow(dx, q - 2, q)) % q  # slope

    col = {}
    for p, r in itertools.combinations(pts, 2):
        s = pclass(p, r)
        col[(idx[p], idx[r])] = 0 if s in (0, q) else s
    return len(pts), col


for q in (3, 5):
    n, col = ag_colouring(q)
    C = lambda a, b: col[(min(a, b), max(a, b))]
    bad = [S for S in itertools.combinations(range(n), q + 1)
           if len({C(a, b) for a, b in itertools.combinations(S, 2)}) < q]
    assert not bad, f"AG(2,{q}) is not a valid counterexample?!"
    print(f"AG(2,{q}) on K_{n}: valid, no {q+1}-set misses a colour")

    # SAT question: colour the n edges from a new vertex so every (q+1)-set containing it
    # still sees all q colours.  Variables: v(u,c) = edge to old vertex u gets colour c.
    v = lambda u, c: u * q + c + 1
    cl = []
    for u in range(n):
        cl.append([v(u, c) for c in range(q)])
        for c1 in range(q):
            for c2 in range(c1 + 1, q):
                cl.append([-v(u, c1), -v(u, c2)])
    for S in itertools.combinations(range(n), q):
        seen = {C(a, b) for a, b in itertools.combinations(S, 2)}
        for c in range(q):
            if c not in seen:
                cl.append([v(u, c) for u in S])
    with Cadical195(bootstrap_with=cl) as s:
        res = s.solve()
    print(f"  extend to K_{n+1}: {'SAT (extends)' if res else 'UNSAT (does not extend)'}")
    assert not res
