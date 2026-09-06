#!/usr/bin/env python3
"""Generate the Lean four-point certificate table for hunts/ainta_seven_point/lean-four-point.

Same architecture as `three_point_gen.py`, one dimension up: **one general cell lemma
(`wfun_ge`) instantiated at many rational intervals**, a one-dimensional cover that removes
everything except a few short intervals, and a bisection tree over the surviving boxes whose
leaves are `linarith` over constants.  The cell machinery is imported from
`three_point_gen` rather than copied, so the two tables are the same table.

Three things differ from `n = 3`, and each is forced by the functional:

    F 4 p (g0,g1,g2) = (g0+g1+g2)/p
                     + (2/3)(w g0 + w g1 + w g2)
                     + w(g0+g1) + w(g1+g2)
                     + 2 w(g0+g1+g2)

1.  The adjacent-pair coefficient is `2/(n-1) = 2/3`, not `1`.  A gap `x` with `w x` large
    therefore closes the certificate only once `(2/3) w x >= c`, so the one-dimensional
    cover has to be run at **level `3c/2`**, not at `c`.  Its near-zero intervals are
    correspondingly wider.  (At `n = 3` the coefficient is `1` and the level is `c`, which
    is why `three_point_gen` never had to name this.)
2.  The region is a tetrahedron, so the boxes are triples of near-zero intervals and the
    bisection is three-dimensional.
3.  A single box lemma would hold thousands of leaves in one declaration, which is one
    heartbeat budget on one core.  The tree is therefore cut into **chunk lemmas** of at
    most `CHUNK` leaves, bin-packed across `NMOD` modules that `lake` builds in parallel,
    with a small router lemma per box.

Usage:  python3 four_point_gen.py [c_numerator] [p]      (c = numerator/10^6)
"""
from fractions import Fraction as Fr
import math, os, sys, itertools

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import three_point_gen as G

# ---------- parameters ----------
CN_DEFAULT = 2310
P_DEFAULT = 2500
PERMOD = 60          # cell lemmas per Cells module
CHUNK = 110          # leaves per chunk lemma
NMOD = 16            # chunk modules, bin-packed by leaf count
HEARTBEATS = 20000000

NS = "Zeta23Ext.Bridge.FourPoint"
LIB = "FourPoint"


def extend_anchors(kmax):
    """`cos (pi k/2)` and `sin (pi k/2)` are 0 or +-1 for every k; `three_point_gen` stops
    at 9/2 because the three-point cutoff is 4.035.  The four-point cutoff is larger."""
    for k in range(1, 2 * kmax + 1):
        a = Fr(k, 2)
        if a in G.ANCHOR_NAME:
            continue
        G.ANCHOR_NAME[a] = ('cs_h%d' % k) if k % 2 else ('cs_%d' % (k // 2))
        G.ANCHOR_CS[a] = (int(round(math.cos(math.pi * k / 2))),
                          int(round(math.sin(math.pi * k / 2))))
    G.ANCHORS[:] = sorted(G.ANCHOR_NAME)


# The six pair terms of `F 4 p`, as (coefficient, gap-index-tuple).
COEFFS = [(Fr(2, 3), (0,)), (Fr(2, 3), (1,)), (Fr(2, 3), (2,)),
          (Fr(1), (0, 1)), (Fr(1), (1, 2)), (Fr(2), (0, 1, 2))]
# how each pair term is written in Lean, in the order of COEFFS
EXPRS = ["x", "y", "z", "(x + y)", "(y + z)", "(x + y + z)"]

sys.setrecursionlimit(200000)


def lower(box, p):
    """Exact rational lower bound for `F 4 p` on `box`, from the cell table."""
    tot = Fr(sum(b[0] for b in box), 1) / p
    Ws = []
    for coef, idxs in COEFFS:
        lo = sum(box[i][0] for i in idxs)
        hi = sum(box[i][1] for i in idxs)
        W = G.Wmulti(lo, hi)
        Ws.append(W)
        tot += coef * W
    return tot, Ws


def subdivide(box, c, S, p, depth=0):
    if sum(b[0] for b in box) >= S:
        return ('leaf', box, [Fr(0)] * 6)
    v, Ws = lower(box, p)
    if v >= c:
        return ('leaf', box, Ws)
    if depth > 46:
        return None
    w = [b[1] - b[0] for b in box]
    k = w.index(max(w))
    m = (box[k][0] + box[k][1]) / 2
    a = list(box); a[k] = (box[k][0], m)
    b = list(box); b[k] = (m, box[k][1])
    ca = subdivide(tuple(a), c, S, p, depth + 1)
    cb = subdivide(tuple(b), c, S, p, depth + 1)
    if ca is None or cb is None:
        return None
    return ('split', box, k, m, ca, cb)


def nleaves(node):
    return 1 if node[0] == 'leaf' else nleaves(node[4]) + nleaves(node[5])


def certificate(cn, p):
    c = Fr(cn, 10 ** 6)
    S = c * p
    level = Fr(3, 2) * c              # see the module docstring, point 1
    clear, bad = G.phase1(level, S)
    nb = len(bad)
    boxes, seen = [], {}
    for t in itertools.product(range(nb), repeat=3):
        if sum(bad[i][0] for i in t) >= S:
            continue
        key = min(t, tuple(reversed(t)))
        if key in seen:
            continue
        node = subdivide(tuple(bad[i] for i in t), c, S, p)
        if node is None:
            return None
        seen[key] = node
        boxes.append((key, node))
    return dict(c=c, S=S, level=level, clear=clear, bad=bad, boxes=boxes)


# ---------- cells actually referenced ----------
def collect_intervals(res):
    """Only intervals a `have` will name: a term whose `Wmulti` is zero is closed by the
    hoisted `wfun_nonneg` instead, and needs no cell lemma."""
    ivals = set(res['clear'])

    def walk(node):
        if node[0] == 'leaf':
            box, Ws = node[1], node[2]
            for (coef, idxs), W in zip(COEFFS, Ws):
                if W == 0:
                    continue
                lo = sum(box[i][0] for i in idxs)
                hi = sum(box[i][1] for i in idxs)
                for pc in G.quarter_pieces(lo, hi):
                    ivals.add(pc)
        else:
            walk(node[4]); walk(node[5])

    for (_, node) in res['boxes']:
        walk(node)
    return sorted(ivals)


# ================= Lean emission =================
R = G.R

CELLS_HDR = """import %s.Base

noncomputable section
open Real
namespace %s

""" % (LIB, NS)
FTR = "\nend %s\n" % NS


def chunk_plan(node, out):
    """Cut the tree into subtrees of at most CHUNK leaves.  Returns a router tree whose
    leaves are chunk indices."""
    if nleaves(node) <= CHUNK or node[0] == 'leaf':
        out.append(node)
        return ('call', len(out) - 1, node[1])
    return ('split', node[1], node[2], node[3],
            chunk_plan(node[4], out), chunk_plan(node[5], out))


def emit_wfact(name, expr, lo, hi, W, ind, cellW, idx, tag):
    pcs = G.quarter_pieces(lo, hi)
    if len(pcs) == 1 and cellW[pcs[0]] == W:
        return ["%shave %s : %s ≤ wfun %s := wc_%d %s (by linarith) (by linarith)"
                % (ind, name, R(W), expr, idx[pcs[0]], expr)]
    out = ["%shave %s : %s ≤ wfun %s := by" % (ind, name, R(W), expr)]
    for t, (aa, bb) in enumerate(pcs):
        k = idx[(aa, bb)]
        if t < len(pcs) - 1:
            out.append("%s  rcases le_total %s %s with h%s%d | h%s%d"
                       % (ind, expr, R(bb), tag, t, tag, t))
            out.append("%s  · exact le_trans (by norm_num) (wc_%d %s (by linarith) (by linarith))"
                       % (ind, k, expr))
        else:
            out.append("%s  exact le_trans (by norm_num) (wc_%d %s (by linarith) (by linarith))"
                       % (ind, k, expr))
    return out


def emit_node(node, ind, out, cellW, idx):
    if node[0] == 'leaf':
        box, Ws = node[1], node[2]
        for t, ((coef, idxs), W) in enumerate(zip(COEFFS, Ws)):
            if W == 0:
                continue                      # hoisted `wfun_nonneg` covers it
            lo = sum(box[i][0] for i in idxs)
            hi = sum(box[i][1] for i in idxs)
            out.extend(emit_wfact("hw%d" % t, EXPRS[t], lo, hi, W, ind, cellW, idx, "q%d" % t))
        out.append("%slinarith" % ind)
        return
    v = "xyz"[node[2]]
    out.append("%srcases le_total %s %s with hc | hc" % (ind, v, R(node[3])))
    for child in (node[4], node[5]):
        out.append("%s· " % ind)
        sub = []
        emit_node(child, ind + "  ", sub, cellW, idx)
        out[-1] = out[-1] + sub[0].lstrip()
        out.extend(sub[1:])


def emit_router(rt, ind, out):
    if rt[0] == 'call':
        b = rt[2]
        out.append("%sexact ch_%d x y z (by linarith) (by linarith) (by linarith)"
                   % (ind, rt[1]))
        out.append("%s  (by linarith) (by linarith) (by linarith)" % ind)
        return
    v = "xyz"[rt[2]]
    out.append("%srcases le_total %s %s with hc | hc" % (ind, v, R(rt[3])))
    for child in (rt[4], rt[5]):
        out.append("%s· " % ind)
        sub = []
        emit_router(child, ind + "  ", sub)
        out[-1] = out[-1] + sub[0].lstrip()
        out.extend(sub[1:])


def rhs(p):
    """The right-hand side of every box, chunk and certificate statement, written once."""
    return ("(1/(%d:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z"
            " + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z)" % p)


NONNEG = ["  have hn0 := wfun_nonneg x",
          "  have hn1 := wfun_nonneg y",
          "  have hn2 := wfun_nonneg z",
          "  have hn3 := wfun_nonneg (x + y)",
          "  have hn4 := wfun_nonneg (y + z)",
          "  have hn5 := wfun_nonneg (x + y + z)"]


def emit(cn, p, out):
    extend_anchors(12)
    res = certificate(cn, p)
    assert res is not None, "certificate does not close at c=%d/10^6, p=%d" % (cn, p)
    c, S, level = res['c'], res['S'], res['level']
    clear, bad, boxes = res['clear'], res['bad'], res['boxes']
    CSTR = "(%d/1000000:ℝ)" % cn
    LSTR = R(level)
    m = 3 + int(1 / c)
    assert c * (m - 3) <= 1 < c * (m - 2), "m is not the largest admissible block size"

    N, D = c.numerator, c.denominator
    a = p * m * D; b = 3 * (m - 1) * D; d = p * (D * m - N * (m - 3))
    g = math.gcd(math.gcd(a, b), d); a //= g; b //= g; d //= g

    ivals = collect_intervals(res)
    idx = {iv: i for i, iv in enumerate(ivals)}
    cells = {iv: G.build_cell(*iv) for iv in ivals}
    assert all(v is not None and v.W > 0 for v in cells.values()), "an unusable cell was kept"
    cellW = {iv: cells[iv].W for iv in ivals}

    os.makedirs(os.path.join(out, LIB), exist_ok=True)

    # ---- cell modules ----
    nmod = (len(ivals) + PERMOD - 1) // PERMOD
    for k in range(nmod):
        body = [CELLS_HDR]
        for iv in ivals[k * PERMOD:(k + 1) * PERMOD]:
            body.append(G.emit_cell("wc_%d" % idx[iv], cells[iv]))
        body.append(FTR)
        open(os.path.join(out, LIB, "Cells%d.lean" % k), 'w').write("".join(body))
    open(os.path.join(out, LIB, "Cells.lean"), 'w').write(
        "\n".join("import %s.Cells%d" % (LIB, k) for k in range(nmod)) + "\n")

    # ---- the one-dimensional cover ----
    segs = [(l, u, 'clear') for (l, u) in clear] + [(l, u, 'bad', i) for i, (l, u) in enumerate(bad)]
    segs.sort()
    pos = G.X0
    for s in segs:
        assert s[0] == pos, "the cover has a gap at %s" % pos
        pos = s[1]
    assert pos == S, "the cover does not reach the cutoff"

    badstr = " ∨ ".join("(%s ≤ x ∧ x ≤ %s)" % (R(l), R(u)) for l, u in bad)
    C = []; A = C.append
    A("import %s.Cells" % LIB)
    A("")
    A("/-!")
    A("# The one-dimensional cover, at the level the adjacent-pair coefficient can pay for")
    A("")
    A("The pair `(i, i+1)` of `F 4 p` carries `2/(4-1) = 2/3`, so a gap `x` closes the whole")
    A("certificate on its own exactly when `(2/3) w x ≥ c`, i.e. `w x ≥ 3c/2`.  This cover is")
    A("therefore run at `3c/2 = %s`, not at `c`." % LSTR)
    A("-/")
    A("")
    A("noncomputable section")
    A("namespace %s" % NS)
    A("")
    A("/-- **The one-dimensional cover.**  Outside %d short intervals around the low zeros of" % len(bad))
    A("the kernel, `w ≥ 3c/2` outright.  `[0,1/2]` is the window of `wfun_window`; the rest is")
    A("the table. -/")
    A("lemma cover1 (x : ℝ) (h0 : 0 ≤ x) (hS : x ≤ %s) :" % R(S))
    A("    %s ≤ wfun x ∨ %s := by" % (LSTR, badstr))
    A("  rcases le_total x (1/2 : ℝ) with hw | hw")
    A("  · exact Or.inl (le_trans (by norm_num) (wfun_window x h0 hw))")
    for si, s in enumerate(segs):
        l, u = s[0], s[1]
        last = (si == len(segs) - 1)
        hn = "hz%d" % (si + 1)
        if not last:
            A("  rcases le_total x %s with %s | %s" % (R(u), hn, hn)); ind = "  · "
        else:
            A("  have %s : x ≤ %s := hS" % (hn, R(u))); ind = "  "
        if s[2] == 'clear':
            A("%sexact Or.inl (le_trans (by norm_num) (wc_%d x (by linarith) (by linarith)))"
              % (ind, idx[(l, u)]))
        else:
            j = s[3]
            expr = "⟨by linarith, by linarith⟩"
            if j < len(bad) - 1:
                expr = "(Or.inl " + expr + ")"
            A("%sexact %s%s%s" % (ind, "Or.inr (" * (j + 1), expr, ")" * (j + 1)))
    A("")
    A("end %s" % NS)
    open(os.path.join(out, LIB, "Cover.lean"), 'w').write("\n".join(C) + "\n")

    # ---- chunks ----
    allchunks = []          # (chunkindex, node)
    routers = []            # (key, routertree)
    for (key, node) in boxes:
        local = []
        rt = chunk_plan(node, local)
        base = len(allchunks)
        allchunks.extend(local)

        def shift(t):
            if t[0] == 'call':
                return ('call', t[1] + base, t[2])
            return ('split', t[1], t[2], t[3], shift(t[4]), shift(t[5]))
        routers.append((key, shift(rt)))

    # bin-pack chunks into NMOD modules, largest first, by leaf count
    order = sorted(range(len(allchunks)), key=lambda i: -nleaves(allchunks[i]))
    bins = [[] for _ in range(NMOD)]
    load = [0] * NMOD
    for i in order:
        j = load.index(min(load))
        bins[j].append(i)
        load[j] += nleaves(allchunks[i])

    for j, members in enumerate(bins):
        L = ["import %s.Cells" % LIB, "",
             "/-! Chunk module %d of %d of the three-dimensional table.  Each lemma is one" % (j, NMOD),
             "subtree of at most %d leaves of one box's bisection tree; `%s/Boxes.lean` routes" % (CHUNK, LIB),
             "the box down to them.  Cutting the tree this way gives each subtree its own",
             "heartbeat budget and lets `lake` compile them in parallel. -/", "",
             "noncomputable section", "namespace %s" % NS, ""]
        for i in sorted(members):
            node = allchunks[i]
            x, y, z = node[1]
            L.append("set_option maxHeartbeats %d in" % HEARTBEATS)
            L.append("lemma ch_%d (x y z : ℝ) (hx1 : %s ≤ x) (hx2 : x ≤ %s)" % (i, R(x[0]), R(x[1])))
            L.append("    (hy1 : %s ≤ y) (hy2 : y ≤ %s)" % (R(y[0]), R(y[1])))
            L.append("    (hz1 : %s ≤ z) (hz2 : z ≤ %s) :" % (R(z[0]), R(z[1])))
            L.append("    %s ≤ %s := by" % (CSTR, rhs(p)))
            L.extend(NONNEG)
            body = []
            emit_node(node, "  ", body, cellW, idx)
            L.extend(body)
            L.append("")
        L.append("end %s" % NS)
        open(os.path.join(out, LIB, "Chunks%d.lean" % j), 'w').write("\n".join(L) + "\n")

    # ---- routers ----
    L = ["import %s.Chunks%d" % (LIB, j) for j in range(NMOD)]
    L += ["",
          "/-! One router lemma per surviving box of the three-dimensional table.  The body is",
          "the top of the box's bisection tree; every branch ends in a chunk lemma. -/", "",
          "noncomputable section", "namespace %s" % NS, ""]
    boxname = {}
    for (key, rt) in routers:
        nm = "box_%d_%d_%d" % key
        boxname[key] = nm
        bx = [bad[i] for i in key]
        L.append("set_option maxHeartbeats %d in" % HEARTBEATS)
        L.append("/-- The box `B%d × B%d × B%d`. -/" % (key[0] + 1, key[1] + 1, key[2] + 1))
        L.append("lemma %s (x y z : ℝ) (hx1 : %s ≤ x) (hx2 : x ≤ %s)" % (nm, R(bx[0][0]), R(bx[0][1])))
        L.append("    (hy1 : %s ≤ y) (hy2 : y ≤ %s)" % (R(bx[1][0]), R(bx[1][1])))
        L.append("    (hz1 : %s ≤ z) (hz2 : z ≤ %s) :" % (R(bx[2][0]), R(bx[2][1])))
        L.append("    %s ≤ %s := by" % (CSTR, rhs(p)))
        body = []
        emit_router(rt, "  ", body)
        L.extend(body)
        L.append("")
    L.append("end %s" % NS)
    open(os.path.join(out, LIB, "Boxes.lean"), 'w').write("\n".join(L) + "\n")

    # ---- Main ----
    L = []; A = L.append
    A("import %s.Cover" % LIB)
    A("import %s.Boxes" % LIB)
    A("")
    A("/-!")
    A("# The four-point certificate, and the unconditional bound it discharges")
    A("")
    A("`four_point_cert` proves the hypothesis `hCert` of `Zeta23Ext.Bridge.n_point_bound` at")
    A("`n = 4`, `c = %d/10⁶`, `p = %d`, so that the `n = 4` instance of that theorem is" % (cn, p))
    A("**unconditional**.  Generated by `hunts/ainta_seven_point/four_point_gen.py`; see")
    A("`hunts/ainta_seven_point/FOUR-POINT.md`.")
    A("-/")
    A("")
    A("noncomputable section")
    A("-- `HD` lives in `Zeta23.ThmD`, `Ncount` and `N0simple` in `Zeta23.ZeroSide`, and")
    A("-- `eventually_atTop` in `Filter`: the same opens `lean/bridge/Zeta23Ext/Bridge/Main.lean`")
    A("-- uses.  `autoImplicit` is off in the lakefile, so a missing one is an error rather than")
    A("-- a silent auto-bound variable.")
    A("open Filter")
    A("open Zeta23 Zeta23.ZeroSide Zeta23.ThmD")
    A("namespace %s" % NS)
    A("")
    A("private lemma sum3 (f : Fin (4-1) → ℝ) : ∑ i, f i = f 0 + f 1 + f 2 := by")
    A("  show ∑ i : Fin 3, f i = f 0 + f 1 + f 2")
    A("  exact Fin.sum_univ_three f")
    A("")
    A("/-- The four-point functional, written out.  The pair coefficient `2/(n − (j−i))` is")
    A("`2/3` on the three adjacent pairs, `1` on the two next-nearest pairs and `2` on the")
    A("outer pair. -/")
    A("lemma F4_eq (p : ℕ) (g : Fin 3 → ℝ) :")
    A("    F 4 p g = (1/(p:ℝ)) * (g 0 + g 1 + g 2)")
    A("      + 2/3 * wfun (g 0) + 2/3 * wfun (g 1) + 2/3 * wfun (g 2)")
    A("      + wfun (g 0 + g 1) + wfun (g 1 + g 2) + 2 * wfun (g 0 + g 1 + g 2) := by")
    A("  simp only [F, ptsN, sum3, Fin.sum_univ_four, Fin.isValue]")
    A("  norm_num")
    A("  -- `norm_num` evaluates the six pair coefficients `2/(4 − (j−i))` and cancels the")
    A("  -- telescoping `ptsN` differences; whether it also closes the goal depends on the")
    A("  -- association it leaves, so `ring` is optional rather than required.")
    A("  try ring")
    A("")
    nb = len(bad)
    A("-- The `%d`-case analysis, carried by a private lemma so that the advertised" % (nb ** 3))
    A("-- `four_point_cert` below is `intro`, `rw` and `exact` at the DEFAULT heartbeat")
    A("-- budget.  `set_option maxHeartbeats` is a compile-resource limit and nothing else,")
    A("-- it is not an axiom and does not appear in `#print axioms`, but the advertised")
    A("-- statements are worth keeping free of it.")
    A("set_option maxHeartbeats %d in" % HEARTBEATS)
    A("private lemma cert_core (x y z : ℝ) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hz0 : 0 ≤ z) :")
    A("    %s ≤ %s := by" % (CSTR, rhs(p)))
    for ln in NONNEG:
        A(ln)
    A("  rcases le_total %s (x + y + z) with hS | hS" % R(S))
    A("  · linarith")
    A("  have hxS : x ≤ %s := by linarith" % R(S))
    A("  have hyS : y ≤ %s := by linarith" % R(S))
    A("  have hzS : z ≤ %s := by linarith" % R(S))
    A("  rcases cover1 x hx0 hxS with hcx | hbx")
    A("  · linarith")
    A("  rcases cover1 y hy0 hyS with hcy | hby")
    A("  · linarith")
    A("  rcases cover1 z hz0 hzS with hcz | hbz")
    A("  · linarith")
    A("  rcases hbx with %s" % " | ".join("hbx%d" % t for t in range(nb)))
    A("  all_goals (rcases hby with %s)" % " | ".join("hby%d" % t for t in range(nb)))
    A("  all_goals (rcases hbz with %s)" % " | ".join("hbz%d" % t for t in range(nb)))
    for i in range(nb):
        for j in range(nb):
            for k in range(nb):
                key = min((i, j, k), (k, j, i))
                if key not in boxname:
                    A("  · exfalso; linarith [hbx%d.1, hby%d.1, hbz%d.1]" % (i, j, k))
                    continue
                nm = boxname[key]
                if (i, j, k) == key:
                    A("  · exact %s x y z hbx%d.1 hbx%d.2 hby%d.1 hby%d.2 hbz%d.1 hbz%d.2"
                      % (nm, i, i, j, j, k, k))
                else:
                    A("  · have h := %s z y x hbz%d.1 hbz%d.2 hby%d.1 hby%d.2 hbx%d.1 hbx%d.2"
                      % (nm, k, k, j, j, i, i))
                    A("    rw [show z + y + x = x + y + z from by ring,")
                    A("        show z + y = y + z from by ring,")
                    A("        show y + x = x + y from by ring] at h")
                    A("    linarith")
    A("")
    A("/-- **The four-point certificate.**  This is the hypothesis `hCert` of")
    A("`Zeta23Ext.Bridge.n_point_bound` at `n = 4`, `c = %d/10⁶`, `p = %d`, proved. -/" % (cn, p))
    A("theorem four_point_cert :")
    A("    ∀ g : Fin (4-1) → ℝ, (∀ i, 0 ≤ g i) → %s ≤ F 4 %d g := by" % (CSTR, p))
    A("  intro g hg")
    A("  rw [F4_eq]")
    A("  exact cert_core (g 0) (g 1) (g 2) (hg 0) (hg 1) (hg 2)")
    A("")
    A("/-- `Phi_n 4 c m p` at the certificate's parameters, as an exact rational in `HD 1`. -/")
    A("theorem Phi_four : Phi_n 4 %s %d %d = (%d * HD 1 - %d) / %d := by" % (CSTR, m, p, a, b, d))
    A("  unfold Phi_n")
    A("  push_cast")
    A("  -- `1 − c(m−(n−1))/m` and the right denominator are nonzero rationals, so the")
    A("  -- identity is a single cross-multiplication with `HD 1` left as an atom.")
    A("  rw [div_eq_div_iff (by norm_num) (by norm_num)]")
    A("  ring")
    A("")
    A("/-- **The four-point bound, unconditional.**  `Zeta23Ext.Bridge.n_point_bound` at")
    A("`n = 4` with its certificate hypothesis discharged by `four_point_cert`: for Mathlib's")
    A("`riemannZeta`, for every `ε > 0` and all large `T`, `(Φ₄ − ε) N(T,2T) ≤ N₀ˢ(T,2T)` with")
    A("`Φ₄ = (%d H − %d)/%d`, `H = HD 1 = 3/2 − (1/√2)cot(1/√2)`. -/" % (a, b, d))
    A("theorem four_point_bound :")
    A("    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,")
    A("      ((%d * HD 1 - %d) / %d - ε) * (Ncount T (2 * T) : ℝ)" % (a, b, d))
    A("        ≤ N0simple T (2 * T) := by")
    A("  rw [← Phi_four]")
    A("  exact n_point_bound 4 %s %d %d (by norm_num) (by norm_num) (by norm_num)" % (CSTR, m, p))
    A("    (by norm_num) four_point_cert (by norm_num)")
    A("")
    A("/-- **The same bound as a proportion.** -/")
    A("theorem four_point_bound_ratio :")
    A("    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,")
    A("      (%d * HD 1 - %d) / %d - ε" % (a, b, d))
    A("        ≤ (N0simple T (2 * T) : ℝ) / (Ncount T (2 * T) : ℝ) := by")
    A("  intro ε hε")
    A("  obtain ⟨T₁, hT₁⟩ := four_point_bound ε hε")
    A("  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp eventually_Ncount_pos")
    A("  refine ⟨max T₁ T₂, fun T hT => ?_⟩")
    A("  have h1 := hT₁ T (le_trans (le_max_left _ _) hT)")
    A("  have h2 := hT₂ T (le_trans (le_max_right _ _) hT)")
    A("  rw [le_div_iff₀ h2]")
    A("  exact h1")
    A("")
    A("/-! ### Standing axiom audit (idiom of `Zeta23Ext/Bridge/Defs.lean`) -/")
    A("")
    for nm in ("F4_eq", "cover1", "four_point_cert", "Phi_four", "four_point_bound",
               "four_point_bound_ratio"):
        A("#print axioms %s" % nm)
    A("")
    A("end %s" % NS)
    open(os.path.join(out, LIB, "Main.lean"), 'w').write("\n".join(L) + "\n")

    root = (["import %s.Base" % LIB, "import %s.Cells" % LIB, "import %s.Cover" % LIB]
            + ["import %s.Chunks%d" % (LIB, j) for j in range(NMOD)]
            + ["import %s.Boxes" % LIB, "import %s.Main" % LIB, ""])
    open(os.path.join(out, "%s.lean" % LIB), 'w').write("\n".join(root))

    return dict(cn=cn, p=p, m=m, S=S, level=level, ncells=len(ivals), nmod=nmod,
                nleaf=sum(nleaves(n) for (_, n) in boxes), nbox=len(boxes),
                nchunk=len(allchunks), load=load, bad=bad, nclear=len(clear), phi=(a, b, d))


if __name__ == '__main__':
    cn = int(sys.argv[1]) if len(sys.argv) > 1 else CN_DEFAULT
    p = int(sys.argv[2]) if len(sys.argv) > 2 else P_DEFAULT
    here = os.path.dirname(os.path.abspath(__file__))
    info = emit(cn, p, os.path.join(here, "lean-four-point"))
    H = 0.67250070367941164573
    a, b, d = info['phi']
    print("c = %d/10^6   m = %d   p = %d   cutoff S = %s   cover level 3c/2 = %s"
          % (cn, info['m'], p, float(info['S']), float(info['level'])))
    print("bad intervals: %s" % [(float(l), float(u)) for l, u in info['bad']])
    print("1-D cell lemmas %d in %d modules; clear segments %d" % (info['ncells'], info['nmod'], info['nclear']))
    print("3-D: %d boxes, %d leaves, %d chunk lemmas in %d modules" % (info['nbox'], info['nleaf'], info['nchunk'], NMOD))
    print("chunk-module leaf loads: %s" % info['load'])
    print("Phi_4 = (%d * HD 1 - %d)/%d = %.20f  (H = %.20f, Phi_4 - H = %.4e)"
          % (a, b, d, (a * H - b) / d, H, (a * H - b) / d - H))
