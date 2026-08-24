#!/usr/bin/env python3
"""Generate the Lean three-point certificate table for the `ThreePoint` library of lean/bridge.

Everything is exact rational arithmetic (`fractions.Fraction`); floating point is used
only to *steer* the branch and bound, never to justify a bound.  Every interval step
below mirrors, one for one, a lemma that the emitted Lean actually applies:

    pi   in [pi_lo, pi_hi]                            Real.pi_gt_d20 / Real.pi_lt_d20
    gam  in [GL, GU]                                  ThreePoint.gam_bounds
    cos t in [taylorCos(tu) - E, taylorCos(tl) + E]   ThreePoint.cos_lower / cos_upper
    sin t in [taylorSin(tl) - E, taylorSin(tu) + E]   ThreePoint.sin_lower / sin_upper
    E = 13/5748019200                                 ThreePoint.taylorErr

    k(x) = N/D,  N = cos(pi x) - 2 gam (pi x) sin(pi x),  D = 1 - 2 (pi x)^2
    w(x) = k(x)^2 >= (nlo/dhi)^2  when  nlo <= |N| and |D| <= dhi   ThreePoint.wfun_ge

Usage:  python3 three_point_gen.py [c_numerator]     (c = numerator/10^6, default 1345)
Writes ThreePoint/Cells*.lean, ThreePoint/Main.lean and ThreePoint.lean under lean/bridge/.
"""
from fractions import Fraction as Fr
import math, os, sys

# ---------- constants proved in ThreePoint/Base.lean ----------
PL = Fr(314159265358979323846, 10**20)
PU = Fr(314159265358979323847, 10**20)
E  = Fr(13, 5748019200)
GL = Fr(8274992907, 10**10)
GU = Fr(8274993018, 10**10)

DA = 10**10     # denominator for reduced angles
DB = 10**12     # denominator for every other interval endpoint
DW = 10**13     # denominator for the cell value W

P  = 3000       # pressure denominator

def fl(x, d=DB): return Fr(math.floor(x*d), d)
def ce(x, d=DB): return Fr(math.ceil(x*d), d)

def taylorCos(t): return 1 - t**2/2 + t**4/24 - t**6/720 + t**8/40320 - t**10/3628800
def taylorSin(t): return t - t**3/6 + t**5/120 - t**7/5040 + t**9/362880 - t**11/39916800

def imul(a, b):
    p = [a[0]*b[0], a[0]*b[1], a[1]*b[0], a[1]*b[1]]
    return (min(p), max(p))

ANCHOR_NAME = {Fr(1,2):'cs_h1', Fr(1):'cs_1', Fr(3,2):'cs_h3', Fr(2):'cs_2',
               Fr(5,2):'cs_h5', Fr(3):'cs_3', Fr(7,2):'cs_h7', Fr(4):'cs_4',
               Fr(9,2):'cs_h9'}
ANCHOR_CS = {Fr(1,2):(0,1), Fr(1):(-1,0), Fr(3,2):(0,-1), Fr(2):(1,0),
             Fr(5,2):(0,1), Fr(3):(-1,0), Fr(7,2):(0,-1), Fr(4):(1,0),
             Fr(9,2):(0,1)}
ANCHORS = sorted(ANCHOR_NAME)

def anchor_of(l, u):
    for a in ANCHORS:
        if a <= l and u <= a + Fr(1,4): return (a, 1)
        if a - Fr(1,4) <= l and u <= a: return (a, -1)
    return None

class Cell:
    __slots__ = ('l','u','a','side','TL','TU','CL','CU','SL','SU','coefC','fC','coefS','fS',
                 'CXL','CXU','SXL','SXU','BL','BU','P2L','P2U','TLO','THI','NLO','sgn',
                 'DHI','W')

def build_cell(l, u):
    an = anchor_of(l, u)
    if an is None: return None
    a, side = an
    c = Cell(); c.l, c.u, c.a, c.side = l, u, a, side
    if side > 0: yl, yu = l - a, u - a
    else:        yl, yu = a - u, a - l
    if not (0 <= yl <= yu <= Fr(1,4)): return None
    c.TL = fl(PL*yl, DA); c.TU = ce(PU*yu, DA)
    if c.TL < 0: c.TL = Fr(0)
    if c.TU > 1: return None
    c.CL = fl(taylorCos(c.TU) - E); c.CU = ce(taylorCos(c.TL) + E)
    c.SL = fl(taylorSin(c.TL) - E); c.SU = ce(taylorSin(c.TU) + E)
    ca, sa = ANCHOR_CS[a]
    if sa == 0:
        c.coefC, c.fC = ca, 'cos'
        c.coefS, c.fS = ca*side, 'sin'
    else:
        c.coefC, c.fC = -sa*side, 'sin'
        c.coefS, c.fS = sa, 'cos'
    def scal(k, lohi): return (k*lohi[0], k*lohi[1]) if k > 0 else (k*lohi[1], k*lohi[0])
    C = (c.CL, c.CU); S = (c.SL, c.SU)
    c.CXL, c.CXU = scal(c.coefC, C if c.fC == 'cos' else S)
    c.SXL, c.SXU = scal(c.coefS, C if c.fS == 'cos' else S)
    c.BL = fl(PL*l); c.BU = ce(PU*u)
    if c.BL <= 0: return None
    c.P2L = fl(2*GL*c.BL); c.P2U = ce(2*GU*c.BU)
    T = imul((c.P2L, c.P2U), (c.SXL, c.SXU))
    c.TLO = fl(T[0]); c.THI = ce(T[1])
    nlo_pos = fl(c.CXL - c.THI)
    nhi = ce(c.CXU - c.TLO)
    if nlo_pos > 0:   c.NLO, c.sgn = nlo_pos, 1
    elif nhi < 0:     c.NLO, c.sgn = -nhi, -1
    else:             c.NLO, c.sgn = Fr(0), 0
    c.DHI = ce(2*c.BU**2 - 1)
    if 2*c.BL**2 <= 1: return None
    c.W = fl((c.NLO/c.DHI)**2, DW) if c.NLO > 0 else Fr(0)
    if c.W < 0: c.W = Fr(0)
    return c

# ---------- float guidance only ----------
S2 = math.sqrt(2.0); GAMf = (1/S2)*math.cos(1/S2)/math.sin(1/S2)
def wtrue(x):
    b = math.pi*float(x)
    return ((math.cos(b) - 2*GAMf*b*math.sin(b))/(1-2*b*b))**2
def wmin_true(l, u, n=120):
    return min(wtrue(l + (u-l)*Fr(i,n)) for i in range(n+1))

X0 = Fr(1,2)          # [0,1/2] is the sinc window of ThreePoint.wfun_window

_cache = {}
def W_of(l, u):
    key = (l,u)
    if key not in _cache: _cache[key] = build_cell(l,u)
    c = _cache[key]
    return (Fr(0) if c is None else c.W), c

def quarter_pieces(l, u):
    cuts = [l]
    q = (l // Fr(1,4) + 1) * Fr(1,4)
    while q < u:
        cuts.append(q); q += Fr(1,4)
    cuts.append(u)
    return [(cuts[i], cuts[i+1]) for i in range(len(cuts)-1) if cuts[i] < cuts[i+1]]

def Wmulti(l, u):
    return min(W_of(*pc)[0] for pc in quarter_pieces(l, u))

def phase1(c, S):
    roots = []; a = X0
    while a < S:
        b = min(a + Fr(1,4), S); roots.append((a,b)); a = b
    clear, bad = [], []
    stack = list(reversed(roots))
    while stack:
        l, u = stack.pop()
        if W_of(l,u)[0] >= c: clear.append((l,u)); continue
        if wmin_true(l,u) < float(c) and (u-l) <= Fr(1,64): bad.append((l,u)); continue
        if u-l <= Fr(1,4096): bad.append((l,u)); continue
        m = (l+u)/2; stack.append((m,u)); stack.append((l,m))
    bad.sort(); merged = []
    for iv in bad:
        if merged and merged[-1][1] == iv[0]: merged[-1] = (merged[-1][0], iv[1])
        else: merged.append(iv)
    clear.sort()
    return clear, merged

sys.setrecursionlimit(100000)

def subdivide(box, c, S, depth):
    x0,x1,y0,y1 = box
    if x0 + y0 >= S: return ('pressure', box)
    W0 = Wmulti(x0,x1); W1 = Wmulti(y0,y1); W2 = Wmulti(x0+y0,x1+y1)
    if Fr(x0+y0)/P + W0 + W1 + 2*W2 >= c: return ('leaf', box, W0, W1, W2)
    if depth > 40: return None
    if x1-x0 >= y1-y0:
        m = (x0+x1)/2
        a = subdivide((x0,m,y0,y1), c,S,depth+1); b = subdivide((m,x1,y0,y1), c,S,depth+1)
        if a is None or b is None: return None
        return ('splitx', box, m, a, b)
    m = (y0+y1)/2
    a = subdivide((x0,x1,y0,m), c,S,depth+1); b = subdivide((x0,x1,m,y1), c,S,depth+1)
    if a is None or b is None: return None
    return ('splity', box, m, a, b)

def phase2(c, S, bad):
    trees = []
    for i, I in enumerate(bad):
        for j, J in enumerate(bad):
            if j < i or I[0] + J[0] >= S: continue
            node = subdivide((I[0], I[1], J[0], J[1]), c, S, 0)
            if node is None: return None
            trees.append((i, j, (I[0],I[1],J[0],J[1]), node))
    return trees

def count(node):
    return 1 if node[0] in ('pressure','leaf') else count(node[3]) + count(node[4])

def collect_intervals(trees, clear):
    ivals = set(clear)
    def walk(n):
        if n[0] == 'leaf':
            x0,x1,y0,y1 = n[1]
            for pc in quarter_pieces(x0,x1): ivals.add(pc)
            for pc in quarter_pieces(y0,y1): ivals.add(pc)
            for pc in quarter_pieces(x0+y0,x1+y1): ivals.add(pc)
        elif n[0] != 'pressure':
            walk(n[3]); walk(n[4])
    for (_,_,_,node) in trees: walk(node)
    return sorted(ivals)

def certificate(cn):
    c = Fr(cn, 10**6); S = c*P
    clear, bad = phase1(c, S)
    trees = phase2(c, S, bad)
    if trees is None: return None
    return dict(c=c, S=S, clear=clear, bad=bad, trees=trees,
                ivals=collect_intervals(trees, clear),
                n2d=sum(count(t[3]) for t in trees))

# ================= Lean emission =================
def R(q):
    return "(%d:ℝ)" % q.numerator if q.denominator == 1 else "(%d/%d:ℝ)" % (q.numerator, q.denominator)

CELL = """
theorem {name} (x : ℝ) (h₁ : {L} ≤ x) (h₂ : x ≤ {U}) : {W} ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : {TL} ≤ Real.pi * {RR} := by nlinarith
  have ht2 : Real.pi * {RR} ≤ {TU} := by nlinarith
  have hc1 : {CL} ≤ Real.cos (Real.pi * {RR}) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : {CL} ≤ taylorCos {TU} - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * {RR}) ≤ {CU} := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos {TL} + taylorErr ≤ {CU} := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : {SL} ≤ Real.sin (Real.pi * {RR}) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : {SL} ≤ taylorSin {TL} - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * {RR}) ≤ {SU} := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin {TU} + taylorErr ≤ {SU} := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = {coefC} * Real.{fC} (Real.pi * {RR}) := by
    have h := (trig_shift {A} (x - {A})).1
    rw [show {A} + (x - {A}) = x by ring, {CS}.1, {CS}.2] at h
    rw [h{FLIP}]; ring
  have hsx : Real.sin (Real.pi*x) = {coefS} * Real.{fS} (Real.pi * {RR}) := by
    have h := (trig_shift {A} (x - {A})).2
    rw [show {A} + (x - {A}) = x by ring, {CS}.1, {CS}.2] at h
    rw [h{FLIP}]; ring
  have hcxl : {CXL} ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ {CXU} := by rw [hcx]; linarith
  have hsxl : {SXL} ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ {SXU} := by rw [hsx]; linarith
  have hb1 : {BL} ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ {BU} := by nlinarith
  have hp1 : {P2L} ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ {P2U} := by nlinarith [hg.1, hg.2]
  have hT1 : {TLO} ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ {THI} := by nlinarith
  have hN : {NLO} ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    {ABSLEM} (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ {DHI} := by nlinarith
  have hfin := wfun_ge x {NLO} {DHI} (by norm_num) (by norm_num) hD0 hD hN
  have hsq : {W} ≤ ({NLO}/{DHI})^2 := by norm_num
  linarith
"""

TRIV = """
theorem {name} (x : ℝ) (_h₁ : {L} ≤ x) (_h₂ : x ≤ {U}) : (0:ℝ) ≤ wfun x := wfun_nonneg x
"""

def emit_cell(name, c):
    if c.NLO == 0 or c.W == 0:
        return TRIV.format(name=name, L=R(c.l), U=R(c.u))
    A = R(c.a)
    RR = "(x - %s)" % A if c.side > 0 else "(%s - x)" % A
    flip = "" if c.side > 0 else ", cos_flip %s x, sin_flip %s x" % (A, A)
    return CELL.format(
        name=name, L=R(c.l), U=R(c.u), W=R(c.W), TL=R(c.TL), TU=R(c.TU),
        CL=R(c.CL), CU=R(c.CU), SL=R(c.SL), SU=R(c.SU), RR=RR, A=A,
        coefC=R(Fr(c.coefC)), fC=c.fC, coefS=R(Fr(c.coefS)), fS=c.fS,
        CS=ANCHOR_NAME[c.a], FLIP=flip,
        CXL=R(c.CXL), CXU=R(c.CXU), SXL=R(c.SXL), SXU=R(c.SXU),
        BL=R(c.BL), BU=R(c.BU), P2L=R(c.P2L), P2U=R(c.P2U),
        TLO=R(c.TLO), THI=R(c.THI), NLO=R(c.NLO), DHI=R(c.DHI),
        ABSLEM="abs_ge_of_le" if c.sgn > 0 else "abs_ge_of_ge")

HDR = """import ThreePoint.Base

noncomputable section
open Real
namespace Zeta23Ext.Bridge.ThreePoint

"""
FTR = "\nend Zeta23Ext.Bridge.ThreePoint\n"
PERMOD = 60

def emit(cn, out):
    r = certificate(cn)
    assert r is not None, "certificate does not close at c=%d/10^6" % cn
    c, S = r['c'], r['S']
    clear, bad, trees, ivals = r['clear'], r['bad'], r['trees'], r['ivals']
    CSTR = "(%d/1000000:ℝ)" % cn
    m = 2 + int(1/c)
    assert c*(m-2) <= 1 < c*(m-1)
    Nn, Dd = c.numerator, c.denominator
    a = P*m*Dd; b = 2*(m-1)*Dd; d = P*(Dd*m - Nn*(m-2))
    g = math.gcd(math.gcd(a,b),d); a//=g; b//=g; d//=g

    idx = {iv:i for i,iv in enumerate(ivals)}
    cellW = {iv: (Fr(0) if build_cell(*iv) is None else build_cell(*iv).W) for iv in ivals}
    nmod = (len(ivals) + PERMOD - 1)//PERMOD
    for k in range(nmod):
        body = [HDR]
        for iv in ivals[k*PERMOD:(k+1)*PERMOD]:
            body.append(emit_cell("wc_%d" % idx[iv], build_cell(*iv)))
        body.append(FTR)
        open(os.path.join(out, "ThreePoint", "Cells%d.lean" % k), 'w').write("".join(body))

    L = []; A = L.append
    A("import ThreePoint.Base")
    for k in range(nmod): A("import ThreePoint.Cells%d" % k)
    A("")
    A("/-!")
    A("# The three-point certificate, and the unconditional bound it discharges")
    A("")
    A("`three_point_cert` proves the hypothesis `hCert` of `Zeta23Ext.Bridge.n_point_bound` at")
    A("`n = 3`, `c = %d/10⁶`, `p = %d`, so that the `n = 3` instance of that theorem is" % (cn, P))
    A("**unconditional**.  Generated by `hunts/ainta_seven_point/three_point_gen.py`; see")
    A("`hunts/ainta_seven_point/THREE-POINT.md`.")
    A("-/")
    A("")
    A("noncomputable section")
    # `HD` lives in `Zeta23.ThmD`, `Ncount` and `N0simple` in `Zeta23.ZeroSide`, and
    # `eventually_atTop` in `Filter`.  These are exactly the opens
    # `lean/bridge/Zeta23Ext/Bridge/Main.lean` uses; without them `autoImplicit`
    # silently turns each of them into an auto-bound variable and the advertised
    # statement becomes a statement about nothing.  `open Real` was vestigial:
    # this module contains no unqualified `Real` name.
    A("open Filter")
    A("open Zeta23 Zeta23.ZeroSide Zeta23.ThmD")
    A("namespace Zeta23Ext.Bridge.ThreePoint")
    A("")
    A("private lemma sum2 (f : Fin (3-1) → ℝ) : ∑ i, f i = f 0 + f 1 := by")
    A("  show ∑ i : Fin 2, f i = f 0 + f 1")
    A("  exact Fin.sum_univ_two f")
    A("")
    A("/-- The three-point functional, written out.  The pair coefficient `2/(n − (j−i))` is `1`")
    A("on the two adjacent pairs and `2` on the outer pair. -/")
    A("lemma F3_eq (p : ℕ) (g : Fin 2 → ℝ) :")
    A("    F 3 p g = (1/(p:ℝ)) * (g 0 + g 1) + wfun (g 0) + wfun (g 1) + 2 * wfun (g 0 + g 1) := by")
    A("  simp only [F, ptsN, sum2, Fin.sum_univ_three, Fin.isValue]")
    A("  norm_num")
    A("  -- `norm_num` evaluates the three pair coefficients `2/(3 \u2212 (j\u2212i))` and cancels the")
    A("  -- telescoping `ptsN` differences; whether it also closes the goal depends on the")
    A("  -- association it leaves, so `ring` is optional rather than required.")
    A("  try ring")
    A("")

    segs = [(l,u,'clear') for (l,u) in clear] + [(l,u,'bad',i) for i,(l,u) in enumerate(bad)]
    segs.sort()
    pos = X0
    for s in segs:
        assert s[0] == pos; pos = s[1]
    assert pos == S

    badstr = " ∨ ".join("(%s ≤ x ∧ x ≤ %s)" % (R(l), R(u)) for l,u in bad)
    A("/-- **The one-dimensional cover.**  Outside four short intervals around the first four")
    A("zeros of the kernel, `w ≥ c` outright.  `[0,1/2]` is the window of `wfun_window`; the")
    A("rest is the table. -/")
    A("lemma cover1 (x : ℝ) (h0 : 0 ≤ x) (hS : x ≤ %s) :" % R(S))
    A("    %s ≤ wfun x ∨ %s := by" % (CSTR, badstr))
    A("  rcases le_total x (1/2 : ℝ) with hw | hw")
    A("  · exact Or.inl (le_trans (by norm_num) (wfun_window x h0 hw))")
    for si, s in enumerate(segs):
        l, u = s[0], s[1]
        last = (si == len(segs)-1)
        hn = "hz%d" % (si+1)
        if not last:
            A("  rcases le_total x %s with %s | %s" % (R(u), hn, hn)); ind = "  · "
        else:
            A("  have %s : x ≤ %s := hS" % (hn, R(u))); ind = "  "
        if s[2] == 'clear':
            A("%sexact Or.inl (le_trans (by norm_num) (wc_%d x (by linarith) (by linarith)))"
              % (ind, idx[(l,u)]))
        else:
            j = s[3]
            expr = "⟨by linarith, by linarith⟩"
            if j < len(bad)-1: expr = "(Or.inl " + expr + ")"
            # `Or.inr Or.inr e` is application of `Or.inr` to two arguments, not
            # nesting: the parentheses are load-bearing.
            A("%sexact %s%s%s" % (ind, "Or.inr (" * (j+1), expr, ")" * (j+1)))
    A("")

    def emit_wfact(varname, expr, l, u, W, ind):
        pcs = quarter_pieces(l,u); out = []
        # When one cell covers the range on its own AND the constant asked for is that
        # cell's own constant -- 1393 of the 1443 leaf steps, every one where no
        # straddle forces a minimum -- the fact IS the cell lemma.  Writing
        # `le_trans (by norm_num) (wc_k ...)` there makes the elaborator postpone a
        # `by norm_num` against a metavariable until the second argument fixes it,
        # once per leaf step, for a `norm_num` that only ever proves `W <= W`.
        # Hand it the term directly instead.
        if len(pcs) == 1 and cellW[pcs[0]] == W:
            k = idx[pcs[0]]
            out.append("%shave %s : %s ≤ wfun %s := wc_%d %s (by linarith) (by linarith)"
                       % (ind, varname, R(W), expr, k, expr))
            return out
        out.append("%shave %s : %s ≤ wfun %s := by" % (ind, varname, R(W), expr))
        for t,(aa,bb) in enumerate(pcs):
            k = idx[(aa,bb)]
            if t < len(pcs)-1:
                out.append("%s  rcases le_total %s %s with hq%d | hq%d" % (ind, expr, R(bb), t, t))
                out.append("%s  · exact le_trans (by norm_num) (wc_%d %s (by linarith) (by linarith))"
                           % (ind, k, expr))
            else:
                out.append("%s  exact le_trans (by norm_num) (wc_%d %s (by linarith) (by linarith))"
                           % (ind, k, expr))
        return out

    def emit_node(node, ind, out):
        kind = node[0]
        if kind == 'pressure':
            out.append("%shave hp0 := wfun_nonneg x" % ind)
            out.append("%shave hp1 := wfun_nonneg y" % ind)
            out.append("%shave hp2 := wfun_nonneg (x+y)" % ind)
            out.append("%slinarith" % ind); return
        if kind == 'leaf':
            x0,x1,y0,y1 = node[1]
            out.extend(emit_wfact("hw0", "x", x0, x1, node[2], ind))
            out.extend(emit_wfact("hw1", "y", y0, y1, node[3], ind))
            out.extend(emit_wfact("hw2", "(x+y)", x0+y0, x1+y1, node[4], ind))
            out.append("%slinarith" % ind); return
        v = 'x' if kind == 'splitx' else 'y'
        out.append("%srcases le_total %s %s with hc | hc" % (ind, v, R(node[2])))
        for child in (node[3], node[4]):
            out.append("%s· " % ind)
            sub = []; emit_node(child, ind + "  ", sub)
            out[-1] = out[-1] + sub[0].lstrip()
            out.extend(sub[1:])

    pairnames = {}
    for (i,j,box,node) in trees:
        x0,x1,y0,y1 = box
        nm = "pair_%d_%d" % (i,j); pairnames[(i,j)] = nm
        # A box lemma is one declaration holding its whole bisection tree, so the tree
        # shares a single heartbeat budget.  B1 x B2 carries 453 of the 487 leaves --
        # the binding basin is there -- and overruns the default 200 000 about 4% of
        # the way in.  This is a compile-resource limit and nothing else: not an axiom,
        # absent from `#print axioms`, and set on the generated tables only, never on
        # the advertised theorems.
        A("set_option maxHeartbeats 10000000 in")
        A("/-- The box `B%d × B%d` of the two-dimensional table. -/" % (i+1,j+1))
        A("lemma %s (x y : ℝ) (hx1 : %s ≤ x) (hx2 : x ≤ %s)" % (nm, R(x0), R(x1)))
        A("    (hy1 : %s ≤ y) (hy2 : y ≤ %s) :" % (R(y0), R(y1)))
        A("    %s ≤ (1/(%d:ℝ)) * (x + y) + wfun x + wfun y + 2 * wfun (x + y) := by" % (CSTR, P))
        body = []; emit_node(node, "  ", body); L.extend(body); A("")

    A("/-- **The three-point certificate.**  This is the hypothesis `hCert` of")
    A("`Zeta23Ext.Bridge.n_point_bound` at `n = 3`, `c = %d/10⁶`, `p = %d`, proved. -/" % (cn, P))
    A("theorem three_point_cert :")
    A("    ∀ g : Fin (3-1) → ℝ, (∀ i, 0 ≤ g i) → %s ≤ F 3 %d g := by" % (CSTR, P))
    A("  intro g hg")
    A("  rw [F3_eq]")
    A("  have hx0 : (0:ℝ) ≤ g 0 := hg 0")
    A("  have hy0 : (0:ℝ) ≤ g 1 := hg 1")
    A("  set x : ℝ := g 0 with hxd")
    A("  set y : ℝ := g 1 with hyd")
    A("  have hn0 := wfun_nonneg x")
    A("  have hn1 := wfun_nonneg y")
    A("  have hn2 := wfun_nonneg (x+y)")
    A("  rcases le_total %s (x + y) with hS | hS" % R(S))
    A("  · linarith")
    A("  have hxS : x ≤ %s := by linarith" % R(S))
    A("  have hyS : y ≤ %s := by linarith" % R(S))
    A("  rcases cover1 x hx0 hxS with hcx | hbx")
    A("  · linarith")
    A("  rcases cover1 y hy0 hyS with hcy | hby")
    A("  · linarith")
    A("  rcases hbx with %s" % " | ".join("hbx%d" % t for t in range(len(bad))))
    A("  all_goals (rcases hby with %s)" % " | ".join("hby%d" % t for t in range(len(bad))))
    for i in range(len(bad)):
        for j in range(len(bad)):
            ii, jj = min(i,j), max(i,j)
            if (ii,jj) in pairnames:
                nm = pairnames[(ii,jj)]
                if i <= j:
                    A("  · exact %s x y hbx%d.1 hbx%d.2 hby%d.1 hby%d.2" % (nm, i, i, j, j))
                else:
                    A("  · have h := %s y x hby%d.1 hby%d.2 hbx%d.1 hbx%d.2" % (nm, j, j, i, i))
                    A("    rw [show y + x = x + y from by ring] at h")
                    A("    linarith")
            else:
                A("  · exfalso; linarith [hbx%d.1, hby%d.1]" % (i, j))
    A("")
    A("/-- `Phi_n 3 c m p` at the certificate's parameters, as an exact rational in `HD 1`. -/")
    A("theorem Phi_three : Phi_n 3 %s %d %d = (%d * HD 1 - %d) / %d := by" % (CSTR, m, P, a, b, d))
    A("  unfold Phi_n")
    A("  push_cast")
    A("  -- `1 \u2212 c(m\u2212(n\u22121))/m` and the right denominator are nonzero rationals, so the")
    A("  -- identity is a single cross-multiplication with `HD 1` left as an atom.")
    A("  rw [div_eq_div_iff (by norm_num) (by norm_num)]")
    A("  ring")
    A("")
    A("/-- **The three-point bound, unconditional.**  `Zeta23Ext.Bridge.n_point_bound` at")
    A("`n = 3` with its certificate hypothesis discharged by `three_point_cert`: for Mathlib's")
    A("`riemannZeta`, for every `ε > 0` and all large `T`, `(Φ₃ − ε) N(T,2T) ≤ N₀ˢ(T,2T)` with")
    A("`Φ₃ = (%d H − %d)/%d`, `H = HD 1 = 3/2 − (1/√2)cot(1/√2)`. -/" % (a, b, d))
    A("theorem three_point_bound :")
    A("    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,")
    A("      ((%d * HD 1 - %d) / %d - ε) * (Ncount T (2 * T) : ℝ)" % (a, b, d))
    A("        ≤ N0simple T (2 * T) := by")
    A("  rw [← Phi_three]")
    A("  exact n_point_bound 3 %s %d %d (by norm_num) (by norm_num) (by norm_num)" % (CSTR, m, P))
    A("    (by norm_num) three_point_cert (by norm_num)")
    A("")
    A("/-- **The same bound as a proportion.** -/")
    A("theorem three_point_bound_ratio :")
    A("    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,")
    A("      (%d * HD 1 - %d) / %d - ε" % (a, b, d))
    A("        ≤ (N0simple T (2 * T) : ℝ) / (Ncount T (2 * T) : ℝ) := by")
    A("  intro ε hε")
    A("  obtain ⟨T₁, hT₁⟩ := three_point_bound ε hε")
    A("  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp eventually_Ncount_pos")
    A("  refine ⟨max T₁ T₂, fun T hT => ?_⟩")
    A("  have h1 := hT₁ T (le_trans (le_max_left _ _) hT)")
    A("  have h2 := hT₂ T (le_trans (le_max_right _ _) hT)")
    A("  rw [le_div_iff₀ h2]")
    A("  exact h1")
    A("")
    A("/-! ### Standing axiom audit (idiom of `Zeta23Ext/Bridge/Defs.lean`) -/")
    A("")
    for nm in ("F3_eq","cover1","three_point_cert","Phi_three","three_point_bound",
               "three_point_bound_ratio"):
        A("#print axioms %s" % nm)
    A("")
    A("end Zeta23Ext.Bridge.ThreePoint")
    open(os.path.join(out, "ThreePoint", "Main.lean"), 'w').write("\n".join(L) + "\n")
    root = ["import ThreePoint.Base"] + ["import ThreePoint.Cells%d" % k for k in range(nmod)] \
           + ["import ThreePoint.Main", ""]
    open(os.path.join(out, "ThreePoint.lean"), 'w').write("\n".join(root))
    return dict(cn=cn, m=m, S=S, ncells=len(ivals), nmod=nmod, n2d=r['n2d'],
                nclear=len(clear), bad=bad, phi=(a,b,d))

if __name__ == '__main__':
    cn = int(sys.argv[1]) if len(sys.argv) > 1 else 1345
    here = os.path.dirname(os.path.abspath(__file__))
    info = emit(cn, os.path.join(here, "..", "..", "lean", "bridge"))
    H = 0.67250070367941164573
    a,b,d = info['phi']
    print("c = %d/10^6   m = %d   p = %d   cutoff S = %s" % (cn, info['m'], P, float(info['S'])))
    print("bad intervals: %s" % [(float(l), float(u)) for l,u in info['bad']])
    print("1-D cell lemmas %d in %d modules; clear segments %d; 2-D leaves %d"
          % (info['ncells'], info['nmod'], info['nclear'], info['n2d']))
    print("Phi_3 = (%d * HD 1 - %d)/%d = %.20f" % (a, b, d, (a*H - b)/d))
