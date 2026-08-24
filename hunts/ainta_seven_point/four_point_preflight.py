#!/usr/bin/env python3
"""Pre-flight validation of the generated four-point certificate, without Lean.

The Lean kernel is the authority on whether the certificate is *proved*.  This script
asks the cheaper question first: is it *arithmetically true*?  A wrong constant, a cell
that does not cover the range it is applied to, a gap in the one-dimensional cover, a
leaf whose six cell bounds do not add up to `c`, a router that sends a region to a chunk
lemma which does not cover it, a dispatch case that names the wrong box -- every one of
those costs an hour of CI to discover and seconds to discover here.

It is not a proof and it is not part of the trust chain.  Everything it checks the Lean
build checks again, rigorously.  It reads the *generated Lean*, not the generator's
in-memory tree, so it also catches emission bugs the generator cannot see.

  python3 hunts/ainta_seven_point/four_point_preflight.py

What it checks:

  1. every `wc_N` cell lemma's advertised constant `W` is a lower bound for `w = k^2` on
     its interval, against a 401-point sweep of the true function;
  2. `cover1`'s case chain is contiguous over `[0, c*p]`, every table segment lies inside
     the cell it invokes, and every table cell clears the cover level `3c/2` -- the level
     the adjacent-pair coefficient `2/3` can pay for, which is what makes a cleared gap
     close the certificate on its own;
  3. every leaf of every chunk lemma: the cell lemmas it invokes really do cover the
     `x`, `y`, `z`, `x+y`, `y+z` and `x+y+z` ranges the branch conditions force
     (including the leaves that split a straddling cell), and the linear combination its
     `linarith` is asked to close really is true;
  4. every router in `Boxes.lean` sends each region to a chunk lemma whose hypotheses
     cover it, and covers its whole box;
  5. the 64-case dispatch in `four_point_cert` names, for each triple of near-zero
     intervals, a box lemma that covers it -- or declares it dead, in which case the
     pressure cutoff really does kill it.
"""
from __future__ import annotations

import glob
import math
import os
import re
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
D = os.path.join(HERE, "lean-four-point", "FourPoint")

C = F(2310, 10 ** 6)      # the certificate constant
P = 2500                  # the pressure denominator
LEVEL = F(3, 2) * C       # the cover level: (2/3) * LEVEL = C
S = C * P                 # the pressure cutoff
COEF = {"x": F(2, 3), "y": F(2, 3), "z": F(2, 3),
        "x+y": F(1), "y+z": F(1), "x+y+z": F(2)}
SQ2 = math.sqrt(2.0)


def sinc(z: float) -> float:
    return 1.0 if z == 0.0 else math.sin(z) / z


def Kfun(x: float) -> float:
    return (sinc((SQ2 - 2 * math.pi * x) / 2) + sinc((SQ2 + 2 * math.pi * x) / 2)) / 2


K0 = Kfun(0.0)


def wfun(x: float) -> float:
    return (Kfun(x) / K0) ** 2


def num(s: str) -> F:
    s = s.replace(": ℝ", "").replace(":ℝ", "").replace("(", "").replace(")", "").strip()
    neg = s.startswith("-")
    if neg:
        s = s[1:]
    v = F(*map(int, s.split("/"))) if "/" in s else F(int(s))
    return -v if neg else v


problems = 0


def bad(msg: str) -> None:
    global problems
    problems += 1
    if problems <= 40:
        print("  " + msg)


# ---------------------------------------------------------------- 1. the cells
cells: dict[str, tuple[F, F, F]] = {}
for path in sorted(glob.glob(os.path.join(D, "Cells*.lean"))):
    for m in re.finditer(
        r"^theorem (wc_\d+) \(x : ℝ\) \(_?h₁ : \(([^)]*)\) ≤ x\) \(_?h₂ : x ≤ \(([^)]*)\)\) :"
        r"\s*\(([^)]*)\) ≤ wfun x",
            open(path, encoding="utf-8").read(), re.M):
        cells[m.group(1)] = (num(m.group(2)), num(m.group(3)), num(m.group(4)))

unsound = 0
for name, (lo, hi, W) in cells.items():
    if lo >= hi:
        bad(f"empty cell {name}: [{lo}, {hi}]")
        unsound += 1
        continue
    a, b = float(lo), float(hi)
    mn = min(wfun(a + (b - a) * i / 400) for i in range(401))
    if float(W) > mn:
        bad(f"unsound cell {name}: claims {float(W):.6e}, true min on [{a},{b}] is {mn:.6e}")
        unsound += 1
print(f"1. cells: {len(cells)} lemmas, {unsound} unsound")

# ------------------------------------------------------------- 2. the 1-D cover
cover = open(os.path.join(D, "Cover.lean"), encoding="utf-8").read()
cover = cover[cover.index("lemma cover1"):]
lines = [l for l in cover.splitlines() if l.strip()]
segments: list[tuple[F, F, str | None]] = []
exported: list[tuple[F, F]] = []
lo = F(0)
for i, ln in enumerate(lines):
    m = re.search(r"rcases le_total x \(([^)]*)\) with \w+ \| \w+", ln)
    if not m:
        continue
    hi = num(m.group(1))
    body = lines[i + 1]
    mc = re.search(r"\(wc_(\d+) x", body)
    if mc:
        segments.append((lo, hi, "wc_" + mc.group(1)))
    elif "wfun_window" in body:
        segments.append((lo, hi, "WINDOW"))
    elif "Or.inr" in body:
        segments.append((lo, hi, None))
        exported.append((lo, hi))
    else:
        bad("unparsed cover1 branch: " + body.strip())
    lo = hi
segments.append((lo, S, None))
exported.append((lo, S))

reach = F(0)
for a, b, name in segments:
    if a != reach:
        bad(f"cover1 gap: {float(reach)} .. {float(a)}")
    if a >= b:
        bad(f"cover1 empty segment [{float(a)}, {float(b)}]")
    reach = b
    if name and name != "WINDOW":
        clo, chi, W = cells[name]
        if not (clo <= a and b <= chi):
            bad(f"cover1 segment [{float(a)},{float(b)}] outside {name} [{float(clo)},{float(chi)}]")
        if W < LEVEL:
            bad(f"cover1 cell {name} gives {float(W)} < level 3c/2 = {float(LEVEL)}")
if reach != S:
    bad(f"cover1 stops at {float(reach)}, not at the cutoff {float(S)}")
declared = re.search(r"    \(([^)]*)\) ≤ wfun x ∨", cover)
if declared is None or num(declared.group(1)) != LEVEL:
    bad("cover1 does not advertise the level 3c/2")
print(f"2. cover1: {len(segments)} segments over [0, {float(S)}], "
      f"{sum(1 for s in segments if s[2] and s[2] != 'WINDOW')} table cells, "
      f"{sum(1 for s in segments if s[2] == 'WINDOW')} window, "
      f"{len(exported)} near-zero intervals at level {float(LEVEL)}: "
      f"{[(float(a), float(b)) for a, b in exported]}")

# --------------------------------------------------------------- the tokenizer
BULLET, SPLIT, HAVE, CELL, TAC = range(5)


def tokenize(src: str):
    toks = []
    for raw in src.splitlines():
        if not raw.strip():
            continue
        ind = len(raw) - len(raw.lstrip())
        txt = raw.lstrip()
        while txt.startswith("· "):
            toks.append((ind, BULLET, None))
            ind += 2
            txt = txt[2:]
            while txt.startswith(" "):
                ind += 1
                txt = txt[1:]
        # a box split carries `with hc | hc`; a straddle split inside a `have ... := by`
        # carries `with hqNN | hqNN`, and must not be read as a box split
        m = re.match(r"rcases le_total ([xyz]) \(([^)]*)\) with hc \| hc", txt)
        if m:
            toks.append((ind, SPLIT, (m.group(1), num(m.group(2)))))
            continue
        m = re.match(r"have (hw\d+) : \(([^)]*)\) ≤ wfun (\(?[xyz +]+\)?) :=(.*)$", txt)
        if m:
            tgt = m.group(3).replace(" ", "").replace("(", "").replace(")", "")
            toks.append((ind, HAVE, (num(m.group(2)), tgt)))
            d = re.match(r"\s*(wc_\d+)\b", m.group(4))
            if d:
                toks.append((ind + 1, CELL, d.group(1)))
            continue
        m = re.search(r"\((wc_\d+) \(?[xyz +]+\)?", txt)
        if m:
            toks.append((ind, CELL, m.group(1)))
            continue
        m = re.match(r"exact (ch_\d+) x y z", txt)
        if m:
            toks.append((ind, TAC, ("CALL", m.group(1))))
            continue
        if re.match(r"(n?linarith|rcases|exact|have )", txt):
            toks.append((ind, TAC, ("OTHER", txt)))
    return toks


def owns(toks, i):
    ind = toks[i][0]
    j = i + 1
    while j < len(toks) and toks[j][0] > ind:
        j += 1
    return j


def walk(toks, lo, hi, rng, out):
    """rng: dict var -> (a, b).  Appends (rng, payload) for each leaf."""
    idx = [k for k in range(lo, hi) if toks[k][1] == SPLIT]
    if idx:
        base = min(toks[k][0] for k in range(lo, hi))
        top = [k for k in idx if toks[k][0] == base]
        if top:
            k = top[0]
            var, thr = toks[k][2]
            bl = [j for j in range(k + 1, hi) if toks[j][1] == BULLET and toks[j][0] == base]
            if len(bl) >= 2:
                b1, b2 = bl[0], bl[1]
                r1 = dict(rng); r1[var] = (rng[var][0], min(rng[var][1], thr))
                r2 = dict(rng); r2[var] = (max(rng[var][0], thr), rng[var][1])
                walk(toks, b1 + 1, owns(toks, b1), r1, out)
                walk(toks, b2 + 1, owns(toks, b2), r2, out)
                return
    hw: list = []
    call = None
    for k in range(lo, hi):
        if toks[k][1] == HAVE:
            hw.append([toks[k][2][0], toks[k][2][1], []])
        elif toks[k][1] == CELL and hw:
            hw[-1][2].append(toks[k][2])
        elif toks[k][1] == TAC and toks[k][2][0] == "CALL":
            call = toks[k][2][1]
    out.append((rng, hw, call))


def forced(rng, tgt):
    if tgt == "x+y":
        return (rng["x"][0] + rng["y"][0], rng["x"][1] + rng["y"][1])
    if tgt == "y+z":
        return (rng["y"][0] + rng["z"][0], rng["y"][1] + rng["z"][1])
    if tgt == "x+y+z":
        return (rng["x"][0] + rng["y"][0] + rng["z"][0],
                rng["x"][1] + rng["y"][1] + rng["z"][1])
    return rng[tgt]


def check_leaf(name, rng, hw):
    Ws: dict[str, F] = {}
    for W, tgt, cns in hw:
        if tgt not in COEF:
            bad(f"{name}: leaf bounds an unexpected expression {tgt}")
            continue
        if not cns or any(c not in cells for c in cns):
            bad(f"{name}: leaf invokes unknown cell {cns}")
            continue
        r0, r1 = forced(rng, tgt)
        ivs = sorted((cells[c][0], cells[c][1], c) for c in cns)
        r = ivs[0][0]
        if r > r0:
            bad(f"{name}: {cns} start at {float(r)}, above {tgt} lo {float(r0)}")
        for a2, b2, c2 in ivs:
            if a2 > r:
                bad(f"{name}: gap before {c2} at {float(r)}")
                break
            r = max(r, b2)
        if r < r1:
            bad(f"{name}: {cns} reach {float(r)}, below {tgt} hi {float(r1)}")
        weakest = min(cells[c][2] for c in cns)
        if W > weakest:
            bad(f"{name}: leaf claims {float(W)} > weakest of {cns} = {float(weakest)}")
        Ws[tgt] = W
    lhs = F(rng["x"][0] + rng["y"][0] + rng["z"][0], P)
    for t, co in COEF.items():
        lhs += co * Ws.get(t, F(0))
    if lhs < C:
        bad(f"{name}: leaf x∈[{float(rng['x'][0])},{float(rng['x'][1])}] "
            f"y∈[{float(rng['y'][0])},{float(rng['y'][1])}] "
            f"z∈[{float(rng['z'][0])},{float(rng['z'][1])}] gives {float(lhs):.9e} < c")


HDR = re.compile(
    r"lemma (ch_\d+|box_\d+_\d+_\d+) \(x y z : ℝ\) \(hx1 : \(([^)]*)\) ≤ x\) \(hx2 : x ≤ \(([^)]*)\)\)\s*"
    r"\(hy1 : \(([^)]*)\) ≤ y\) \(hy2 : y ≤ \(([^)]*)\)\)\s*"
    r"\(hz1 : \(([^)]*)\) ≤ z\) \(hz2 : z ≤ \(([^)]*)\)\) :")


def declarations(path):
    src = open(path, encoding="utf-8").read()
    out = []
    ms = list(HDR.finditer(src))
    for i, m in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else src.index("\nend Zeta23Ext")
        body = src[src.index(":= by", m.end()) + len(":= by"):end]
        box = {"x": (num(m.group(2)), num(m.group(3))),
               "y": (num(m.group(4)), num(m.group(5))),
               "z": (num(m.group(6)), num(m.group(7)))}
        out.append((m.group(1), box, body))
    return out


# ------------------------------------------------------------- 3. the chunks
chunkbox: dict[str, dict] = {}
nleaf = 0
before = problems
for path in sorted(glob.glob(os.path.join(D, "Chunks*.lean"))):
    for name, box, body in declarations(path):
        chunkbox[name] = box
        toks = tokenize(body)
        leaves: list = []
        walk(toks, 0, len(toks), box, leaves)
        for rng, hw, call in leaves:
            nleaf += 1
            check_leaf(name, rng, hw)
print(f"3. chunks: {len(chunkbox)} lemmas, {nleaf} leaves, {problems - before} problems")

# ------------------------------------------------------------- 4. the routers
before = problems
routers: dict[str, dict] = {}
nroute = 0
for name, box, body in declarations(os.path.join(D, "Boxes.lean")):
    routers[name] = box
    toks = tokenize(body)
    regions: list = []
    walk(toks, 0, len(toks), box, regions)
    for rng, hw, call in regions:
        nroute += 1
        if call is None:
            bad(f"{name}: a router region does not end in a chunk call")
            continue
        cb = chunkbox.get(call)
        if cb is None:
            bad(f"{name}: routes to unknown chunk {call}")
            continue
        for v in "xyz":
            if not (cb[v][0] <= rng[v][0] and rng[v][1] <= cb[v][1]):
                bad(f"{name}: region {v}∈[{float(rng[v][0])},{float(rng[v][1])}] "
                    f"outside {call} {v}∈[{float(cb[v][0])},{float(cb[v][1])}]")
print(f"4. routers: {len(routers)} boxes, {nroute} regions, {problems - before} problems")

# ------------------------------------------------------- 5. the 64-case dispatch
before = problems
main = open(os.path.join(D, "Main.lean"), encoding="utf-8").read()
cert = main[main.index("private lemma cert_core"):main.index("theorem four_point_cert")]
cases = []
for ln in cert.splitlines():
    t = ln.strip()
    m = re.match(r"· exact (box_\d+_\d+_\d+) x y z", t)
    if m:
        cases.append(("direct", m.group(1)))
        continue
    m = re.match(r"· have h := (box_\d+_\d+_\d+) z y x", t)
    if m:
        cases.append(("flip", m.group(1)))
        continue
    if t.startswith("· exfalso"):
        cases.append(("dead", None))
nb = len(exported)
if len(cases) != nb ** 3:
    bad(f"dispatch has {len(cases)} cases, expected {nb ** 3}")
else:
    t = 0
    for i in range(nb):
        for j in range(nb):
            for k in range(nb):
                kind, nm = cases[t]
                t += 1
                lows = exported[i][0] + exported[j][0] + exported[k][0]
                if kind == "dead":
                    if lows < S:
                        bad(f"dispatch ({i},{j},{k}) declared dead but its corner "
                            f"{float(lows)} is below the cutoff {float(S)}")
                    continue
                if lows >= S:
                    bad(f"dispatch ({i},{j},{k}) calls {nm} but the pressure cutoff kills it")
                want = (k, j, i) if kind == "flip" else (i, j, k)
                if nm != "box_%d_%d_%d" % want:
                    bad(f"dispatch ({i},{j},{k}) {kind} calls {nm}, expected box_%d_%d_%d" % want)
                    continue
                rb = routers.get(nm)
                if rb is None:
                    bad(f"dispatch ({i},{j},{k}) calls unknown {nm}")
                    continue
                order = (k, j, i) if kind == "flip" else (i, j, k)
                for v, ix in zip("xyz", order):
                    if rb[v] != exported[ix]:
                        bad(f"dispatch ({i},{j},{k}): {nm} {v} is "
                            f"[{float(rb[v][0])},{float(rb[v][1])}], not B{ix + 1}")
print(f"5. dispatch: {len(cases)} cases "
      f"({sum(1 for c in cases if c[0] == 'dead')} dead by pressure), "
      f"{problems - before} problems")

print(f"total: {len(cells)} cell lemmas, {nleaf} leaves, {len(chunkbox)} chunks, "
      f"{len(routers)} boxes, {problems} problems")
sys.exit(1 if problems else 0)
