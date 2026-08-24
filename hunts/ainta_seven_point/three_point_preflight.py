#!/usr/bin/env python3
"""Pre-flight validation of the generated three-point certificate, without Lean.

The Lean kernel is the authority on whether the certificate is *proved*.  This
script is a different question, asked first because it is cheap: is the
certificate *arithmetically true*?  A wrong constant, a cell that does not cover
the range it is applied to, a gap in the one-dimensional cover, a leaf whose
three cell bounds do not actually add up to `c` -- every one of those is
something a Lean build discovers after an hour, and this discovers in seconds.

It is not a proof and it is not part of the trust chain.  It is a filter, so that
a CI round is not spent finding an error that float arithmetic could have found.
Everything it checks is checked again, rigorously, by the Lean build.

  python3 hunts/ainta_seven_point/three_point_preflight.py

What it checks:

  1. every `wc_N` cell lemma's advertised constant `W` is a lower bound for
     `w = k^2` on its interval, against a 400-point sweep of the true function;
  2. `cover1`'s case chain is contiguous over `[0, 807/200]`, every table
     segment lies inside the cell it invokes, and every table cell clears `c`;
  3. every leaf of every two-dimensional box: the cell lemmas it invokes really
     do cover the `x`, `y` and `x+y` ranges the branch conditions force
     (including the leaves that split a straddling cell in two), and the linear
     combination its `linarith` is asked to close really is true.
"""
from __future__ import annotations

import glob
import math
import os
import re
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
D = os.path.join(HERE, "lean-three-point", "ThreePoint")

C = F(1345, 10 ** 6)      # the certificate constant
P = 3000                  # the pressure denominator
S = F(807, 200)           # the pressure cutoff c*p, rounded up to a rational
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
        bad(f"unsound cell {name}: claims {float(W):.6e}, true min on "
            f"[{a},{b}] is {mn:.6e}")
        unsound += 1
print(f"1. cells: {len(cells)} lemmas, {unsound} unsound")

# ------------------------------------------------------------- 2. the 1-D cover
main = open(os.path.join(D, "Main.lean"), encoding="utf-8").read()
cover = main[main.index("lemma cover1"):main.index("lemma pair_0_0")]
lines = [l for l in cover.splitlines() if l.strip()]
segments: list[tuple[F, F, str | None]] = []
lo = F(0)
exported: list[tuple[F, F]] = []
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
            bad(f"cover1 segment [{float(a)},{float(b)}] outside {name} "
                f"[{float(clo)},{float(chi)}]")
        if W < C:
            bad(f"cover1 cell {name} gives {float(W)} < c = {float(C)}")
if reach != S:
    bad(f"cover1 stops at {float(reach)}, not at the cutoff {float(S)}")
print(f"2. cover1: {len(segments)} segments over [0, {float(S)}], "
      f"{sum(1 for s in segments if s[2] and s[2] != 'WINDOW')} table cells, "
      f"{sum(1 for s in segments if s[2] == 'WINDOW')} window, "
      f"{len(exported)} near-zero intervals "
      f"{[(float(a), float(b)) for a, b in exported]}")

# ------------------------------------------------------------ 3. the 2-D boxes
BULLET, RCASES, HAVE, CELL, TAC = range(5)


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
        m = re.match(r"rcases le_total ([xy]) \(([^)]*)\) with \w+ \| \w+", txt)
        if m:
            toks.append((ind, RCASES, (m.group(1), num(m.group(2)))))
            continue
        m = re.match(r"have hw\d+ : \(([^)]*)\) ≤ wfun \(?([xy+]+)\)? :=(.*)$", txt)
        if m:
            toks.append((ind, HAVE, (num(m.group(1)), m.group(2))))
            # the direct form `:= wc_k e (by linarith) (by linarith)` carries its cell
            # on the same line; the `:= by` form carries it on the lines that follow
            d = re.match(r"\s*(wc_\d+)\b", m.group(3))
            if d:
                toks.append((ind + 1, CELL, d.group(1)))
            continue
        m = re.search(r"\((wc_\d+) \(?([xy+]+)\)?", txt)
        if m:
            toks.append((ind, CELL, m.group(1)))
            continue
        if re.match(r"(n?linarith|exact|have )", txt):
            toks.append((ind, TAC, txt))
    return toks


def owns(toks, i):
    ind = toks[i][0]
    j = i + 1
    while j < len(toks) and toks[j][0] > ind:
        j += 1
    return j


def walk(toks, lo, hi, xr, yr, out):
    rcs = [k for k in range(lo, hi) if toks[k][1] == RCASES]
    if rcs:
        base = min(toks[k][0] for k in range(lo, hi))
        top = [k for k in rcs if toks[k][0] == base]
        if top:
            k = top[0]
            var, thr = toks[k][2]
            bl = [j for j in range(k + 1, hi)
                  if toks[j][1] == BULLET and toks[j][0] == base]
            if len(bl) >= 2:
                b1, b2 = bl[0], bl[1]
                if var == "x":
                    walk(toks, b1 + 1, owns(toks, b1), (xr[0], min(xr[1], thr)), yr, out)
                    walk(toks, b2 + 1, owns(toks, b2), (max(xr[0], thr), xr[1]), yr, out)
                else:
                    walk(toks, b1 + 1, owns(toks, b1), xr, (yr[0], min(yr[1], thr)), out)
                    walk(toks, b2 + 1, owns(toks, b2), xr, (max(yr[0], thr), yr[1]), out)
                return
    hw = []
    for k in range(lo, hi):
        if toks[k][1] == HAVE:
            hw.append([toks[k][2][0], toks[k][2][1], []])
        elif toks[k][1] == CELL and hw:
            hw[-1][2].append(toks[k][2])
    out.append((xr, yr, hw))


BOXES = {
    "pair_0_0": (F(65, 64), F(71, 64), F(65, 64), F(71, 64)),
    "pair_0_1": (F(65, 64), F(71, 64), F(31, 16), F(17, 8)),
    "pair_0_2": (F(65, 64), F(71, 64), F(23, 8), F(203, 64)),
    "pair_1_1": (F(31, 16), F(17, 8), F(31, 16), F(17, 8)),
}
MARKS = ["lemma pair_0_0", "lemma pair_0_1", "lemma pair_0_2", "lemma pair_1_1",
         "theorem three_point_cert"]
total = 0
for k, mark in enumerate(MARKS[:-1]):
    name = mark.split()[1]
    src = main[main.index(mark):main.index(MARKS[k + 1])]
    src = src[src.index("2 * wfun (x + y) := by") + len("2 * wfun (x + y) := by"):]
    leaves: list = []
    walk(tokenize(src), 0, len(tokenize(src)), (BOXES[name][0], BOXES[name][1]),
         (BOXES[name][2], BOXES[name][3]), leaves)
    before = problems
    for (xa, xb), (ya, yb), hws in leaves:
        Ws: dict[str, F] = {}
        for W, tgt, cns in hws:
            if not cns or any(c not in cells for c in cns):
                bad(f"{name}: leaf invokes unknown cell {cns}")
                continue
            rng = {"x": (xa, xb), "y": (ya, yb), "x+y": (xa + ya, xb + yb)}[tgt]
            ivs = sorted((cells[c][0], cells[c][1], c) for c in cns)
            r = ivs[0][0]
            if r > rng[0]:
                bad(f"{name}: {cns} start at {float(r)}, above {tgt} lo {float(rng[0])}")
            for a2, b2, c2 in ivs:
                if a2 > r:
                    bad(f"{name}: gap before {c2} at {float(r)}")
                    break
                r = max(r, b2)
            if r < rng[1]:
                bad(f"{name}: {cns} reach {float(r)}, below {tgt} hi {float(rng[1])}")
            weakest = min(cells[c][2] for c in cns)
            if W > weakest:
                bad(f"{name}: leaf claims {float(W)} > weakest of {cns} = {float(weakest)}")
            Ws[tgt] = W
        lhs = F(xa + ya, P) + Ws.get("x", F(0)) + Ws.get("y", F(0)) + 2 * Ws.get("x+y", F(0))
        if lhs < C:
            bad(f"{name}: leaf x∈[{float(xa)},{float(xb)}] y∈[{float(ya)},{float(yb)}] "
                f"gives {float(lhs):.9e} < c")
    print(f"3. {name}: {len(leaves)} leaves, {problems - before} problems")
    total += len(leaves)

print(f"total: {len(cells)} cell lemmas, {total} leaves, {problems} problems")
sys.exit(1 if problems else 0)
