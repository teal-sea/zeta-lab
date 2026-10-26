"""Emit the generated Lean files of the piece `horizontal_legs` (hunt #137).

Run from the repository root:

    .venv/bin/python hunts/rh_height_lean/gen_legs.py              # write the four files
    .venv/bin/python hunts/rh_height_lean/gen_legs.py --check      # compare, write nothing
    .venv/bin/python hunts/rh_height_lean/gen_legs.py --report     # also print mpmath values
    .venv/bin/python hunts/rh_height_lean/gen_legs.py --out DIR    # write into DIR instead

The files are `lean/RHHeight/LegsBottom.lean` (the leg `[1/2, 2] + 3i`),
`lean/RHHeight/LegsTop1.lean` and `LegsTop2.lean` (the leg `[1/2, 2] + 52i`) and
`lean/RHHeight/LegsArg.lean` (the two points `1/2 + 3i` and `1/2 + 52i`). Each segment
`[a, b] + iy` gets one table of term boxes `m^(-(a + iy))`, `m <= N`, and one rational
inequality `0 < segSlack`, which `RHHeight.Legs.re_pos_of_segment` (in
`lean/RHHeight/LegSupport.lean`) turns into `Re zeta(sigma + iy) > 0` for every sigma in
`[a, b]`. Each point gets a table and the box `RHHeight.Legs.zeta_mem_pointBox` proves to
contain zeta there.

The term boxes are computed by the lab's bit-exact rational mirror of the interval layer
(`scripts/61_rung3_mirror.py`): an exp tower (`dirichletTermBox2`) for every prime, the
coarsened product of two earlier boxes for every composite, and the exact box `1` for
`m = 1`, as in hunts #132 and #133. Nothing here is trusted by the proof: every literal box
is checked by the kernel against the Lean definition (`decide +kernel`), and so is every
inequality. This script also evaluates `segSlack` and the point boxes in exact rational
arithmetic, with the same definitions as the Lean file, and refuses to write a file whose
inequalities do not hold with the margin `MARGIN`.

The partitions were found by a dynamic program over the dyadic grid of step 1/64 (scratch
work, not kept): fewest prime towers, every segment's slack above `MARGIN`, truncations `N`
from 2 to 16. The mpmath values printed by `--report` are measurements, one route, floating
point, and play no part in the proof.
"""
from __future__ import annotations

import argparse
import importlib.util
import math
import sys
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
LEAN_DIR = HERE / "lean" / "RHHeight"

#: Term-box parameters `dirichletTermBox2 nLog nExp p kL kE`, hunt #133's choice.
NLOG, NEXP, P, KE = 36, 16, 80, 8
#: The Taylor order of `RHHeight.Legs.logTab` (`Interval.logQ 20 (kOf n) n`).
LOG_ORDER = 20
#: Every segment slack and every point-box margin must exceed this.
MARGIN = F(1, 20)

#: (height, [(a, b, N), ...]) for the two legs; the breakpoints tile [1/2, 2].
BOTTOM = (F(3), [(F(1, 2), F(43, 64), 2), (F(43, 64), F(19, 16), 2), (F(19, 16), F(2), 2)])
TOP = (F(52), [(F(1, 2), F(39, 64), 12), (F(39, 64), F(3, 4), 12), (F(3, 4), F(15, 16), 12),
               (F(15, 16), F(9, 8), 10), (F(9, 8), F(23, 16), 10), (F(23, 16), F(2), 10)])
#: (tag, x, y, N, the stated lower bound of arg zeta(x + iy)).
POINTS = [("Arg3", F(1, 2), F(3), 4, F(-1, 5)), ("Arg52", F(1, 2), F(52), 28, F(-1, 3))]


def load_mirror():
    """`scripts/61_rung3_mirror.py`, imported read-only (its name starts with a digit)."""
    path = ROOT / "scripts" / "61_rung3_mirror.py"
    spec = importlib.util.spec_from_file_location("rung3_mirror_for_legs", path)
    mod = importlib.util.module_from_spec(spec)
    old = sys.dont_write_bytecode
    sys.dont_write_bytecode = True
    try:
        spec.loader.exec_module(mod)
    finally:
        sys.dont_write_bytecode = old
    return mod


def spf(m: int) -> int:
    """Smallest prime factor."""
    f = 2
    while f * f <= m:
        if m % f == 0:
            return f
        f += 1
    return m


# ---------------------------------------------------------------------------
# The Lean definitions of LegSupport.lean, in exact rational arithmetic
# ---------------------------------------------------------------------------


def table(M, x: F, y: F, N: int) -> dict:
    """Term boxes for m = 0..N at s = x + iy, the way the Lean file builds them."""
    S = M.cexact(x, y)
    boxes = {0: M.cexact(0, 0), 1: M.cexact(1, 0)}
    for m in range(2, N + 1):
        f = spf(m)
        if f == m:
            arg = M.cmul(M.cneg(S), M.C(M.logQ(NLOG, m.bit_length(), F(m)), M.iexact(0)))
            if not M.normBound(arg) <= 2 ** KE:
                raise ValueError(f"normBound {float(M.normBound(arg))} > 2^{KE} at m = {m}")
            boxes[m] = M.dirichletTermBox2(NLOG, NEXP, P, m.bit_length(), KE, m, S)
        else:
            boxes[m] = M.ccoarsen(P, M.cmul(boxes[f], boxes[m // f]))
    return boxes


def towers(N: int) -> int:
    return sum(1 for m in range(2, N + 1) if spf(m) == m)


def c_g(N: int, x: F, y: F) -> tuple[F, F]:
    """`cReG N x y`, `cImG N x y`."""
    d = (x - 1) ** 2 + y ** 2
    return (N * (x - 1) / d + F(1, 2) + x / (12 * N), -(N * y) / d + y / (12 * N))


def main_box(M, boxes: dict, N: int, x: F, y: F):
    """`mainBoxG T N x y`."""
    acc = M.cexact(0, 0)
    for m in range(N):
        acc = M.cadd(acc, boxes[m])
    cre, cim = c_g(N, x, y)
    return M.cadd(acc, M.cmul(boxes[N], M.cexact(cre, cim)))


def norm_up(B) -> F:
    """`normUp B`, the octagon bound."""
    X = max(abs(B.re.lo), abs(B.re.hi))
    Y = max(abs(B.im.lo), abs(B.im.hi))
    return max(X, Y) + F(5, 12) * min(X, Y)


def log_tab(M, n: int) -> F:
    """`logTab n`; `kOf n` is the bit length of `n` for `n < 64`."""
    if n < 2:
        return F(0)
    return M.logQ(LOG_ORDER, n.bit_length(), F(n)).hi


def q4g(x: F, y: F) -> F:
    return (x * x + y * y) * ((x + 1) ** 2 + y * y) * ((x + 2) ** 2 + y * y) * ((x + 3) ** 2 + y * y)


def sqrt_up(q: F, den: int = 10 ** 4) -> F:
    """A rational `P >= 0` with `P^2 >= q` and a short decimal denominator."""
    r = F(math.isqrt(math.ceil(q * den * den)) + 1, den)
    assert r * r >= q
    return r


def lip_l(M, boxes: dict, N: int, b: F, y: F) -> F:
    """`lipL T N b y`."""
    s = sum((log_tab(M, n) * norm_up(boxes[n]) for n in range(N)), F(0))
    C1 = F(N) / y + F(1, 2) + (b + y) / (12 * N)
    C2 = F(N) / (y * y) + F(1, 12 * N)
    return s + norm_up(boxes[N]) * (log_tab(M, N) * C1 + C2)


def rem_r(boxes: dict, N: int, a: F, Pb: F) -> F:
    """`remR T N a P`."""
    return Pb * norm_up(boxes[N - 1]) / ((F(N) - 1) ** 3 * 720 * (a + 3))


def segment(M, a: F, b: F, y: F, N: int) -> dict:
    boxes = table(M, a, y, N)
    B = main_box(M, boxes, N, a, y)
    Pb = sqrt_up(q4g(b, y))
    L = lip_l(M, boxes, N, b, y)
    R = rem_r(boxes, N, a, Pb)
    slack = B.re.lo - (b - a) * L - R
    return {"a": a, "b": b, "y": y, "N": N, "boxes": boxes, "P": Pb, "main_lo": B.re.lo,
            "L": L, "R": R, "slack": slack}


def point(M, x: F, y: F, N: int, lower: F) -> dict:
    boxes = table(M, x, y, N)
    B = main_box(M, boxes, N, x, y)
    Pb = sqrt_up(q4g(x, y))
    e = rem_r(boxes, N, x, Pb)
    re_lo, re_hi = B.re.lo - e, B.re.hi + e
    im_lo, im_hi = B.im.lo - e, B.im.hi + e
    ratio = im_lo / re_lo
    return {"x": x, "y": y, "N": N, "boxes": boxes, "P": Pb, "e": e, "re": (re_lo, re_hi),
            "im": (im_lo, im_hi), "ratio": ratio, "lower": lower,
            "ok": re_lo > 0 and im_hi <= 0 and ratio >= lower,
            "margin": ratio - lower}


# ---------------------------------------------------------------------------
# Rendering
# ---------------------------------------------------------------------------


def q(x: F) -> str:
    x = F(x)
    if x.denominator == 1:
        return f"({x.numerator} : ℚ)"
    return f"({x.numerator} / {x.denominator} : ℚ)"


HEADER = """module

public import RHHeight.LegSupport

@[expose] public section

/-!
# {title} (generated)

Generated by `hunts/rh_height_lean/gen_legs.py` from the lab's bit-exact rational mirror of
the interval layer; do not edit by hand. Every literal is checked by the kernel against the
Lean definition (`decide +kernel`): primes against `dirichletTermBox2` with `nLog = {nlog}`,
`nExp = {nexp}`, `p = {p}`, `kE = {ke}`, `kL` the bit length of `m`; composites against the
`{p}`-bit coarsened product of the boxes of their smallest prime factor and cofactor. The
inequalities are decided by the kernel too. The analysis is `RHHeight/LegSupport.lean`.
-/

open Complex ZetaLean ZetaLean.ComplexInterval HardyFirstZero RHHeight.Legs
"""


def render_table(lines: list, boxes: dict, x: F, y: F, N: int) -> None:
    pt = f"ptQ {q(x)} {q(y)}"
    lines.append(f"/-- Term boxes `m^(-s)` at `s = {x} + {y} i`, `1 ≤ m ≤ {N}`. -/")
    lines.append("def tab : ℕ → ComplexInterval")
    lines.append("  | 1 => ComplexInterval.exact 1 0")
    for m in range(2, N + 1):
        bx = boxes[m]
        lines.append(f"  | {m} => lit {q(bx.re.lo)} {q(bx.re.hi)}")
        lines.append(f"      {q(bx.im.lo)} {q(bx.im.hi)} (by norm_num) (by norm_num)")
    lines.append("  | _ => ComplexInterval.exact 0 0")
    lines.append("")
    lines.append("theorem tab_mem_1 :")
    lines.append(f"    (tab 1).contains (((1 : ℕ) : ℂ) ^ (-{pt})) :=")
    lines.append("  HardyTenZeros.contains_one_cpow _")
    lines.append("")
    for m in range(2, N + 1):
        f = spf(m)
        if f == m:
            kl = m.bit_length()
            lines.append(f"theorem tab_eq_{m} :")
            lines.append(f"    dirichletTermBox2 {NLOG} {NEXP} {P} {kl} {KE} {m} "
                         f"(ComplexInterval.exact {q(x)} {q(y)}) = tab {m} := by")
            lines.append("  decide +kernel")
            lines.append("")
            lines.append(f"theorem tab_mem_{m} :")
            lines.append(f"    (tab {m}).contains ((({m} : ℕ) : ℂ) ^ (-{pt})) := by")
            lines.append(f"  rw [← tab_eq_{m}]")
            lines.append("  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)")
            lines.append("    (exact_contains_ptQ _ _) (by norm_num) (by norm_num) (by decide +kernel)")
            lines.append("")
        else:
            g = m // f
            lines.append(f"theorem tab_eq_{m} : ((tab {f}).mul (tab {g})).coarsen {P} = tab {m} := by")
            lines.append("  decide +kernel")
            lines.append("")
            lines.append(f"theorem tab_mem_{m} :")
            lines.append(f"    (tab {m}).contains ((({m} : ℕ) : ℂ) ^ (-{pt})) := by")
            lines.append(f"  rw [← tab_eq_{m}]")
            lines.append(f"  exact HardyTenZeros.contains_cpow_mul_coarsen {P} tab_mem_{f} tab_mem_{g}")
            lines.append("")
    lines.append(f"theorem tab_mem : ∀ m < {N} + 1,")
    lines.append(f"    (tab m).contains ((m : ℂ) ^ (-{pt})) := by")
    lines.append("  intro m hm")
    lines.append("  interval_cases m")
    lines.append("  · rw [Nat.cast_zero, zero_cpow (neg_ne_zero.mpr (ptQ_ne_zero _ (by norm_num)))]")
    lines.append("    exact contains_zero")
    for m in range(1, N + 1):
        lines.append(f"  · exact tab_mem_{m}")
    lines.append("")


def render_legs(title: str, height: F, segs: list, first_index: int) -> str:
    lines = [HEADER.format(title=title, nlog=NLOG, nexp=NEXP, p=P, ke=KE)]
    for k, d in enumerate(segs, start=first_index):
        a, b, N, y = d["a"], d["b"], d["N"], height
        ns = f"RHHeight.Legs.H{height.numerator}S{k}"
        lines.append(f"namespace {ns}")
        lines.append("")
        lines.append("set_option maxRecDepth 100000")
        lines.append("")
        render_table(lines, d["boxes"], a, y, N)
        lines.append(f"/-- The slack of the segment `[{a}, {b}] + {y} i` with `N = {N}` is positive"
                     f" (exactly {float(d['slack']):.6f}, rounded here). -/")
        lines.append("theorem slack_pos :")
        lines.append(f"    0 < segSlack tab {N} {q(a)} {q(b)} {q(y)} {q(d['P'])} := by")
        lines.append("  decide +kernel")
        lines.append("")
        lines.append(f"/-- `Re ζ(σ + {y} i) > 0` for `{a} ≤ σ ≤ {b}`. -/")
        lines.append(f"theorem seg : ∀ σ : ℝ, ({q(a)} : ℝ) ≤ σ → σ ≤ ({q(b)} : ℝ) →")
        lines.append(f"    0 < (riemannZeta ((σ : ℂ) + ({q(y)} : ℂ) * I)).re :=")
        lines.append(f"  re_pos_of_segment (a := {q(a)}) (b := {q(b)}) (y := {q(y)}) (by norm_num) (by norm_num)")
        lines.append(f"    (N := {N}) (by norm_num) (by norm_num) tab_mem (P := {q(d['P'])}) (by norm_num)")
        lines.append("    (by decide +kernel) slack_pos")
        lines.append("")
        lines.append(f"end {ns}")
        lines.append("")
    return "\n".join(lines)


def render_points(pts: list) -> str:
    lines = [HEADER.format(title="Boxes for zeta at 1/2 + 3i and 1/2 + 52i, and the arguments there",
                           nlog=NLOG, nexp=NEXP, p=P, ke=KE)]
    for tag, d in pts:
        x, y, N = d["x"], d["y"], d["N"]
        ns = f"RHHeight.Legs.{tag}"
        lo = d["lower"]
        lines.append(f"namespace {ns}")
        lines.append("")
        lines.append("set_option maxRecDepth 100000")
        lines.append("")
        render_table(lines, d["boxes"], x, y, N)
        lines.append(f"/-- The box `M_{N}({x} + {y} i)` inflated by the order-4 remainder radius. -/")
        lines.append("def box : ComplexInterval :=")
        lines.append(f"  (mainBoxG tab {N} {q(x)} {q(y)}).inflate (remR tab {N} {q(x)} {q(d['P'])})")
        lines.append("")
        lines.append("theorem box_contains :")
        lines.append(f"    box.contains (riemannZeta (ptQ {q(x)} {q(y)})) :=")
        lines.append(f"  zeta_mem_pointBox (a := {q(x)}) (y := {q(y)}) (by norm_num) (by norm_num) (N := {N})")
        lines.append(f"    (by norm_num) tab_mem (P := {q(d['P'])}) (by norm_num) (by decide +kernel) le_rfl")
        lines.append("")
        lines.append(f"/-- The box lies in the open right half-plane, below the real axis, and"
                     f" `Im lo / Re lo ≥ {lo}` (it is {float(d['ratio']):.6f}, rounded here). -/")
        lines.append("theorem box_ok :")
        lines.append(f"    0 < box.re.lo ∧ box.im.hi ≤ 0 ∧ {q(lo)} ≤ box.im.lo / box.re.lo := by")
        lines.append("  decide +kernel")
        lines.append("")
        lines.append(f"/-- `{lo} ≤ arg ζ({x} + {y} i) ≤ 0`. -/")
        lines.append("theorem arg_bounds :")
        lines.append(f"    ({q(lo)} : ℝ) ≤ (riemannZeta (ptQ {q(x)} {q(y)})).arg ∧")
        lines.append(f"      (riemannZeta (ptQ {q(x)} {q(y)})).arg ≤ 0 := by")
        lines.append("  obtain ⟨h1, h2, h3⟩ := box_ok")
        lines.append("  obtain ⟨h4, h5⟩ := arg_mem_of_box box_contains h1 h2")
        lines.append("  refine ⟨le_trans ?_ h4, h5⟩")
        lines.append("  exact_mod_cast h3")
        lines.append("")
        lines.append(f"end {ns}")
        lines.append("")
    return "\n".join(lines)


def build(M) -> dict:
    out = {}
    bottom = [segment(M, a, b, BOTTOM[0], N) for a, b, N in BOTTOM[1]]
    top = [segment(M, a, b, TOP[0], N) for a, b, N in TOP[1]]
    pts = [(tag, point(M, x, y, N, lo)) for tag, x, y, N, lo in POINTS]
    for name, segs in (("bottom", bottom), ("top", top)):
        assert segs[0]["a"] == F(1, 2) and segs[-1]["b"] == 2
        for d0, d1 in zip(segs, segs[1:]):
            assert d0["b"] == d1["a"], "the segments must tile [1/2, 2]"
    out["LegsBottom"] = (render_legs("Re zeta > 0 on the leg [1/2, 2] + 3i", BOTTOM[0], bottom, 1),
                         bottom)
    out["LegsTop1"] = (render_legs("Re zeta > 0 on [1/2, 15/16] + 52i", TOP[0], top[:3], 1), top[:3])
    out["LegsTop2"] = (render_legs("Re zeta > 0 on [15/16, 2] + 52i", TOP[0], top[3:], 4), top[3:])
    out["LegsArg"] = (render_points(pts), pts)
    return out


def report(out: dict) -> None:
    import mpmath
    from mpmath import mp
    with mp.workdps(30):
        for name in ("LegsBottom", "LegsTop1", "LegsTop2"):
            for d in out[name][1]:
                a, b, y = d["a"], d["b"], d["y"]
                grid = [a + (b - a) * F(k, 64) for k in range(65)]
                vals = [mpmath.zeta(mpmath.mpc(float(s), float(y))).real for s in grid]
                print(f"  measured: min Re zeta on [{a}, {b}] + {y}i (65 samples) = {float(min(vals)):.6f}")
        for tag, d in out["LegsArg"][1]:
            z = mpmath.zeta(mpmath.mpc(float(d["x"]), float(d["y"])))
            print(f"  measured: zeta({d['x']} + {d['y']}i) = {complex(z)}, arg = {float(mpmath.arg(z)):.6f}")


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true", help="compare with the files on disk, write nothing")
    ap.add_argument("--report", action="store_true", help="also print mpmath values (measured)")
    ap.add_argument("--out", help="write into this directory instead of lean/RHHeight")
    args = ap.parse_args(argv)
    M = load_mirror()
    out = build(M)
    bad = 0
    for name in ("LegsBottom", "LegsTop1", "LegsTop2"):
        for d in out[name][1]:
            flag = "ok" if d["slack"] > MARGIN else "REFUSED"
            print(f"{name}: [{d['a']}, {d['b']}] + {d['y']}i, N = {d['N']} ({towers(d['N'])} towers):"
                  f" main {float(d['main_lo']):.4f}, variation {float((d['b'] - d['a']) * d['L']):.4f},"
                  f" remainder {float(d['R']):.4f}, slack {float(d['slack']):.4f} {flag}")
            bad += 0 if d["slack"] > MARGIN else 1
    for tag, d in out["LegsArg"][1]:
        ok = d["ok"] and d["margin"] > MARGIN / 10
        print(f"LegsArg {tag}: N = {d['N']} ({towers(d['N'])} towers), radius {float(d['e']):.5f},"
              f" Re in [{float(d['re'][0]):.5f}, {float(d['re'][1]):.5f}],"
              f" Im in [{float(d['im'][0]):.5f}, {float(d['im'][1]):.5f}],"
              f" Im lo / Re lo = {float(d['ratio']):.5f} against {d['lower']} {'ok' if ok else 'REFUSED'}")
        bad += 0 if ok else 1
    if args.report:
        report(out)
    if bad:
        print("REFUSED: a segment or a point does not close with the margin", file=sys.stderr)
        return 1
    target = Path(args.out) if args.out else LEAN_DIR
    for name, (text, _) in out.items():
        path = target / f"{name}.lean"
        if args.check:
            same = path.is_file() and path.read_text(encoding="utf-8") == text
            print(f"  {path.name} {'matches' if same else 'differs from'} the generator")
            bad += 0 if same else 1
        else:
            path.write_text(text, encoding="utf-8")
            print(f"  wrote {path} ({len(text.splitlines())} lines)")
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
