"""Emit `lean/RHHeight100/Box<tag>.lean`: zeros 11 to 29 on the line, one file per bracket.

Run from the repository root:

    .venv/bin/python hunts/rh_height_lean/gen_boxes100.py                # write every file
    .venv/bin/python hunts/rh_height_lean/gen_boxes100.py --check        # compare, write nothing
    .venv/bin/python hunts/rh_height_lean/gen_boxes100.py --only 5297    # one bracket

Hunt #133's generator (`hunts/hardy_ten_zeros/gen_boxes.py`) carried to the nineteen zeros
with `50 < t < 100`, for `RHHeight100`. The brackets are the two-decimal intervals around
`mpmath.zetazero(k)` for k = 11..29, except the two in `SHIFTED` (k = 16 and 28), whose zero
sits within 1e-3 of a two-decimal endpoint; their brackets are moved by 0.005, keeping width
1/100. Truncations and radii come from hunt
#133's `choose_truncations` and `lean_radius`, unchanged; the assembly is
`RHHeight100.zero_of_tables100`. The term boxes are computed by the lab's
bit-exact rational mirror of the interval layer (`scripts/61_rung3_mirror.py`): an exp
tower (`dirichletTermBox2`) for every prime, the coarsened product of two earlier boxes for
every composite (`cpowBox`, smallest prime factor first), and the exact box `1` for `m = 1`.
Nothing here is trusted by the proof: the kernel checks every literal against the Lean
definition by `decide +kernel`, so a wrong mirror value fails the build, never the theorem.
The generator re-runs the final sign test in exact rational arithmetic, with the radii and
with the radii times `sizing.MARGIN`, and refuses to write a file that does not pass both.
"""
from __future__ import annotations

import argparse
import sys
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
if str(ROOT) not in sys.path:  # pragma: no cover - import bootstrap
    sys.path.insert(0, str(ROOT))

from hunts.hardy_first_zero import sizing as S1  # noqa: E402
from hunts.hardy_ten_zeros import sizing as SZ  # noqa: E402

LEAN_DIR = HERE / "lean" / "RHHeight100"
NLOG, NEXP, P = SZ.NLOG, SZ.NEXP, SZ.P
#: Hunt #133 used kE = 8 (|s log m| <= 256). Above t of about 59 the arguments pass 256 (at
#: t = 100, m = 160 they reach about 508), so the range reduction here uses kE = 10.
KE = 10


def q(x: F) -> str:
    x = F(x)
    if x.denominator == 1:
        return f"({x.numerator} : ℚ)"
    return f"({x.numerator} / {x.denominator} : ℚ)"


def scale(t: F) -> int:
    """100 for a two-decimal height, 1000 for a three-decimal one."""
    for d in (100, 1000):
        if (F(t) * d).denominator == 1:
            return d
    raise ValueError(f"{t} has more than three decimals")


def lit(t: F) -> str:
    """`NNNN / 100` or `NNNNN / 1000`, unnormalized, so every statement names the same term."""
    d = scale(t)
    return f"{int(F(t) * d)} / {d}"


def qt(t: F) -> str:
    """The height as the unnormalized rational literal `(NNNN / 100 : ℚ)`."""
    return f"({lit(t)} : ℚ)"


def tag(a: F) -> str:
    """`5297` for 52.97, `95865` for 95.865."""
    return str(int(F(a) * scale(a)))


#: Brackets moved off a zero that sits within 1e-3 of a two-decimal endpoint, keeping width
#: 1/100: gamma_16 = 67.07981 (at (67.07, 67.08) the order-4 boxes decide the sign but not
#: with the radii x 1.5 margin, even at N = 160) and gamma_28 = 95.87063 (no truncation up to
#: 160 decides (95.87, 95.88)).
SHIFTED = {16: (F(67075, 1000), F(67085, 1000)), 28: (F(95865, 1000), F(95875, 1000))}


def plan() -> list[dict]:
    """Truncations and radii for zeros 11..29 (order 4, Lean radii), hunt #133's rules."""
    import mpmath
    from mpmath import mp
    with mp.workdps(30):
        gs = [mpmath.zetazero(k).imag for k in range(11, 30)]
    rows = []
    for k, g in zip(range(11, 30), gs):
        a, b = SZ.bracket(g)
        if k in SHIFTED:
            a, b = SHIFTED[k]
        c = SZ.choose_truncations(a, b, 4, True)
        rows.append({"k": k, "a": a, "b": b, "tag": tag(a), "N_a": c["N_a"], "N_b": c["N_b"],
                     "rad_a": SZ.lean_radius(a, c["N_a"]), "rad_b": SZ.lean_radius(b, c["N_b"])})
    return rows


def spf(m: int) -> int:
    """Smallest prime factor."""
    f = 2
    while f * f <= m:
        if m % f == 0:
            return f
        f += 1
    return m


def c_const(N: int, t: F) -> tuple[F, F]:
    """`cRe N t`, `cIm N t` of `TenSupport.lean`, exactly."""
    den = F(1, 4) + t * t
    return (N * F(-1, 2) / den + F(1, 2) + F(1, 2) / (12 * N), -(N * t) / den + t / (12 * N))


def table(M, t: F, N: int) -> dict:
    """Term boxes for m = 1..N at s = 1/2 + it, the way the Lean file builds them."""
    S = M.cexact(F(1, 2), t)
    boxes = {}
    for m in range(1, N + 1):
        if m == 1:
            boxes[m] = M.cexact(1, 0)
            continue
        f = spf(m)
        if f == m:
            arg = M.cmul(M.cneg(S), M.C(M.logQ(NLOG, m.bit_length(), F(m)), M.iexact(0)))
            if not M.normBound(arg) <= 2**KE:
                raise ValueError(f"normBound {float(M.normBound(arg))} > 2^{KE} at m = {m}, t = {t}")
            boxes[m] = M.dirichletTermBox2(NLOG, NEXP, P, m.bit_length(), KE, m, S)
        else:
            boxes[m] = M.ccoarsen(P, M.cmul(boxes[f], boxes[m // f]))
    return boxes


def main_box(M, boxes: dict, N: int, t: F):
    """`mainBox T N t`: sumBoxes T N, plus T N times the exact c_N(s)."""
    acc = M.cexact(0, 0)
    for m in range(N):
        acc = M.cadd(acc, boxes[m] if m >= 1 else M.cexact(0, 0))
    cre, cim = c_const(N, t)
    return M.cadd(acc, M.cmul(boxes[N], M.cexact(cre, cim)))


def prod_hi(M, A, B) -> F:
    return M.iadd(M.imul(A.re, B.re), M.imul(A.im, B.im)).hi


def build(row, M=None) -> dict:
    """Everything one bracket's Lean file needs, with the exact sign test done here."""
    M = M or S1.load_mirror()
    a, b, Na, Nb = row["a"], row["b"], row["N_a"], row["N_b"]
    ta, tb = table(M, a, Na), table(M, b, Nb)
    ea, eb = row["rad_a"]["e"], row["rad_b"]["e"]
    Ma, Mb = main_box(M, ta, Na, a), main_box(M, tb, Nb, b)
    hi = prod_hi(M, M.cinflate(Ma, ea), M.cinflate(Mb, eb))
    hi_margin = prod_hi(M, M.cinflate(Ma, ea * SZ.MARGIN), M.cinflate(Mb, eb * SZ.MARGIN))
    return {**row, "ta": ta, "tb": tb, "hi": hi, "hi_margin": hi_margin}


def render(d) -> str:
    a, b, tg = d["a"], d["b"], d["tag"]
    ns = f"RHHeight100.I{tg}"
    la, lb = lit(a), lit(b)
    fa, fb = f"{float(a):g}", f"{float(b):g}"
    lines = [
        "module",
        "",
        "public import RHHeight100.Support",
        "",
        "@[expose] public section",
        "",
        "/-!",
        f"# A zero of zeta on the critical line between {fa} and {fb} (generated)",
        "",
        "Generated by `hunts/rh_height_lean/gen_boxes100.py` from the lab's bit-exact rational mirror",
        "of the interval layer; do not edit by hand. Every literal is checked by the kernel against",
        "the Lean definition (`decide +kernel`): primes against `dirichletTermBox2` with",
        f"`nLog = {NLOG}`, `nExp = {NEXP}`, `p = {P}`, `kE = {KE}`, `kL` the bit length of `m`;",
        f"composites against the `{P}`-bit coarsened product of the boxes of their smallest prime",
        "factor and cofactor. The order-4 remainder at truncation `N` and the phase lemma come from",
        "hunt #133's `TenSupport.lean` and `RHHeight100/Support.lean`; `zero_of_tables100` assembles them. No minimality and no uniqueness of the",
        "zero in this interval is asserted.",
        "-/",
        "",
        "open Complex ZetaLean ZetaLean.ComplexInterval HardyFirstZero",
        "",
        f"namespace {ns}",
        "",
        "set_option maxRecDepth 100000",
        "",
    ]
    for side, t, N, tbl in (("A", a, d["N_a"], d["ta"]), ("B", b, d["N_b"], d["tb"])):
        tq = qt(t)
        lines.append(f"/-- Term boxes `m^(-s)` at `s = 1/2 + i · {t}`, `1 ≤ m ≤ {N}`. -/")
        lines.append(f"def t{side} : ℕ → ComplexInterval")
        lines.append("  | 1 => ComplexInterval.exact 1 0")
        for m in range(2, N + 1):
            bx = tbl[m]
            lines.append(f"  | {m} => lit {q(bx.re.lo)} {q(bx.re.hi)}")
            lines.append(f"      {q(bx.im.lo)} {q(bx.im.hi)} (by norm_num) (by norm_num)")
        lines.append("  | _ => ComplexInterval.exact 0 0")
        lines.append("")
        lines.append(f"theorem t{side}_mem_1 :")
        lines.append(f"    (t{side} 1).contains (((1 : ℕ) : ℂ) ^ (-sOf ({tq} : ℝ))) :=")
        lines.append("  HardyTenZeros.contains_one_cpow _")
        lines.append("")
        for m in range(2, N + 1):
            f = spf(m)
            if f == m:
                kl = m.bit_length()
                lines.append(f"theorem t{side}_eq_{m} :")
                lines.append(f"    dirichletTermBox2 {NLOG} {NEXP} {P} {kl} {KE} {m} (ptBox {tq}) = t{side} {m} := by")
                lines.append("  decide +kernel")
                lines.append("")
                lines.append(f"theorem t{side}_mem_{m} :")
                lines.append(f"    (t{side} {m}).contains ((({m} : ℕ) : ℂ) ^ (-sOf ({tq} : ℝ))) := by")
                lines.append(f"  rw [← t{side}_eq_{m}]")
                lines.append("  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)")
                lines.append("    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)")
                lines.append("")
            else:
                g = m // f
                lines.append(f"theorem t{side}_eq_{m} : ((t{side} {f}).mul (t{side} {g})).coarsen {P} = t{side} {m} := by")
                lines.append("  decide +kernel")
                lines.append("")
                lines.append(f"theorem t{side}_mem_{m} :")
                lines.append(f"    (t{side} {m}).contains ((({m} : ℕ) : ℂ) ^ (-sOf ({tq} : ℝ))) := by")
                lines.append(f"  rw [← t{side}_eq_{m}]")
                lines.append(f"  exact HardyTenZeros.contains_cpow_mul_coarsen {P} t{side}_mem_{f} t{side}_mem_{g}")
                lines.append("")
        lines.append(f"theorem t{side}_mem : ∀ m < {N} + 1,")
        lines.append(f"    (t{side} m).contains ((m : ℂ) ^ (-sOf ({tq} : ℝ))) := by")
        lines.append("  intro m hm")
        lines.append("  interval_cases m")
        lines.append("  · rw [Nat.cast_zero, zero_cpow (neg_ne_zero.mpr (sOf_ne_zero _))]")
        lines.append("    exact contains_zero")
        for m in range(1, N + 1):
            lines.append(f"  · exact t{side}_mem_{m}")
        lines.append("")
    ea, eb = d["rad_a"]["e"], d["rad_b"]["e"]
    lines += [
        "/-- The interval product decides the sign: its upper end is negative. -/",
        "theorem product_hi_neg :",
        f"    HardyTenZeros.prodHi ((HardyTenZeros.mainBox tA {d['N_a']} {qt(a)}).inflate {q(ea)})",
        f"      ((HardyTenZeros.mainBox tB {d['N_b']} {qt(b)}).inflate {q(eb)}) < 0 := by",
        "  decide +kernel",
        "",
        f"end {ns}",
        "",
        "namespace RHHeight100",
        "",
        "open HardyFirstZero HardyTenZeros",
        "",
        f"/-- `ζ` has a zero `1/2 + it` with `{fa} < t < {fb}`. No minimality and no",
        "uniqueness is asserted. -/",
        f"theorem zero_in_{tg} :",
        f"    ∃ t ∈ Set.Ioo ({la} : ℝ) ({lb}), riemannZeta (1 / 2 + t * I) = 0 := by",
        f"  have h := zero_of_tables100 (a := {la}) (b := {lb})",
        "    (by norm_num) (by norm_num) (by norm_num) (by norm_num)",
        f"    (Na := {d['N_a']}) (Nb := {d['N_b']}) (by norm_num) (by norm_num)",
        f"    I{tg}.tA_mem I{tg}.tB_mem",
        f"    (ra := {q(d['rad_a']['r'])}) (Ra := {q(d['rad_a']['R'])}) (ea := {q(ea)})",
        f"    (rb := {q(d['rad_b']['r'])}) (Rb := {q(d['rad_b']['R'])}) (eb := {q(eb)})",
        "    (by norm_num) (by norm_num) (by norm_num) (by norm_num [q4Q]) (by norm_num)",
        "    (by norm_num) (by norm_num) (by norm_num) (by norm_num [q4Q]) (by norm_num)",
        f"    I{tg}.product_hi_neg",
        f"  have e1 : (({la} : ℚ) : ℝ) = {la} := by norm_num",
        f"  have e2 : (({lb} : ℚ) : ℝ) = {lb} := by norm_num",
        "  rw [e1, e2] at h",
        "  exact h",
        "",
        "end RHHeight100",
        "",
    ]
    return "\n".join(lines)


def path_for(tg: str) -> Path:
    return LEAN_DIR / f"Box{tg}.lean"


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true", help="compare with the files on disk, write nothing")
    ap.add_argument("--only", help="one bracket tag, e.g. 2102")
    args = ap.parse_args(argv)
    M = S1.load_mirror()
    rows = plan()
    if args.only:
        rows = [r for r in rows if r["tag"] == args.only]
        if not rows:
            print(f"no bracket with tag {args.only}", file=sys.stderr)
            return 2
    bad = 0
    for row in rows:
        d = build(row, M)
        print(f"{d['tag']}: N_a = {d['N_a']}, N_b = {d['N_b']}, upper end {float(d['hi']):.6e},"
              f" with radii x {float(SZ.MARGIN)}: {float(d['hi_margin']):.6e}")
        if not (d["hi"] < 0 and d["hi_margin"] < 0):
            print(f"REFUSED: the boxes for {d['tag']} do not decide the sign with the margin", file=sys.stderr)
            bad += 1
            continue
        text = render(d)
        out = path_for(d["tag"])
        if args.check:
            same = out.is_file() and out.read_text(encoding="utf-8") == text
            print(f"  {out.name} {'matches' if same else 'differs from'} the generator")
            bad += 0 if same else 1
        else:
            out.write_text(text, encoding="utf-8")
            print(f"  wrote {out.relative_to(ROOT)} ({len(text.splitlines())} lines)")
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
