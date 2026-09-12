#!/usr/bin/env python3
"""Generate the rung-3 certificate Lean files from a plan JSON.

The plan (produced and cross-verified by the numeric planner) fixes the
square geometry, the point grid on the small frontier, the upper-bound boxes
on the big frontier, and every per-site parameter.  This script emits one
Lean file per site plus (separately) the assembly file proving
`davenport_heilbronn : davenport_heilbronn_statement`.

Evaluation is *staged*: a bit-exact Fraction mirror of the Lean interval
arithmetic (scripts/61_rung3_mirror.py) precomputes every box value; the
generated proofs assert per-term literal equalities (cheap `norm_num`
calls), fold literals, and read `normLower`/`normBound` off a literal box.
A wrong mirror value cannot weaken the theorem, the kernel refuses the
equality, and the mirror doubles as an exact feasibility check at
generation time: sites whose margins fail are reported *before* any kernel
compute is spent.

Grid `beta`s are **read off the enclosure, not predicted** (`docs/25` §4.3
defect 2, hunt `hunts/r_908de5`): a predicted beta drawn at the achievable
bound makes `normLower >= beta` true at the line by construction, in any
arithmetic, so the site inequality stops carrying information.  With
`beta := normLower` the site inequality is true by construction *and says so*,
and the obligation that still bites, `eps' + L*h/2 <= beta`, the hypothesis of
`DH_lower_on_[hv]cell`: is checked here, at generation time.

Usage:
  .venv/bin/python scripts/60_rung3_generate.py PLAN.json OUTDIR [--only ID]
                                                [--beta measured|plan]
"""
from __future__ import annotations

import importlib.util
import json
import pathlib
import sys
from fractions import Fraction

_here = pathlib.Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location("mirror", _here / "61_rung3_mirror.py")
mirror = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(mirror)

TAYLOR_N = 20
COARSEN_P = 64
KE = 10
CHUNK = 25

TERM_SIMPSET = (
    "term_{sid}, coeffBox, kappaCBox, kappaI, {S}, dirichletTermBox, expCr,\n"
    "      expSmall, expSumC, smulQ, powI, coarsen, ZetaLean.Interval.coarsen,\n"
    "      halveC, normBound, inflate, ComplexInterval.mul, ComplexInterval.add,\n"
    "      ComplexInterval.neg, ComplexInterval.exact, ZetaLean.Interval.exact,\n"
    "      ZetaLean.Interval.mul, ZetaLean.Interval.add, ZetaLean.Interval.neg,\n"
    "      ZetaLean.Interval.sub, ZetaLean.Interval.halve, ZetaLean.Interval.logQ,\n"
    "      ZetaLean.Interval.log2I, ZetaLean.Interval.log1, ZetaLean.Interval.logSum,\n"
    "      ZetaLean.Interval.logRem, Nat.factorial, Finset.sum_range_succ,\n"
    "      Finset.sum_range_zero"
)

HB_SIMPSET = (
    "{S}, normBound, ComplexInterval.mul, ComplexInterval.neg,\n"
    "      ComplexInterval.exact, ZetaLean.Interval.logQ, ZetaLean.Interval.log2I,\n"
    "      ZetaLean.Interval.log1, ZetaLean.Interval.logSum, ZetaLean.Interval.logRem,\n"
    "      ZetaLean.Interval.exact, ZetaLean.Interval.mul, ZetaLean.Interval.add,\n"
    "      ZetaLean.Interval.neg, ZetaLean.Interval.sub, Finset.sum_range_succ"
)

INV_SIMPSET = (
    "{S}, inv5sBox, normSqI, ComplexInterval.mul, ComplexInterval.add,\n"
    "      ComplexInterval.neg, ComplexInterval.exact, ZetaLean.Interval.mul,\n"
    "      ZetaLean.Interval.add, ZetaLean.Interval.neg, ZetaLean.Interval.sub,\n"
    "      ZetaLean.Interval.exact"
)

LIT_SIMPSET = (
    "ComplexInterval.mul, ComplexInterval.add, ComplexInterval.neg,\n"
    "      ComplexInterval.exact, kappaCBox, kappaI, ZetaLean.Interval.mul,\n"
    "      ZetaLean.Interval.add, ZetaLean.Interval.neg, ZetaLean.Interval.sub,\n"
    "      ZetaLean.Interval.exact"
)


# Denominator of a measured `beta` literal.  `normLower` is exact but its
# denominator runs to thousands of bits; rounding DOWN to a multiple of
# 2^-BETA_BITS keeps the Lean literal small and keeps the claim true, a smaller
# beta being a weaker statement about the same enclosure.
BETA_BITS = 40


def beta_literal(nl: Fraction) -> Fraction:
    """Largest multiple of 2^-BETA_BITS that is at most `nl`."""
    scale = 1 << BETA_BITS
    return Fraction(int(nl * scale), scale)


def cell_requirements(plan: dict) -> dict:
    """`eps' + L*h/2` per grid site, the hypothesis of `DH_lower_on_[hv]cell`.

    Each site bounds the cells on either side of it, so its requirement is the
    larger of the two gaps' demands.
    """
    L, eps = Fraction(plan["L"]), Fraction(plan["small"]["eps"])
    by_seg: dict[str, list] = {}
    for g in plan.get("grid", []):
        by_seg.setdefault(g["segment"], []).append(g)
    need: dict[str, Fraction] = {}
    for gs in by_seg.values():
        for i, g in enumerate(gs):
            if g["gap_next"] is None:
                continue
            d = eps + L * Fraction(g["gap_next"]) / 2
            for s in (g, gs[i + 1]):
                need[s["id"]] = max(need.get(s["id"], Fraction(0)), d)
    return need


def q(x) -> str:
    f = Fraction(x)
    if f.denominator == 1:
        return f"({f.numerator} : ℚ)"
    return f"({f.numerator}/{f.denominator} : ℚ)"


def lit(box) -> str:
    return (f"(⟨⟨{q(box.re.lo)}, {q(box.re.hi)}, by norm_num⟩, "
            f"⟨{q(box.im.lo)}, {q(box.im.hi)}, by norm_num⟩⟩ : ComplexInterval)")


def kL_of(m: int) -> int:
    return m.bit_length()


def emit_site(site: dict, kind: str) -> tuple[str, dict]:
    sid = site["id"]
    K = site["K"]
    N = 5 * K
    S = f"S_{sid}"
    relo, rehi = Fraction(site["re_lo"]), Fraction(site["re_hi"])
    imlo, imhi = Fraction(site["im_lo"]), Fraction(site["im_hi"])
    r = Fraction(site["r"])

    # --- mirror computation of every box value -------------------------------
    MS = mirror.C(mirror.I(relo, rehi), mirror.I(imlo, imhi))
    terms = {m: mirror.term(m, MS, TAYLOR_N, COARSEN_P, KE) for m in range(N)}
    blockt = {m: mirror.dirichletTermBox(TAYLOR_N, COARSEN_P, kL_of(m), KE, m, MS)
              for m in (N + 1, N + 2, N + 3, N + 4)}
    m1, m2, m3, m4 = N + 1, N + 2, N + 3, N + 4
    antiV = mirror.invC(mirror.inv5sBox(MS))
    blockBox = mirror.cadd(
        mirror.cadd(blockt[m1], mirror.cneg(blockt[m4])),
        mirror.cmul(mirror.KAPPA_C,
                    mirror.cadd(blockt[m2], mirror.cneg(blockt[m3]))))
    antiSum = mirror.cadd(
        mirror.cadd(mirror.cmul(mirror.cexact(m1, 0), blockt[m1]),
                    mirror.cneg(mirror.cmul(mirror.cexact(m4, 0), blockt[m4]))),
        mirror.cmul(mirror.KAPPA_C,
                    mirror.cadd(mirror.cmul(mirror.cexact(m2, 0), blockt[m2]),
                                mirror.cneg(mirror.cmul(mirror.cexact(m3, 0),
                                                        blockt[m3])))))
    antiBox = mirror.cmul(antiSum, antiV)
    ps = {0: mirror.cexact(0, 0)}
    acc = ps[0]
    for i in range(N):
        acc = mirror.cadd(acc, terms[i])
        ps[i + 1] = acc
    halfBlock = mirror.cmul(blockBox, mirror.cexact(Fraction(1, 2), 0))
    B = mirror.cadd(mirror.cadd(ps[N], halfBlock), mirror.cneg(antiBox))
    Binf = mirror.cinflate(B, r)
    stats = {
        "id": sid, "kind": kind, "K": K,
        "normLower": mirror.normLower(Binf),
        "normBound": mirror.normBound(Binf),
    }

    # --- emit ----------------------------------------------------------------
    lines: list[str] = []
    a = lines.append
    a("/- Generated by scripts/60_rung3_generate.py, do not edit by hand. -/")
    a("import ZetaLean.DHCertSupport")
    a("")
    a("open Complex Finset ZetaLean ZetaLean.ComplexInterval ZetaLean.DH")
    a("")
    a("set_option maxRecDepth 8000000")
    a("set_option maxHeartbeats 40000000")
    a("")
    a("namespace ZetaLean.DH.Cert")
    a("")
    a(f"def {S} : ComplexInterval :=")
    a(f"  ⟨⟨{q(relo)}, {q(rehi)}, by norm_num⟩, ⟨{q(imlo)}, {q(imhi)}, by norm_num⟩⟩")
    a("")
    a(f"def term_{sid} (m : ℕ) : ComplexInterval :=")
    a("  if m % 5 = 0 then ComplexInterval.exact 0 0")
    a(f"  else (coeffBox m).mul (dirichletTermBox {TAYLOR_N} {COARSEN_P} (Nat.log2 m + 1) {KE} m {S})")
    a("")
    tsimp = TERM_SIMPSET.format(sid=sid, S=S)
    for m in range(N):
        if m % 5 == 0:
            a(f"private lemma ev_{sid}_{m} : term_{sid} {m} = ComplexInterval.exact 0 0 := rfl")
            a("")
            continue
        a(f"private lemma tm_{sid}_{m} {{s : ℂ}} (hS : {S}.contains s) :")
        a(f"    (dirichletTermBox {TAYLOR_N} {COARSEN_P} {kL_of(m)} {KE} {m} {S}).contains")
        a(f"      ((({m} : ℕ) : ℂ) ^ (-s)) :=")
        a("  contains_dirichletTermBox (by norm_num) (by norm_num) hS (by norm_num)")
        a("    (by norm_num)")
        a("    (by norm_num [" + HB_SIMPSET.format(S=S) + "])")
        a("")
        a(f"private lemma ev_{sid}_{m} : term_{sid} {m} =")
        a(f"    {lit(terms[m])} := by")
        a("  norm_num [" + tsimp + "]")
        a("")
    for m in (m1, m2, m3, m4):
        a(f"private lemma tm_{sid}_{m} {{s : ℂ}} (hS : {S}.contains s) :")
        a(f"    (dirichletTermBox {TAYLOR_N} {COARSEN_P} {kL_of(m)} {KE} {m} {S}).contains")
        a(f"      ((({m} : ℕ) : ℂ) ^ (-s)) :=")
        a("  contains_dirichletTermBox (by norm_num) (by norm_num) hS (by norm_num)")
        a("    (by norm_num)")
        a("    (by norm_num [" + HB_SIMPSET.format(S=S) + "])")
        a("")
        a(f"private lemma evb_{sid}_{m} :")
        a(f"    dirichletTermBox {TAYLOR_N} {COARSEN_P} {kL_of(m)} {KE} {m} {S} =")
        a(f"    {lit(blockt[m])} := by")
        a("  norm_num [" + tsimp + "]")
        a("")
    # dispatcher
    a(f"private lemma ht_{sid} {{s : ℂ}} (hS : {S}.contains s) :")
    a(f"    ∀ m, m < {N} → (term_{sid} m).contains ((dh_coeff m : ℂ) * (m : ℂ) ^ (-s)) :=")
    a("  fun m hm =>")
    a("    match m, hm with")
    for m in range(N):
        if m % 5 == 0:
            a(f"    | {m}, _ => contains_coeff_term_zero {m} rfl")
        else:
            a(f"    | {m}, _ => contains_coeff_term_ne {m} (by norm_num) (tm_{sid}_{m} hS)")
    a(f"    | (n + {N}), hm => absurd hm (by omega)")
    a("")
    # chunked partial-sum literals
    bounds = sorted(set(list(range(0, N, CHUNK)) + [N]))
    a(f"private lemma ps_{sid}_0 : dhSumBoxes (term_{sid}) 0 = ComplexInterval.exact 0 0 :=")
    a("  dhSumBoxes_zero _")
    a("")
    for lo_b, hi_b in zip(bounds, bounds[1:]):
        rws = []
        for n in range(hi_b, lo_b, -1):
            rws.append(f"show ({n} : ℕ) = {n - 1} + 1 from rfl")
            rws.append("dhSumBoxes_succ")
        rws.append(f"ps_{sid}_{lo_b}")
        rws.extend(f"ev_{sid}_{n}" for n in range(lo_b, hi_b))
        a(f"private lemma ps_{sid}_{hi_b} : dhSumBoxes (term_{sid}) {hi_b} =")
        a(f"    {lit(ps[hi_b])} := by")
        a("  rw [" + ",\n    ".join(rws) + "]")
        a("  norm_num [" + LIT_SIMPSET + "]")
        a("")
    # correction boxes and literals
    t = lambda m: f"(dirichletTermBox {TAYLOR_N} {COARSEN_P} {kL_of(m)} {KE} {m} {S})"
    a(f"def blockBox_{sid} : ComplexInterval :=")
    a(f"  ({t(m1)}.add {t(m4)}.neg).add (kappaCBox.mul ({t(m2)}.add {t(m3)}.neg))")
    a("")
    a(f"private lemma evblk_{sid} : blockBox_{sid} = {lit(blockBox)} := by")
    a(f"  rw [blockBox_{sid}, evb_{sid}_{m1}, evb_{sid}_{m2}, evb_{sid}_{m3}, evb_{sid}_{m4}]")
    a("  norm_num [" + LIT_SIMPSET + "]")
    a("")
    a(f"def antiV_{sid} : ComplexInterval :=")
    a(f"  (inv5sBox {S}).invC (by norm_num [" + INV_SIMPSET.format(S=S) + "])")
    a("")
    a(f"private lemma evV_{sid} : antiV_{sid} = {lit(antiV)} := by")
    a(f"  norm_num [antiV_{sid}, invC, normSqI, ZetaLean.Interval.inv', " + INV_SIMPSET.format(S=S) + "]")
    a("")
    e1 = f"((ComplexInterval.exact ({m1} : ℕ) 0).mul {t(m1)})"
    e2 = f"((ComplexInterval.exact ({m2} : ℕ) 0).mul {t(m2)})"
    e3n = f"(((ComplexInterval.exact ({m3} : ℕ) 0).mul {t(m3)}).neg)"
    e4n = f"(((ComplexInterval.exact ({m4} : ℕ) 0).mul {t(m4)}).neg)"
    a(f"def antiBox_{sid} : ComplexInterval :=")
    a(f"  (({e1}.add {e4n}).add")
    a(f"    (kappaCBox.mul ({e2}.add {e3n}))).mul antiV_{sid}")
    a("")
    a(f"private lemma evanti_{sid} : antiBox_{sid} = {lit(antiBox)} := by")
    a(f"  rw [antiBox_{sid}, evb_{sid}_{m1}, evb_{sid}_{m2}, evb_{sid}_{m3}, evb_{sid}_{m4},")
    a(f"    evV_{sid}]")
    a("  norm_num [" + LIT_SIMPSET + "]")
    a("")
    a(f"def B_{sid} : ComplexInterval :=")
    a(f"  ((dhSumBoxes (term_{sid}) {N}).add (blockBox_{sid}.mul")
    a(f"    (ComplexInterval.exact (1/2) 0))).add antiBox_{sid}.neg")
    a("")
    a(f"private lemma evB_{sid} : B_{sid} = {lit(B)} := by")
    a(f"  rw [B_{sid}, ps_{sid}_{N}, evblk_{sid}, evanti_{sid}]")
    a("  norm_num [" + LIT_SIMPSET + "]")
    a("")
    a(f"private lemma hB_{sid} {{s : ℂ}} (hS : {S}.contains s) :")
    a(f"    (B_{sid}).contains (∑ n ∈ range ({K} * 5), (dh_coeff n : ℂ) * (n : ℂ) ^ (-s)")
    a(f"      + dhBlock s {K} / 2 - dhAnti s (({K} : ℕ) : ℝ)) := by")
    a(f"  have hb := contains_dhBlock_of_terms (s := s) {K}")
    a(f"    (tm_{sid}_{m1} hS) (tm_{sid}_{m2} hS) (tm_{sid}_{m3} hS) (tm_{sid}_{m4} hS)")
    a(f"  have ha := contains_dhAnti_of_terms (s := s) {K}")
    a(f"    (tm_{sid}_{m1} hS) (tm_{sid}_{m2} hS) (tm_{sid}_{m3} hS) (tm_{sid}_{m4} hS)")
    a(f"    (contains_inv5sBox hS (by norm_num [" + INV_SIMPSET.format(S=S) + "]))")
    a(f"  exact contains_corrected (contains_dhSumBoxes {N} (ht_{sid} hS))")
    a("    (contains_half_of hb) ha")
    a("")
    slo = Fraction(site["sigma_lo"])
    a(f"theorem enc_{sid} {{s : ℂ}} (hS : {S}.contains s) :")
    a(f"    ((B_{sid}.inflate {q(r)}).contains (DH s)) :=")
    a(f"  DH_mem_of_partial_enclosure_order2_boxed hS (by norm_num [{S}]) (by norm_num [{S}])")
    a(f"    (K := {K}) (by norm_num) (hB_{sid} hS)")
    a(f"    (σlo := {q(slo)}) (by norm_num) (by norm_num [{S}])")
    a(f"    (a := {site['a']}) (b := {site['b']}) (by norm_num) (by norm_num)")
    a(f"    (P := {q(site['P'])}) (by norm_num) (by norm_num)")
    a(f"    (NS := {q(site['NS'])}) (by norm_num [{S}, normBound, ComplexInterval.exact,")
    a("      ZetaLean.Interval.exact])")
    a(f"    (NS1 := {q(site['NS1'])}) (by norm_num [{S}, normBound, ComplexInterval.add,")
    a("      ComplexInterval.exact, ZetaLean.Interval.add, ZetaLean.Interval.exact])")
    a(f"    (NS2 := {q(site['NS2'])}) (by norm_num [{S}, normBound, ComplexInterval.add,")
    a("      ComplexInterval.exact, ZetaLean.Interval.add, ZetaLean.Interval.exact])")
    a(f"    (r := {q(r)}) (by norm_num)")
    a("")
    if kind == "grid":
        # `beta` is *read off* the enclosure by default (`beta_literal` of the
        # mirror's own `normLower`), not predicted: a predicted beta drawn at
        # the achievable bound makes the site inequality true at the line in any
        # arithmetic, which is `docs/25` §4.3 defect 2.  A plan that carries an
        # explicit `beta` still wins, so the old behaviour stays reachable.
        beta = (Fraction(site["beta"]) if site.get("beta") is not None
                else beta_literal(stats["normLower"]))
        assert stats["normLower"] >= beta, (
            f"{sid}: normLower {float(stats['normLower'])} < beta {float(beta)}")
        # The claim is only worth what the *cell* obligation can spend.  A beta
        # read off the enclosure clears the site inequality by construction, so
        # the site inequality stops being evidence of anything; the check that
        # still bites is the hypothesis of `DH_lower_on_[hv]cell`.
        need = site.get("beta_need")
        assert need is None or beta >= Fraction(need), (
            f"{sid}: beta {float(beta)} < cell requirement eps' + L*h/2 = "
            f"{float(Fraction(need))}, this site cannot support its grid cell")
        px, py = site["re_lo"], site["im_lo"]
        a(f"noncomputable def z_{sid} : ℂ := ⟨(({q(px)}) : ℝ), (({q(py)}) : ℝ)⟩")
        a("")
        a(f"theorem beta_{sid} : (({q(beta)}) : ℝ) ≤ ‖DH z_{sid}‖ := by")
        a(f"  have henc := enc_{sid} (s := z_{sid}) (ComplexInterval.contains_exact _ _)")
        a("  refine le_norm_of_enclosure henc ?_")
        a(f"  rw [evB_{sid}]")
        a("  norm_num [normLower, ZetaLean.Interval.distToZero, inflate]")
    elif kind == "big":
        M = Fraction(site["M"])
        assert stats["normBound"] <= M, (
            f"{sid}: normBound {float(stats['normBound'])} > M {float(M)}")
        a(f"theorem upper_{sid} {{s : ℂ}} (hS : {S}.contains s) :")
        a(f"    ‖DH s‖ ≤ (({q(M)}) : ℝ) := by")
        a(f"  have henc := enc_{sid} hS")
        a("  refine norm_le_of_enclosure henc ?_")
        a(f"  rw [evB_{sid}]")
        a("  norm_num [normBound, inflate]")
    elif kind == "centre":
        eps = Fraction(site["eps"])
        assert stats["normBound"] < eps, (
            f"centre: normBound {float(stats['normBound'])} >= eps {float(eps)}")
        px, py = site["re_lo"], site["im_lo"]
        a(f"noncomputable def z_{sid} : ℂ := ⟨(({q(px)}) : ℝ), (({q(py)}) : ℝ)⟩")
        a("")
        a(f"theorem centre_lt_{sid} : ‖DH z_{sid}‖ < (({q(eps)}) : ℝ) := by")
        a(f"  have henc := enc_{sid} (s := z_{sid}) (ComplexInterval.contains_exact _ _)")
        a("  refine norm_lt_of_enclosure henc ?_")
        a(f"  rw [evB_{sid}]")
        a("  norm_num [normBound, inflate]")
    a("")
    a("end ZetaLean.DH.Cert")
    a("")
    return "\n".join(lines), stats


def main() -> None:
    plan_path, outdir = sys.argv[1], pathlib.Path(sys.argv[2])
    only = sys.argv[sys.argv.index("--only") + 1] if "--only" in sys.argv else None
    beta_from_plan = ("--beta" in sys.argv
                      and sys.argv[sys.argv.index("--beta") + 1] == "plan")
    plan = json.loads(pathlib.Path(plan_path).read_text())
    outdir.mkdir(parents=True, exist_ok=True)
    sites = []
    c = dict(plan["centre"])
    c.setdefault("id", "centre")
    c["re_lo"] = c["re_hi"] = plan["small"]["cre"]
    c["im_lo"] = c["im_hi"] = plan["small"]["cim"]
    c["eps"] = plan["small"]["eps"]
    sites.append((c, "centre"))
    need = cell_requirements(plan)
    for g in plan.get("grid", []):
        g = dict(g)
        if g["segment"] in ("bottom", "top"):
            g["re_lo"] = g["re_hi"] = g["x"]
            g["im_lo"] = g["im_hi"] = g["fixed"]
        else:
            g["re_lo"] = g["re_hi"] = g["fixed"]
            g["im_lo"] = g["im_hi"] = g["x"]
        # None => read beta off the enclosure.  `--beta plan` restores the
        # predicted value the plan carries.
        g["beta"] = ((g.get("beta") or g.get("pred_beta_claim") or g.get("pred_beta"))
                     if beta_from_plan else None)
        g["beta_need"] = str(need[g["id"]]) if g["id"] in need else None
        sites.append((g, "grid"))
    for b in plan.get("big", {}).get("boxes", []):
        b = dict(b)
        b["M"] = plan["M"]
        sites.append((b, "big"))
    for site, kind in sites:
        if only and site["id"] != only:
            continue
        text, stats = emit_site(site, kind)
        (outdir / f"C{site['id']}.lean").write_text(text)
        print(f"C{site['id']}.lean kind={kind} K={site['K']} "
              f"normLower={float(stats['normLower']):.6g} "
              f"normBound={float(stats['normBound']):.6g}", flush=True)


if __name__ == "__main__":
    main()
