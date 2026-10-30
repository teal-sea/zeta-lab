"""Pins for hunt #152: Revers's error terms, the zero sum, and planted faults."""

from __future__ import annotations

import dataclasses
import sys
from pathlib import Path

import pytest

flint = pytest.importorskip("flint")
from flint import arb  # noqa: E402

sys.path.insert(0, str(Path(__file__).resolve().parent))
import skewes_terms as st  # noqa: E402
import zero_layer as zl  # noqa: E402


@pytest.fixture(autouse=True)
def _prec128():
    old = flint.ctx.prec
    flint.ctx.prec = 128
    yield
    flint.ctx.prec = old


def _contains_decimal(ball, printed: str) -> bool:
    """The printed six-digit value is within one unit of its last digit of the ball.

    One unit, not half: the paper's row at eta = 1.58e-5 prints 6.97516e-3 for
    6.9751654e-3, so its printing truncates at least there.
    """
    mant, exp = printed.split("e")
    digits = len(mant.split(".")[1])
    ulp = arb(10) ** (int(exp) - digits)
    return bool(abs(ball - arb(printed)) <= ulp + ball.rad())


# [Rev25] subsections 6.2 and 6.3: eta -> printed R, Saouter-Demichel and Chao-Plymen tables.
SD_TABLE = [("0.0000228", "2.79507e-3"), ("0.0000200", "2.79503e-3"),
            ("0.0000180", "2.79500e-3"), ("0.0000160", "2.79527e-3"),
            ("0.0000159", "2.83095e-3"), ("0.0000158", "6.97516e-3")]
CP_TABLE = [("0.0001600", "6.14384e-3"), ("0.0001400", "6.14369e-3"),
            ("0.0001200", "6.14353e-3"), ("0.0001063", "6.20670e-3"),
            ("0.0001061", "6.40600e-3"), ("0.0001060", "6.67779e-3"),
            ("0.0001050", "6.33687e-1")]


@pytest.mark.parametrize("eta,printed", SD_TABLE)
def test_R_reproduces_revers_saouter_demichel_table(eta, printed):
    p = dataclasses.replace(st.SAOUTER_DEMICHEL, eta=eta)
    assert _contains_decimal(st.revers_R(p)["R"], printed)


@pytest.mark.parametrize("eta,printed", CP_TABLE)
def test_R_reproduces_revers_chao_plymen_table(eta, printed):
    p = dataclasses.replace(st.CHAO_PLYMEN, eta=eta)
    assert _contains_decimal(st.revers_R(p)["R"], printed)


def test_revers_row_labelled_1_55e_5_is_the_value_at_1_56e_5():
    """Observation: the table's last row (eta = 0.0000155, R = 5.15554e1) is
    reproduced at eta = 0.0000156; at 0.0000155 the same formula gives 5473.12.
    Both rows are negative lower bounds, so the paper's conclusion is unaffected."""
    at_156 = st.revers_R(dataclasses.replace(st.SAOUTER_DEMICHEL, eta="0.0000156"))["R"]
    at_155 = st.revers_R(dataclasses.replace(st.SAOUTER_DEMICHEL, eta="0.0000155"))["R"]
    assert _contains_decimal(at_156, "5.15554e1")
    assert abs(at_155 - arb("5473.1245")) < arb("1e-3")


def test_hypotheses_hold_at_both_parameter_sets():
    for p in (st.CHAO_PLYMEN, st.SAOUTER_DEMICHEL):
        assert all(st.check_hypotheses(p).values())


def test_hypothesis_check_can_fail():
    bad = dataclasses.replace(st.SAOUTER_DEMICHEL, T="7e7")  # T > A
    assert not st.check_hypotheses(bad)["2 pi e < T <= A"]


def test_float_margin_from_revers_sum():
    """MISSION (c): -1 - S* - R = 1.2787e-4 at eta = 2.28e-5 (before Delta S1)."""
    lb = st.lower_bound_I(arb(st.REVERS_S_STAR["saouter_demichel"]), st.SAOUTER_DEMICHEL)
    assert abs(lb - arb("1.27874e-4")) < arb("1e-9")


def test_planted_fault_dropping_R4_moves_the_bound():
    full = st.revers_R(st.SAOUTER_DEMICHEL)
    dropped = full["R"] - full["R4"]
    assert abs(full["R"] - dropped - arb("3.2021e-5")) < arb("1e-9")


@pytest.fixture(scope="module")
def low_zeros():
    g, _ = zl.arb_zeros(1, 120, batch=120)
    return g


def test_cutoffs_count_exactly_the_intended_zeros():
    """Revers's printed T are truncations: one zero short; ours count exactly n."""
    for key, p in (("chao_plymen", st.CHAO_PLYMEN), ("saouter_demichel", st.SAOUTER_DEMICHEL)):
        assert zl.count_below(p.T) == st.N_ZEROS[key]
        assert zl.count_below(st.REVERS_PRINTED_T[key]) == st.N_ZEROS[key] - 1


def test_cutoffs_by_the_mpmath_route():
    """Route 2 (mpmath, not rigorous) agrees with Arb on both cutoffs."""
    import mpmath

    with mpmath.workdps(30):
        for key, p in (("chao_plymen", st.CHAO_PLYMEN), ("saouter_demichel", st.SAOUTER_DEMICHEL)):
            assert mpmath.nzeros(mpmath.mpf(p.T)) == st.N_ZEROS[key]
            assert mpmath.nzeros(mpmath.mpf(st.REVERS_PRINTED_T[key])) == st.N_ZEROS[key] - 1


def test_zero_count_matches_ground_truth():
    assert zl.count_below("100") == 29
    assert zl.count_below("1000") == 649


def test_zeros_ordered_and_first_known(low_zeros):
    assert zl.check_ordered(low_zeros)
    assert abs(low_zeros[0] - arb("14.134725141734694")) < arb("1e-15")
    assert abs(low_zeros[2] - arb("25.010857580145689")) < arb("1e-15")


def test_sum_agrees_with_mpmath_float_route(low_zeros):
    """The ball sum over 120 zeros agrees with an mpmath float sum over zetazero."""
    import mpmath

    w, al = "727.952018", "1.34e11"
    ball = st.lehman_sum(low_zeros, w, al)
    with mpmath.workdps(40):
        W, AL = mpmath.mpf(w), mpmath.mpf(al)
        s = mpmath.mpf(0)
        for n in range(1, 121):
            g = mpmath.zetazero(n).imag
            rho = mpmath.mpc(0.5, g)
            s += mpmath.re(mpmath.exp(1j * g * W) * (1 / rho + 1 / (W * rho**2))
                           * mpmath.exp(-g * g / (2 * AL)))
        s *= 2
    assert abs(ball - arb(mpmath.nstr(s, 35))) < arb("1e-25")


def test_planted_fault_perturbing_one_zero_moves_the_ball(low_zeros):
    """A 1e-6 shift in gamma_100 moves the sum by ~ |ds/dgamma| 1e-6 and leaves the ball."""
    w, al = "727.952018", "1.34e11"
    ball = st.lehman_sum(low_zeros, w, al)
    bad = list(low_zeros)
    bad[99] = bad[99] + arb("1e-6")
    moved = st.lehman_sum(bad, w, al)
    shift = abs(moved - ball)
    assert not bool(abs(moved - ball) < 10 * (ball.rad() + moved.rad()))
    bound = arb("1508.3") / low_zeros[99] * arb("1e-6")  # [Rev25] RieleS1 bound
    assert bool(shift <= bound)
    assert bool(shift > bound / 1000)


def test_second_order_term_matters(low_zeros):
    w, al = "727.952018", "1.34e11"
    a = st.lehman_sum(low_zeros, w, al)
    b = st.lehman_sum(low_zeros, w, al, second_order=False)
    assert bool(abs(a - b) > arb("1e-6"))


def test_grid_sum_equals_single_omega_sums(low_zeros):
    """The one-pass grid sum reproduces lehman_sum at both stored omegas."""
    sd, cp = st.SAOUTER_DEMICHEL, st.CHAO_PLYMEN
    g = st.lehman_sum_grid(low_zeros, [sd.omega, "727.951335792"], sd.alpha)
    one = st.lehman_sum(low_zeros, sd.omega, sd.alpha)
    assert abs(g[sd.omega] - one) <= arb("1e-30") + one.rad()
    g2 = st.lehman_sum_grid(low_zeros, [cp.omega], cp.alpha)
    one2 = st.lehman_sum(low_zeros, cp.omega, cp.alpha)
    assert abs(g2[cp.omega] - one2) <= arb("1e-30") + one2.rad()


def test_planted_fault_grid_shifted_by_one_step_fails(low_zeros):
    """A grid point one 5e-8 step away is distinguishable from the stored omega."""
    sd = st.SAOUTER_DEMICHEL
    one = st.lehman_sum(low_zeros, sd.omega, sd.alpha)
    shifted = st.lehman_sum_grid(low_zeros, ["727.95134005"], sd.alpha)["727.95134005"]
    assert not shifted.overlaps(one)


def test_zeros_file_hashes_to_the_digest(tmp_path, low_zeros):
    import gzip
    import hashlib

    f = tmp_path / "z.txt.gz"
    zl.write_zeros(low_zeros, f)
    assert hashlib.sha256(gzip.open(f).read()).hexdigest() == zl.zeros_digest(low_zeros)


def test_omega_grid_file_is_the_preregistered_one():
    import json

    d = json.loads((Path(__file__).resolve().parent / "omega_grid.json").read_text())
    assert d["decisive"] == ["727.951335792", "727.951335426"]
    assert d["control"] == "727.95134"
    assert len(d["omegas"]) == 83 and len(set(d["omegas"])) == 83


HERE = Path(__file__).resolve().parent


@pytest.mark.skipif(not (HERE / "shards" / "shard_020.json").exists(), reason="shard outputs absent")
def test_target_A_combined_result_is_pinned():
    import combine

    r = combine.combine("chao_plymen", HERE / "shards")
    assert r["checks"]["complete"] and r["gate"]["S_star_inside_ball"]
    assert r["lower_bounds"]["0.0001061"]["positive"]
    assert not r["lower_bounds"]["0.000106"]["positive"]


@pytest.mark.skipif(not (HERE / "shards_b2" / "shard_220.json").exists(), reason="B2 shards absent")
def test_B2_preregistered_evaluation_is_pinned():
    import evaluate_b2

    r = evaluate_b2.evaluate(HERE / "shards_b2")
    assert r["checks"]["complete"] and r["checks"]["every_shard_has_every_omega"]
    assert r["control"]["overlaps_recorded"]
    assert r["H_supported"] is False
    assert not r["decisive_rule"]["727.951335426"]["meets_rule"]
    gap = arb(r["decisive_rule"]["727.951335792"]["abs_diff_plus_rad"])
    assert bool(gap > arb("3.3e-5")) and bool(gap < arb("3.4e-5"))
    lb = r["lower_bounds_at_decisive_points"]["727.951335792"]
    assert lb["0.0000159"]["positive"] and not lb["0.0000158"]["positive"]
    assert not any(v["positive"] for v in r["lower_bounds_at_decisive_points"]["727.951335426"].values())
    assert all(f["gamma1_fault_leaves_own_ball"] for f in r["planted_faults"].values())


@pytest.mark.skipif(not (HERE / "shards" / "shard_020.json").exists(), reason="shard outputs absent")
def test_combine_refuses_a_duplicated_shard(tmp_path):
    """Planted fault: shard 10 replaced by a copy of shard 9. Arb's count still
    agrees, so completeness must come from the structural checks."""
    import shutil

    import combine

    for f in (HERE / "shards").glob("shard_*.json"):
        shutil.copy(f, tmp_path / f.name)
    shutil.copy(HERE / "shards" / "shard_009.json", tmp_path / "shard_010.json")
    r = combine.combine("chao_plymen", tmp_path)
    assert r["checks"]["turing_count_N(T)"] == 2_000_000
    assert not r["checks"]["contiguous_indices"]
    assert not r["checks"]["complete"]
    assert "complete" in combine.failed_checks(r["checks"])


# --- Added 2026-10-27, review of PR #360 -------------------------------------

#: The proved intervals [omega - eta, omega + eta] of targets A and B, exact.
EXACT_INTERVALS = {
    "A": ("727.952018", "0.0001061"),
    "B": ("727.951335792", "0.0000159"),
}


def _exact(key):
    from decimal import Decimal

    w, e = (Decimal(x) for x in EXACT_INTERVALS[key])
    return w - e, w + e


def _quote_contains_exact(lo: str, hi: str) -> bool:
    """A quoted [lo, hi] must contain the exact interval it overlaps (outward or exact)."""
    from decimal import Decimal

    qlo, qhi = Decimal(lo), Decimal(hi)
    for key in EXACT_INTERVALS:
        elo, ehi = _exact(key)
        if qlo <= ehi and elo <= qhi:
            return qlo <= elo and qhi >= ehi
    return False


def _quoted_intervals(text: str) -> list[tuple[str, str]]:
    import re

    return re.findall(r"log x in\s+\[(\d+\.\d+), (\d+\.\d+)\]", text)


def _case_log_entry() -> str:
    text = (HERE.parent / "README.md").read_text()
    start = text.index("### Hunt #152:")
    nxt = text.find("\n### Hunt #", start + 1)
    return text[start:] if nxt < 0 else text[start:nxt]


def test_quoted_intervals_contain_the_exact_ones():
    """Every 'log x in [lo, hi]' in RESULTS.md and the case log contains the
    exact [omega - eta, omega + eta] it reports, so no quote is rounded inward."""
    for name, text in (("RESULTS.md", (HERE / "RESULTS.md").read_text()),
                       ("case log", _case_log_entry())):
        quotes = _quoted_intervals(text)
        assert len(quotes) >= 2, name
        assert all(_quote_contains_exact(lo, hi) for lo, hi in quotes), (name, quotes)
        # both targets are quoted in each file
        assert any(_quote_contains_exact(lo, hi) and lo.startswith("727.9519") for lo, hi in quotes)
        assert any(_quote_contains_exact(lo, hi) and lo.startswith("727.95131") for lo, hi in quotes)


def test_planted_fault_an_inward_digit_fails_the_interval_check():
    """The first quote of B, lower end 727.9513199, was rounded inward."""
    assert _exact("B")[0] < __import__("decimal").Decimal("727.9513199")
    assert not _quote_contains_exact("727.9513199", "727.9513517")
    assert not _quote_contains_exact("727.9519120", "727.9521241")  # one digit inward at A
    assert _quote_contains_exact("727.951319892", "727.9513517")
    text = "pi(x) > li(x) for some x with log x in [727.9513199, 727.9513517]"
    assert not all(_quote_contains_exact(lo, hi) for lo, hi in _quoted_intervals(text))


def test_revers_saouter_demichel_row_1_59e_5_is_a_digit_slip():
    """[Rev25] tables: lower estimate = -1 - S* - Delta S1 - Delta S2 - R from the
    printed values. Every positive row agrees to 5e-9 except eta = 0.0000159,
    printed 0.000015987 where the printed values give 6.5986e-5."""
    cp, sd = arb(st.REVERS_S_STAR["chao_plymen"]), arb(st.REVERS_S_STAR["saouter_demichel"])
    d_cp = arb("1.89855e-5") + arb("4.9599e-11")
    d_sd = arb("2.6011e-5") + arb("4.9599e-11")
    rows = [(cp, d_cp, "6.14384e-3", "0.000390651"), (cp, d_cp, "6.14369e-3", "0.000390805"),
            (cp, d_cp, "6.14353e-3", "0.000390959"), (cp, d_cp, "6.20670e-3", "0.000327792"),
            (cp, d_cp, "6.40600e-3", "0.000128492"),
            (sd, d_sd, "2.79507e-3", "0.000101863"), (sd, d_sd, "2.79503e-3", "0.000101907"),
            (sd, d_sd, "2.79500e-3", "0.000101939"), (sd, d_sd, "2.79527e-3", "0.000101670")]
    for s, d, R, printed in rows:
        assert abs(-1 - s - d - arb(R) - arb(printed)) < arb("5e-9"), (R, printed)
    off = -1 - sd - d_sd - arb("2.83095e-3") - arb("0.000015987")
    assert abs(off - arb("4.9999e-5")) < arb("1e-8")


def _lb(p, S):
    return st.lower_bound_I(S, p)


def test_doors_A_is_binding_not_free():
    """RESULTS.md 'The doors' (corrected 2026-10-27): raising A toward the verified
    RH height costs margin through log A in R6; lowering it hits the cliff near
    sqrt(alpha omega)."""
    S_A = arb("[-1.006553479 +/- 3.85e-10]")
    lb = {A: _lb(dataclasses.replace(st.CHAO_PLYMEN, eta="0.0001061", A=A), S_A)
          for A in ("1.0e7", "1.022e7", "3.06e10", "3e12")}
    for A in lb:
        assert all(st.check_hypotheses(dataclasses.replace(st.CHAO_PLYMEN, eta="0.0001061",
                                                           A=A)).values())
    assert lb["1.0e7"] < 0 and lb["1.022e7"] > 0 and lb["3e12"] < 0
    assert lb["3.06e10"] < lb["1.022e7"]
    S_B = arb("[-1.00288927 +/- 5.39e-9]")
    pb = dataclasses.replace(st.SAOUTER_DEMICHEL, omega="727.951335792", eta="0.0000159")
    lbB = {A: _lb(dataclasses.replace(pb, A=A), S_B) for A in ("6.7e7", "6.85e7", "3e12")}
    assert lbB["6.7e7"] < 0 and lbB["6.85e7"] > 0 and lbB["3e12"] > 0
    assert lbB["3e12"] < arb("0.7") * lbB["6.85e7"]  # the margin falls by about 36%


def test_split_sums_add_up_to_lehman_sum(low_zeros):
    import s2_check

    w, al = "727.951335792", "6e12"
    s1, s2 = s2_check.split_sums(low_zeros, w, al)[len(low_zeros)]
    full = st.lehman_sum(low_zeros, w, al)
    first = st.lehman_sum(low_zeros, w, al, second_order=False)
    assert (s1 + s2).overlaps(full) and abs(s1 + s2 - full) < arb("1e-25")
    assert s1.overlaps(first) and abs(s1 - first) < arb("1e-25")
    assert bool(s2 > 0)


S2_FILE = HERE / "s2_first20000.json"


@pytest.mark.skipif(not S2_FILE.exists(), reason="S2 data absent")
def test_s2_data_reproduces_from_the_driver():
    """The committed S2 file's 1000-zero checkpoint is what the driver computes now."""
    import json

    import s2_check

    d = json.loads(S2_FILE.read_text())
    assert d["n"] == 20000
    g, _ = zl.arb_zeros(1, 1000, 5000, 64)
    for label, (w, al) in s2_check.POINTS.items():
        s1, s2 = s2_check.split_sums(g, w, al)[1000]
        rec = d["points"][label]["by_count"]["1000"]
        assert s1.overlaps(arb(rec["S1"])) and s2.overlaps(arb(rec["S2"])), label


@pytest.mark.skipif(not (S2_FILE.exists() and (HERE / "shards_b2" / "shard_220.json").exists()
                         and (HERE / "shards" / "shard_020.json").exists()),
                    reason="S2 data or shards absent")
def test_sign_slip_in_revers_6_3_post_hoc():
    """Post-hoc, measured (RESULTS.md sections 3, 7, 8): Revers's 6.3 S* is the
    Saouter-Demichel first-order value minus S2, not plus; our S1 matches theirs."""
    import s2_check

    r = s2_check.compare(S2_FILE, HERE / "shards", HERE / "shards_b2")
    a = {k: arb(v) for k, v in r.items() if isinstance(v, str) and v.startswith("[")}
    assert abs(a["SD_minus_S2_minus_Sstar (sign-slip identity)"]) < arb("2e-9")
    # planted fault: Theorem 3.1's own sign does not reproduce S*
    assert abs(a["SD_plus_S2_minus_Sstar (Theorem 3.1's sign)"]) > arb("3e-5")
    assert abs(a["gap_minus_two_S2"]) < arb("5e-8")
    e2e = abs(a["our_S1_minus_SD (end-to-end check of the 2.2e7 zeros)"])
    assert bool(e2e > arb("4.5e-8")) and bool(e2e < arb("4.8e-8"))
    assert abs(a["A_our_S1_minus_CP (CP printed to 6 decimals)"]) <= arb("5e-7")
    assert abs(a["A_S_minus_Sstar (plus S2, as Theorem 3.1)"]) < arb("2e-10")
    assert abs(a["A_S_minus_2S2_minus_Sstar (minus S2 convention)"]) > arb("3e-5")
    alt = r["alt_omega_727.9513358_interpolated_S_minus_Sstar"]
    assert -8.1e-7 < alt < -7.9e-7
    assert r["alt_over_sign_slip_residual"] > 500
    assert r["S2_tail_estimate_B"] < 2.5e-7
