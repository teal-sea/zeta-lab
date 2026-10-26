"""Hunt #136, lane eulerstep: every number EULER_STEP.md states is pinned here.

All checks are live.  The fast ones recompute small ranges on every run; the
``slow`` ones recompute the full ranges the document quotes (every prime ideal
of norm at most 10^4, the per-prime route to norm 1000, the brute-force C_p
ranges).  Planted faults show that each family of checks can fail.  The
document itself is read too: its line numbers, its fractions, its rival table
and its headline counts (the doc-sync tests at the end of the fast tier).

Run from the repo root with one process (the Lean lane may be building):

    .venv/bin/python -m pytest -q -n0 hunts/below_seven_eighths/test_euler_step.py
    .venv/bin/python -m pytest -q -n0 -m slow hunts/below_seven_eighths/test_euler_step.py
"""

from __future__ import annotations

import json
import os
import re
import sys
from collections import Counter
from fractions import Fraction as Fr

import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)
ROOT = os.path.dirname(os.path.dirname(HERE))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

import euler_step as es  # noqa: E402

needs_paper = pytest.mark.skipif(not es.paper_available(), reason="pinned paper.tex not present on this machine")
needs_flint = pytest.mark.skipif(not es.HAVE_FLINT, reason="python-flint absent: no exact fast products, no balls")

DOC = os.path.join(HERE, "EULER_STEP.md")

#: counts the document quotes; each is asserted against a computation below
#: (the slow ones by the slow tier) and against the document by test_doc_sync
HEADLINE = {
    "citations": 202,
    "scan_lines": 52,
    "ideals_1e4": 1234, "split_1e4": 1222, "inert_1e4": 12,
    "ideals_1000": 165,
    "table_cases": 7128, "table_row_cases": 528, "table_omitted": 6600,
    "reciprocity_primes": 93, "reciprocity_pairs": 8556, "reciprocity_minus": 3600,
    "inert_ells": 616, "rational_primes_1e4": 1229, "epstein_norms": 329,
    "limit_control_differences": 8, "grid_points": 54,
    # 16 in es.planted_faults() and 3 on the instruments that read the paper and
    # the document (test_citation_checker_is_line_specific,
    # test_line_number_scanner_catches_planted_numbers,
    # test_doc_sync_catches_planted_changes)
    "faults": 19,
}


def _doc_text():
    if not os.path.isfile(DOC):
        pytest.skip("document not present")
    with open(DOC, encoding="utf-8") as fh:
        return fh.read()


def _strip_code_and_dates(text: str) -> str:
    text = re.sub(r"`[^`]*`", " ", text)  # code spans: the hash, file names, test names
    return re.sub(r"\d{4}-\d{2}-\d{2}(?:T\d{2}:\d{2}Z)?", " ", text)  # dates


# ---------------------------------------------------------------------------
# the source
# ---------------------------------------------------------------------------

@needs_paper
def test_paper_is_the_pinned_source():
    assert es.paper_sha256() == es.PAPER_SHA256
    with open(es.PAPER, encoding="utf-8") as fh:
        assert len(fh.read().split("\n")) - 1 == es.PAPER_LINES


@needs_paper
def test_every_citation_is_on_its_line():
    res = es.check_citations()
    assert len(res) == len(es.CITATIONS) == HEADLINE["citations"]
    assert [k for k, v in res.items() if not v] == []


@needs_paper
def test_citation_checker_is_line_specific():
    """Planted fault: every citation moved one line down, and every one moved
    one line up, must fail, and so must one wrong line.  A checker weakened to
    a search of the whole file would let them pass and turn this red."""
    assert es.citation_faults() == {"every_citation_shifted_down_fails": True,
                                    "every_citation_shifted_up_fails": True,
                                    "one_wrong_line_fails": True}


def line_number_candidates(text: str) -> set:
    """Integers of three to five digits that could be paper line numbers:
    outside code spans and dates, not part of a decimal (300.5), a thousands
    group (16,677) or a fraction (401/600), not an exponent or product factor
    (X^25, 25*121), a hunt number (#136) or a signed number (-150); a number
    ending a sentence and both ends of a hyphenated range count."""
    text = _strip_code_and_dates(text)
    out = set()
    for m in re.finditer(r"\d+(?:[.,/]\d+)*", text):
        tok = m.group(0)
        if any(c in tok for c in ".,/"):
            continue
        s, e = m.span()
        before = text[s - 1] if s > 0 else " "
        after = text[e] if e < len(text) else " "
        if before in "^*#_" or before.isalpha() or after in "^*":
            continue
        if before == "-" and not (s >= 2 and text[s - 2].isdigit()):
            continue  # a minus sign, not the hyphen of a range
        if 3 <= len(tok) <= 5:
            out.add(int(tok))
    return out


#: integers of three to five digits in EULER_STEP.md that are counts, sizes or
#: ranges, not paper line numbers (every other such integer must be cited):
#: norm and height bounds 100, 121, 200, 300, 500, 1000, 2000; case, pair and
#: prime counts 104, 160, 165, 231, 329, 528, 611, 616, 617, 1222, 1229, 1234,
#: 3600, 6600, 7128, 8556; and 202, the number of citations
NOT_LINE_NUMBERS = {
    100, 104, 121, 160, 165, 200, 202, 231, 300, 329, 500, 528, 611, 616, 617,
    1000, 1222, 1229, 1234, 2000, 3600, 6600, 7128, 8556,
}


def uncited_line_numbers(text: str) -> list:
    cited = {n for n, _ in es.CITATIONS.values()}
    return sorted(n for n in line_number_candidates(text) if n not in cited and n not in NOT_LINE_NUMBERS)


def test_every_line_number_in_the_document_is_a_cited_line():
    """EULER_STEP.md says every line number it gives is one of CITATIONS."""
    text = _doc_text()
    assert uncited_line_numbers(text) == []
    # and every listed count really occurs, so the list cannot hide a line number
    assert NOT_LINE_NUMBERS <= line_number_candidates(text)


def test_line_number_scanner_catches_planted_numbers():
    """Planted fault (the verifier's two strings): a line number that ends a
    sentence, and a hyphenated range of two line numbers, appended to a copy
    of the document, must be reported; the scanner must also leave alone the
    shapes that are not line numbers."""
    text = _doc_text()
    assert line_number_candidates("See line 9998.") == {9998}
    assert line_number_candidates("See lines 9998-9999.") == {9998, 9999}
    assert uncited_line_numbers(text + "\nSee line 9998.\n") == [9998]
    assert uncited_line_numbers(text + "\nSee lines 9998-9999.\n") == [9998, 9999]
    assert line_number_candidates("-101/100, 300.5, 16,677, X^25, 25*121, #136, 2026-10-21, D = -150") == set()


@needs_paper
def test_paper_tex_has_no_appendix():
    """The 11/12 paper's Appendix A.1 identity is not in paper.tex; its 7/8
    counterpart is (4.7) of Lemma 4.4."""
    assert es.paper_has_appendix() is False


def test_citation_line_numbers_quoted_in_the_document():
    c = es.CITATIONS
    assert c["lem42_head"][0] == 766 and c["lem44_head"][0] == 935
    assert c["eq47_a"][0] == 966 and c["lem71_hyp"][0] == 4011
    assert c["region_two"][0] == 4056 and c["H_eta_78"][0] == 5525
    assert c["separation"][0] == 3995 and c["S_contains_6"][0] == 591
    # local data (7.6) is lines 3861 to 3867; Section 7.2 is lines 3847 to 4199
    assert c["local_params_Q_j"][0] == 3861 and c["local_params_Wloc"][0] == 3867
    assert es.SECTION_72 == (c["sec72_head"][0], c["sec72_last"][0]) == (3847, 4199)


# ---------------------------------------------------------------------------
# the consumers of Lemma 7.1
# ---------------------------------------------------------------------------

@needs_paper
def test_consumer_scan_is_complete():
    """Every line outside Section 7.2 that names the lemma, a label defined
    in Section 7.2, an Euler region, D_1 or D_2 is in CONSUMER_SCAN_LINES,
    and nothing else is."""
    scan = es.consumer_scan()
    assert set(scan) == set(es.CONSUMER_SCAN_LINES)
    assert len(scan) == HEADLINE["scan_lines"]
    cited = {n for n, _ in es.CITATIONS.values()}
    assert set(scan) <= cited


def test_consumer_groups_in_the_document():
    """Section 1.1 of the document places each scanned line in the group
    CONSUMER_SCAN_LINES gives it, and in no other."""
    groups = Counter(es.CONSUMER_SCAN_LINES.values())
    assert groups == {"pointer": 8, "region_one": 12, "principal": 11, "every_row": 15, "identity": 6}
    text = _doc_text()
    section = text.split("Where it is consumed")[1].split("Second-order uses")[0]
    bullets = {"pointer": "- Pointers", "region_one": "- Region one only", "principal": "- Region two at the principal",
               "every_row": "- Region two at every row", "identity": "- (7.13) used as an identity"}
    starts = sorted((section.index(b), g) for g, b in bullets.items())
    for i, (pos, g) in enumerate(starts):
        end = starts[i + 1][0] if i + 1 < len(starts) else len(section)
        found = {int(n) for n in re.findall(r"\d{3,5}", section[pos:end])} & set(es.CONSUMER_SCAN_LINES)
        assert found == {n for n, gg in es.CONSUMER_SCAN_LINES.items() if gg == g}, g


# ---------------------------------------------------------------------------
# Lemma 4.2, (4.6), (4.7) at primes
# ---------------------------------------------------------------------------

@needs_flint
def test_prime_gauss_identities_to_norm_1000():
    r = es.run_prime_gauss(1000, balls=True, jacobi=True)
    assert r["counts"] == {"split": 160, "inert": 5}
    assert r["fails"] == []


@needs_flint
def test_appendix_a1_form_at_every_prime_to_norm_1000():
    primes = es.primes_of_norm_upto(1000)
    assert len(primes) == HEADLINE["ideals_1000"]
    assert [P.pi for P in primes if not es.a1_form_at_prime(P)] == []


def test_prime_ideal_counts_to_norm_10000():
    """The counts of the full range (the identities there are the slow tier)."""
    primes = es.primes_of_norm_upto(10 ** 4)
    kinds = Counter(P.kind for P in primes)
    assert len(primes) == HEADLINE["ideals_1e4"]
    assert (kinds["split"], kinds["inert"]) == (HEADLINE["split_1e4"], HEADLINE["inert_1e4"])
    assert len({P.ell for P in primes if P.kind == "split"}) == 611


def test_inert_reduction_premises_to_ell_10000():
    """G_r = ell at every inert prime 5 <= ell <= 10^4 (616 primes), from the
    derived reduction and the exact symbols chi_p(4) = chi_p(-1) = 1."""
    ells = [l for l in es.primes_upto(10 ** 4) if l >= 5 and l % 3 == 2]
    assert len(ells) == HEADLINE["inert_ells"]
    bad = [l for l in ells if not all(es.inert_derived_checks(l).values())]
    assert bad == []


def test_inert_reduction_against_direct_sums_small():
    r = es.inert_bruteforce(100, balls=False)
    assert r["n"] == 12 and r["bad"] == []


def test_additive_character_against_the_complex_form():
    """The exact index route for e(w/m) agrees with exp(4 pi i Im z/sqrt 3)
    (paper line 613) on 400 random (w, m); a float comparison, measured."""
    assert es.additive_character_crosscheck(400) < 1e-9


@needs_flint
def test_gamma_of_p_powers_by_direct_summation_small():
    """Gamma(p^t) summed over O/p^t for t <= 3 against the four-term formula,
    and (4.6) G(p^3) = gamma_3(p) exactly, at both primes over each split
    ell <= 43 and at the inert 5 and 11 (14 prime ideals)."""
    r = es.p_power_quadratic_run(43, tmax=3, inert=((5, 3), (11, 3)))
    assert r == {"n": 14, "bad": []}
    # the entry is computed, not hard-coded: |G(p)| = 1 is an exact product now
    assert "G_unit" not in es.prime_gauss_checks(es.split_primes(7)[0], balls=False)
    assert es.prime_gauss_checks(es.split_primes(7)[0], balls=False)["G_ABS"]


def test_jacobi_route_and_values_at_7():
    P = es.split_primes(7)[0]
    assert P.pi == (-2, -3)
    G2 = es.gauss_vec(P.pi, [(P, 2)])
    assert (G2 * G2 * G2).as_scalar() == (14, 21) == es.emul(es.eneg(P.pi), (7, 0))
    assert all(es.jacobi_checks(P).values())


# ---------------------------------------------------------------------------
# Lemma 7.1: generic, per prime, brute force
# ---------------------------------------------------------------------------

def test_lemma71_generic_all_rows():
    res = es.lemma71_symbolic(trunc=(25, 3, 30))
    for j in range(6):
        assert res[j]["P_equal"] and res[j]["Pstar_equal"], j
        assert res[j]["eta_degree_equals_X_degree"], j


def test_family_table_716_complete_on_a_window():
    """Table (7.16) has ten rows (lines 4089 to 4098).  Every summand of (7.10)
    with r <= 10, each family, k <= 2, j in 0..5 and m <= r + 3 equals R^r times
    the table's entries, and zero where no row applies (line 4084).  Row 1 holds
    for every j (line 4083) and row 6 on its j-dependent m range; both are
    exercised at every j."""
    r = es.family_table_complete(rmax=10, kmax=2, mspan=3)
    assert r["n_rows"] == 10 and len(es.TABLE_716_ROWS) == 10
    assert r["checked"] == HEADLINE["table_cases"] == 72 * 99
    assert r["row_cases"] == HEADLINE["table_row_cases"] and r["omitted_cases"] == HEADLINE["table_omitted"]
    assert r["bad"] == []
    js = r["js_by_row"]
    assert js[0] == [0, 1, 2, 3, 4, 5] and js[5] == [0, 1, 2, 3, 4, 5]
    assert [js[i] for i in (1, 2, 3, 4, 6, 7, 8, 9)] == [[5], [0], [0], [1], [2], [3], [3], [4]]


def test_period_structure_closes_the_truncation():
    assert es.period_ratio_check(40) == {"parity": True, "lift_ratio_Q6": True}


def test_omega_p_is_minus_one_exactly_at_7_mod_12():
    for P in es.primes_of_norm_upto(1000):
        om = 1 if P.chi_exp((-1, 0)) == 0 else -1
        assert (om == -1) == (P.Q % 12 == 7), P


def test_support_of_the_principal_row():
    sup = es.lemma71_support()
    t0 = sorted({s[0] for s in sup[0]})
    assert t0 == [1, 6, 7, 12, 13, 18, 19, 24, 25]
    # the first monomials carrying eta(p)^6: X^6 Z^6 (k = 0, m = 1) and X^6 W Z^6
    s6 = sorted(s for s in sup[0] if s[0] == 6)
    assert s6[0] == (6, 0, 6) and (6, 1, 6) in s6


@needs_flint
def test_lemma71_with_true_gauss_sums_to_norm_100():
    primes = es.primes_of_norm_upto(100)
    assert len(primes) == 23
    for P in primes:
        assert all(es.lemma71_at_prime(P).values()), P


def test_cp_and_gauss_lift_bruteforce_small():
    P7 = es.split_primes(7)[0]
    assert es.cp_bruteforce(P7, 3, 2) == {"checked": 54, "bad": []}
    assert es.gauss_lift_bruteforce(P7, 4) == []
    P5 = es.inert_prime(5)
    assert es.cp_bruteforce(P5, 2, 2) == {"checked": 36, "bad": []}


def test_rational_identities_717_and_part_two():
    assert es.local_rational_identities() == {"7.17": True, "16.4": True, "16.8": True, "16.8_p_divides_u": True}


def test_region_two_exponents_are_the_maxima():
    r = es.region_bookkeeping()
    assert r["R_exp_region1"] and r["27/25"] and r["3/2-3x"]
    assert r["good_region2"] and r["ramified_region2"] and r["tail"]
    assert r["region2_good_max"] == Fr(-363, 200)
    assert r["region2_ramified_max"] == Fr(-33, 40)


def test_region_one_bounds_at_the_minimal_vertices():
    a = es.region_one_bookkeeping(Fr(1, 100))
    assert a["good_max"] == Fr(-101, 100) and a["ramified_max"] == Fr(-1, 100)
    b = es.region_one_bookkeeping(Fr(1, 1000))
    assert b["good_max"] == Fr(-1001, 1000) and b["ramified_max"] == Fr(-1, 1000)
    c = es.region_one_bookkeeping(Fr(1, 20))
    assert c["good_max"] == Fr(-21, 20) and c["ramified_max"] == Fr(-3, 100)
    assert all(d["good_ok"] and d["ramified_ok"] for d in (a, b, c))


def test_where_the_euler_step_binds():
    """The product over the primes not dividing u converges normally for
    x_r > 2/3 at (w, z) = (1, 1/6) and for x_r > 401/600 at the region-two
    corner."""
    assert es.euler_floor(0, Fr(1), Fr(1, 6)) == Fr(2, 3)
    assert es.euler_floor(0, Fr(19, 20), Fr(33, 200)) == Fr(401, 600)
    best = es.defect_exponents(0, (Fr(7, 8), Fr(1), Fr(1, 6)))
    assert best[0] == Fr(-15, 8)
    # the binding monomial below x = 4/5 is R(1 - 1/Q) = Q^{4 - 6x - 6z}
    assert es.defect_exponents(0, (Fr(7, 10), Fr(1), Fr(1, 6)))[1] == (Fr(4), 6, 0, 6)
    assert Fr(7, 8) - Fr(2, 3) == Fr(5, 24) and Fr(7, 8) - Fr(401, 600) == Fr(31, 150)
    # the two leading monomials cross at x = 4/5, both at exponent -9/5
    assert es.defect_exponents(0, (Fr(4, 5), Fr(1), Fr(1, 6)))[0] == Fr(-9, 5)
    assert 3 - 6 * Fr(4, 5) == -1 - Fr(4, 5) == Fr(-9, 5)


def test_row_requirements_every_row():
    """Section 6's table: R1 to R5 at the residue point and the corner, for
    every row u.  At p not dividing u the j = 0 factor keeps rho = chi_p(u)
    formal; at p | u every j = 1..5 has the same threshold-0 floors.  The j = 1
    factor has the j = 0 threshold -1 floors, and j = 2..5 reach -33/40 at the
    corner with x_r = 7/8, above -1."""
    r = es.row_requirements()
    assert r["residue_point"] == {"R1": Fr(2, 3), "R2": Fr(1, 2), "R2_by_j": {j: Fr(1, 2) for j in range(1, 6)},
                                  "R3": Fr(1, 2), "R4": Fr(1, 2), "R5": Fr(3, 5)}
    assert r["corner"] == {"R1": Fr(401, 600), "R2": Fr(301, 600), "R2_by_j": {j: Fr(301, 600) for j in range(1, 6)},
                           "R3": Fr(301, 600), "R4": Fr(301, 600), "R5": Fr(301, 500)}
    for (w, z) in es.FLOOR_POINTS.values():
        assert es.euler_floor(1, w, z) == es.euler_floor(0, w, z)
    corner78 = (Fr(7, 8), Fr(19, 20), Fr(33, 200))
    assert [es.defect_exponents(j, corner78)[0] for j in range(2, 6)] == [Fr(-33, 40)] * 4
    # the rho exponent really is free in the j = 0 series (so every row u is covered)
    R, Hm1 = es._hdefect_series(0)
    assert {k[R.names.index("rho")] for k in Hm1.t} != {0}


def test_bounded_below_floor_of_the_principal_row():
    """H_p - 1 = O(Q^{-delta}), delta > 0 (H_p bounded away from zero for large
    Q, line 9054) exactly when x_r > 1/2 at (1, 1/6) and x_r > 301/600 at the
    region-two corner; the majorant of line 8749 needs the stronger 2/3 and
    401/600 of test_where_the_euler_step_binds."""
    assert es.euler_floor(0, Fr(1), Fr(1, 6), threshold=0) == Fr(1, 2)
    assert es.euler_floor(0, Fr(19, 20), Fr(33, 200), threshold=0) == Fr(301, 600)


def test_principal_multiplier_part_two():
    """Part II's principal local factor (lines 9051 to 9077), from the exact
    expansion of B_p + 1 = (G_p + H_p)/H_p at u = 1.

    The largest exponent equals the largest of the four exponents of line
    9068 at all 54 grid points; B_p + 1 decays (delta > 0) exactly for
    x_r > 3/5 at the residue point and x_r > 301/500 at the corner; at
    x_r = 7/8 at the corner the largest exponent is -7/8, attained only by
    D = eta(p) Q^{-x}, so the 7/8 of line 9074 is the region's own x-floor."""
    r = es.principal_multiplier_report()
    assert r["n_grid"] == HEADLINE["grid_points"] and r["grid_bad"] == []
    assert r["floor_residue_point"] == Fr(3, 5)
    assert r["floor_region_two"] == Fr(301, 500)
    assert r["max_at_7_8_floors"] == Fr(-7, 8)
    assert r["argmax_at_7_8_floors"] == [(Fr(0), 1, 0, 0)]
    # the four cited exponents at the corner of D_2: "Each is at most -7/8"
    corner = (Fr(7, 8), Fr(19, 20), Fr(33, 200))
    assert es.cited_principal_exponents(corner) == [Fr(-7, 8), Fr(-99, 100), Fr(-273, 200), Fr(-47, 50)]
    assert max(es.cited_principal_exponents((Fr(7, 8), Fr(1), Fr(1, 6)))) == Fr(-7, 8)
    # the floors are where the binding cited exponent 4 - 5x - 6z vanishes
    assert 4 - 5 * Fr(3, 5) - 6 * Fr(1, 6) == 0 and 4 - 5 * Fr(301, 500) - 6 * Fr(33, 200) == 0
    # the Part II margin: kappa_P = (7/16) l/K = 7/(96K) below (7/8) l/K = 7/(48K), l = 1/6
    assert Fr(7, 16) * Fr(1, 6) == Fr(7, 96) and Fr(7, 8) * Fr(1, 6) == Fr(7, 48)


def test_principal_series_against_direct_evaluation():
    """Second route, measured: the truncated series for B_p + 1 against a
    direct complex-float evaluation of (7.11), (7.12) and G_p at Q = 7."""
    assert es.principal_multiplier_float_crosscheck() < 1e-9


def test_route_parameters_quoted():
    import inspect

    assert inspect.signature(es.lemma71_at_prime).parameters["trunc"].default == (13, 2, 18)
    assert inspect.signature(es.lemma71_symbolic).parameters["trunc"].default == (25, 3, 30)
    # H_p - 1 to X^19 W^3 Z^24; B_p + 1 built to X^13 W^2 Z^18 and cut below X^13
    assert inspect.signature(es._hdefect_series).parameters["trunc"].default == (19, 3, 24)
    assert inspect.signature(es._principal_series).parameters["trunc"].default == (13, 2, 18)
    R, B1, _ = es._principal_series()
    assert max(k[R.nsym] for k in B1.t) == 12
    # the principal grid: x_r from 61/100 to 3/2 at six (w_r, z_r), the residue
    # point and the region-two corner among them
    xs = sorted({p[0] for p in es.PRINCIPAL_GRID})
    wz = {(p[1], p[2]) for p in es.PRINCIPAL_GRID}
    assert xs[0] == Fr(61, 100) and xs[-1] == Fr(3, 2) and len(wz) == 6
    assert (Fr(1), Fr(1, 6)) in wz and (Fr(19, 20), Fr(33, 200)) in wz


def test_hunt120_quotes_the_appendix_identity():
    path = os.path.join(ROOT, "hunts", "qrh_rival_step", "RESULTS.md")
    if not os.path.isfile(path):
        pytest.skip("hunt #120 not present")
    with open(path, encoding="utf-8") as fh:
        text = " ".join(fh.read().split())  # the quote spans line breaks
    assert "we derive the following identity in Appendix A.1" in text
    assert "mu(n) gamma_{-1}(n) = chi_n(-1) G(n)^{-1} conj(alpha(n)) gamma_2(n)" in text


# ---------------------------------------------------------------------------
# squarefree composites, reciprocity, pair phases
# ---------------------------------------------------------------------------

def _combos():
    P7, P7b = es.split_primes(7)
    P13, P13b = es.split_primes(13)
    P19 = es.split_primes(19)[0]
    P5, P11 = es.inert_prime(5), es.inert_prime(11)
    return [[P7, P13], [P7, P7b], [P7, P5], [P13, P19], [P7, P13, P19], [P5, P11], [P7, P13b, P5]]


@needs_flint
def test_eq47_and_the_1112_form_on_composites():
    combos = _combos()
    assert len(combos) == 7
    for c in combos:
        r = es.composite_signal_checks(c, balls=True)
        assert all(r.values()), ([P.Q for P in c], r)


def test_crt_rule_for_gamma_j():
    P7, P7b = es.split_primes(7)
    P13 = es.split_primes(13)[0]
    P19 = es.split_primes(19)[0]
    P5 = es.inert_prime(5)
    for A, B in (([P7], [P13]), ([P7, P13], [P19]), ([P7], [P7b]), ([P5], [P7])):
        assert all(es.crt_checks(A, B).values())


def test_sextic_reciprocity_to_norm_500():
    r = es.reciprocity_checks(500)
    assert r["primes"] == HEADLINE["reciprocity_primes"] and r["pairs"] == HEADLINE["reciprocity_pairs"]
    assert r["bad"] == [] and r["supplement_bad"] == []
    ps = es.primes_of_norm_upto(500)
    neg = sum(es.rfrak(a.pi, b.pi) == -1 for a in ps for b in ps if a.pi != b.pi)
    assert neg == HEADLINE["reciprocity_minus"]  # the bicharacter is not trivially one on these pairs


def test_lemma43_table_and_bicharacter():
    assert es.lemma43_table() == {"table": True, "bichar": True, "mod4": True,
                                  "square_invariance": True, "n_odd_classes": 12}


def test_pair_phase_paragraph():
    P7, P7b = es.split_primes(7)
    P13 = es.split_primes(13)[0]
    P19 = es.split_primes(19)[0]
    P5 = es.inert_prime(5)
    r = es.pair_phase_checks([P7, P13, P19, P5, P7b], trials=300)
    assert r == {"trials": 300, "bad": {"i": 0, "iii": 0, "iv": 0}}


# ---------------------------------------------------------------------------
# p = 3, the excluded primes, the transfer
# ---------------------------------------------------------------------------

def test_transfer_local_factors_every_prime_to_10000():
    r = es.transfer_checks(10 ** 4)
    assert r["kinds"] == {"split": 611, "inert": 617, "ramified": 1}
    assert sum(r["kinds"].values()) == HEADLINE["rational_primes_1e4"]
    assert r["bad"] == []


def test_the_symbol_is_undefined_at_2_and_3():
    r = es.excluded_primes()
    assert r["lambda_field_order"] == 3 and r["two_field_order"] == 4
    assert r["lambda_6_does_not_divide"] and r["two_6_does_not_divide"]
    assert r["omega_is_1_mod_lambda"] and r["minus1_is_1_mod_2"] and r["no_primary_at_lambda"]
    with pytest.raises(ValueError):
        es.Prime((2, 0))
    with pytest.raises(ValueError):
        es.Prime(es.LAMBDA)


# ---------------------------------------------------------------------------
# rivals
# ---------------------------------------------------------------------------

@pytest.fixture(scope="module")
def rivals():
    return es.rival_report()


def test_dh_rival(rivals):
    r = rivals["DH"]
    assert r["conductor_primes"] == (5,)
    assert r["n_norms"] == 22 and r["n_norms_failing_C"] == 12
    assert 25 not in r["first_failing_t_principal_row"]  # the prime above 5 is in S
    assert r["first_failing_t_principal_row"][7] == 6
    assert r["first_failing_t_principal_row"][19] is None
    assert r["first_failing_t_by_j_at_7"] == {0: 6, 1: 6, 2: 3, 3: 3, 4: 4, 5: 6}
    assert r["n_pairs"] == 231 and r["n_pairs_failing_M"] == 66
    assert r["first_pairs_failing_M"][0] == (7, 13)
    assert r["n_conjugate_pairs"] == 21 and r["n_conjugate_pairs_failing_M"] == 12
    # the first coprime pair of good ideals that fails, by the product of the
    # norms, is the conjugate pair over 7, not (7, 13)
    assert r["first_conjugate_pair_failing_M"] == 7
    assert r["first_coprime_pair_failing_M"] == (49, "conjugate pair", (7, 7))
    assert r["n_norms_nonunit_U"] == 12
    assert r["moebius_over_F"] == (49, 3) and r["moebius_ideals_checked_F"] == 58
    n, b, mua = r["moebius_first_difference"]
    assert n == 4 and str(b) == "k**2 + 1" and mua == 0
    assert rivals["kappa_agrees_with_lab"] is True
    assert rivals["kappa_minpoly"] == "k**4 + 2*k**3 - 6*k**2 - 2*k + 1"


def test_epstein_rival(rivals):
    r = rivals["Epstein_-15"]
    assert r["conductor_primes"] == (3, 5) and r["n_norms"] == 22
    assert r["n_norms_failing_C"] == 21
    assert r["first_failing_t_principal_row"][7] == 6
    assert r["first_failing_t_by_j_at_7"] == {0: 6, 1: 6, 2: 6, 3: 4, 4: 4, 5: 6}
    assert r["n_pairs"] == 231 and r["n_pairs_failing_M"] == 0
    assert r["n_conjugate_pairs"] == 21 and r["n_conjugate_pairs_failing_M"] == 21
    assert r["first_conjugate_pair_failing_M"] == 7
    assert r["n_norms_nonunit_U"] == 21
    assert r["moebius_over_F"] == (49, 3)
    n, b, mua = r["moebius_first_difference"]
    assert (n, b, mua) == (4, -3, 0)


def test_controls(rivals):
    c = rivals["chi5_control"]
    assert c["n_norms"] == 22 and c["n_norms_failing_C"] == 0 and c["n_pairs_failing_M"] == 0
    assert c["n_conjugate_pairs_failing_M"] == 0 and c["moebius_first_difference"] is None
    assert c["moebius_over_F"] is None and c["moebius_ideals_checked_F"] == 58
    assert c["n_norms_nonunit_U"] == 0 and c["nonunit_norms_first"] == []
    d = rivals["Epstein_-19_control"]
    assert d["conductor_primes"] == (19,) and d["n_norms"] == 22 and 19 not in d["first_failing_t_principal_row"]
    assert d["n_norms_failing_C"] == 22 and d["n_pairs"] == 231 and d["n_pairs_failing_M"] == 0
    assert d["first_failing_t_principal_row"][7] == 6
    assert d["n_conjugate_pairs"] == 20 and d["n_conjugate_pairs_failing_M"] == 20 and d["n_norms_nonunit_U"] == 22
    assert d["moebius_first_difference"][0] == 4 and d["moebius_over_F"] == (49, 3)


def test_limit_control_completely_multiplicative_but_not_a_character(rivals):
    """What the step does not separate: a completely multiplicative unimodular
    function that agrees with chi_5 o N up to norm 100 and is 1 at larger
    primes passes every local test, yet differs from chi_5 o N at 8 good norms
    up to 200.  That it is no Hecke character is a density argument applied to
    the function itself (inferred); the two values it uses are pinned."""
    c = rivals["truncated_chi5_control"]
    assert c["n_norms_failing_C"] == 0 and c["n_pairs_failing_M"] == 0
    assert c["n_conjugate_pairs_failing_M"] == 0 and c["moebius_first_difference"] is None
    assert c["moebius_over_F"] is None
    assert c["n_norms_nonunit_U"] == 0 and c["nonunit_norms_first"] == []
    assert es.TRUNCATED_CHI5_CUTOFF == 100
    diffs = es.truncated_control_differences(200)
    assert diffs == [103, 109, 127, 139, 157, 163, 193, 199]
    assert len(diffs) == HEADLINE["limit_control_differences"]
    v = es.truncated_control_values()
    assert v["is_i_at_norm_7"] and v["one_above_cutoff"]


def test_where_each_rival_fails_the_prime_power_test(rivals):
    """DH fails exactly at the norms with chi_5(N p) = +-i (N p = 2, 3 mod 5);
    the Epstein function exactly at the split norms."""
    dh = rivals["DH"]["first_failing_t_principal_row"]
    assert {Q for Q, t in dh.items() if t is not None} == {Q for Q in dh if Q % 5 in (2, 3)}
    assert {t for t in dh.values() if t is not None} == {6}
    ep = rivals["Epstein_-15"]["first_failing_t_principal_row"]
    split = {P.Q for P in es.primes_of_norm_upto(200) if P.kind == "split"}
    assert len(split) == 21
    assert {Q for Q, t in ep.items() if t is not None} == split
    assert rivals["Epstein_-19_control"]["moebius_first_difference"] == (4, -1, 0)


def test_epstein_on_norms_of_F():
    r = es.epstein_norm_form_check(2000)
    assert r == {"n_norms": HEADLINE["epstein_norms"], "equal": True}


def test_rival_values_quoted():
    v = es.rival_values()
    assert str(v["dh_a7"]) == "k" and v["dh_a7_6"] == -1 and str(v["dh_a13"]) == "-k"
    assert v["dh_a91"] == 1 and v["dh_a4"] == -1 and v["dh_a121"] == 1
    # the conjugate pair over 7: a(49) = -1 against a(7)^2 = kappa^2
    assert v["dh_a49"] == -1 and v["dh_a49_differs_from_a7_squared"] and v["dh_a25"] == 0
    assert v["dh_kappa6_plus_1_nonzero"] and v["dh_kappa2_plus_1_nonzero"]
    assert (v["ep_a2"], v["ep_a3"], v["ep_a4"], v["ep_a6"]) == (0, 0, 3, 2)
    assert (v["ep_a7"], v["ep_a7_4"], v["ep_a7_6"], v["ep_a19"], v["ep_a49"]) == (0, 1, 1, 2, 1)
    assert abs(v["kappa_float"] - 0.2840790438404123) < 1e-15


def test_epstein_coefficients_two_routes():
    r = es.epstein_formula_check(2000)
    assert r["D15"] and r["D19"] and r["lab_route"]
    assert r["a(7^6)_brute"] == r["a(7^6)_formula"] == 1


def test_hunt120_numbers_quoted():
    path = os.path.join(ROOT, "hunts", "qrh_rival_step", "results.json")
    if not os.path.isfile(path):
        pytest.skip("hunt #120 results not present")
    with open(path) as fh:
        data = json.load(fh)
    pins = data["pins"]
    assert pins["d15_count_beyond_7_8_below_300"] == 12
    assert abs(pins["d15_max_re_below_300"] - 1.0267748672) < 1e-9
    assert data["parts"]["census_d15"]["t_range"] == [0.5, 300.5]


# ---------------------------------------------------------------------------
# planted faults
# ---------------------------------------------------------------------------

def test_every_planted_fault_goes_red():
    """Sixteen faults in es.planted_faults(), each of which must turn its check
    red: the twelve of the first round and four added with the round-1 checks.
    The other three planted faults are test_citation_checker_is_line_specific,
    test_line_number_scanner_catches_planted_numbers and
    test_doc_sync_catches_planted_changes."""
    r = es.planted_faults()
    assert sorted(r) == sorted([
        "closed_form_J3_sign", "series_omega_exponent", "cp_G1_to_G5", "relation_sign_gamma1gamma2",
        "swap_character_conjugate", "perturb_one_gauss_coefficient", "swap_prime_in_L42a",
        "prime_route_omega_exponent", "prime_route_cp_G1_to_G5", "cp_drop_congruence",
        "mobius_sign_composite", "near_miss_fails_at_t6",
        "table_row6_condition", "p3_drop_Q", "principal_multiplier_sign", "prime_route_multiplier_G5",
    ])
    assert len(r) == 16 == HEADLINE["faults"] - 3
    assert [k for k, v in r.items() if not v] == []


def test_the_control_beside_the_near_miss_stays_green():
    """Not a fault: the unmodified character passes the test the near miss fails."""
    assert es.fault_controls() == {"near_miss_control_passes": True}


def test_omega_fault_is_visible_only_where_omega_p_is_minus_one():
    """Stated sensitivity limit: the generic route catches this fault at every
    j; the prime route can only catch it at a norm Q = 7 mod 12."""
    r = es.omega_fault_visibility()
    assert r == {"omega_13": 1, "omega_19": -1, "fault_visible_at_13": False, "fault_visible_at_19": True}


def test_lexical_rules_of_this_lane():
    """The reserved stem, in any form, and the em dash: neither in this lane's bytes."""
    stem = "cert" + "if"  # assembled so this file does not contain it
    dash = chr(0x2014)
    for name in ("euler_step.py", "test_euler_step.py", "EULER_STEP.md"):
        path = os.path.join(HERE, name)
        if not os.path.isfile(path):
            continue
        with open(path, encoding="utf-8") as fh:
            text = fh.read()
        assert stem not in text.lower(), name
        assert dash not in text, name


# ---------------------------------------------------------------------------
# doc-sync: the numbers of EULER_STEP.md against the computations
# ---------------------------------------------------------------------------

#: fractions the document takes from paper.tex (line in the comment) rather
#: than from a computation of this lane
CITED_FRACTIONS = {
    Fr(7, 8),       # the target and region-two x-floor (4056, 5574, 15532)
    Fr(-7, 8),      # "Each is at most -7/8" (9071), Q^(-7/8) (9074)
    Fr(19, 20),     # region-two w-floor (4056)
    Fr(33, 200),    # region-two z-floor (4056)
    Fr(51, 100),    # region-one x-floor (4054)
    Fr(17, 50),     # region-one z-floor (4054)
    Fr(-1, 100),    # region-one w-floor (4054)
    Fr(4, 5),       # c_H (4064)
    Fr(163, 200),   # the tail exponent (4184)
    Fr(1, 50),      # eps_H = min(eps_0, 1/50) (4166)
    Fr(1, 6),       # the residue point z = 1/6 (15599) and l = 1/6 (16304)
    Fr(11, 12),     # the 11/12 theorem (6784)
    Fr(3, 8),       # eps_0 = 3/8 (9134, 6418)
    Fr(1, 4),       # m = (1/4) min{...} (16366)
    Fr(-1, 2),      # gamma_r = Q^(-1/2) G_r (3875)
    Fr(1, 2),       # Re s = 1/2 (MISSION.md) and Q^(1/2)
    Fr(-363, 200),  # region-two good exponent (4173)
    Fr(-33, 40),    # region-two exponent at p | u (4174)
}


def computed_fractions() -> set:
    """Every fraction the document takes from a computation of this lane."""
    out = set()
    rr = es.row_requirements()
    for pt in rr.values():
        out |= {pt[k] for k in ("R1", "R2", "R3", "R4", "R5")}
    out |= {Fr(7, 8) - rr["residue_point"]["R1"], Fr(7, 8) - rr["corner"]["R1"]}  # the slacks
    rb = es.region_bookkeeping()
    out |= {rb["region2_good_max"], rb["region2_ramified_max"]}
    for eps0 in (Fr(1, 100), Fr(1, 1000), Fr(1, 20)):  # eps_0, inputs of the region-one check
        d = es.region_one_bookkeeping(eps0)
        out |= {eps0, d["good_max"], d["ramified_max"]}
    out.add(es.defect_exponents(0, (Fr(7, 8), Fr(1), Fr(1, 6)))[0])   # -15/8
    out.add(es.defect_exponents(0, (Fr(4, 5), Fr(1), Fr(1, 6)))[0])   # -9/5
    out |= set(es.cited_principal_exponents((Fr(7, 8), Fr(19, 20), Fr(33, 200))))
    xs = sorted({p[0] for p in es.PRINCIPAL_GRID})
    out |= {xs[0], xs[-1]}  # the grid's x_r range
    return out


def doc_fractions(text: str) -> set:
    return {Fr(f) for f in re.findall(r"(?<![\w./^])(-?\d+/\d+)(?![\d/])", _strip_code_and_dates(text))}


def doc_sync_problems(text: str, report: dict) -> list:
    """Everything in the document that disagrees with the computations."""
    problems = []
    # 1. every fraction is computed or cited, and every computed one appears
    comp = computed_fractions()
    found = doc_fractions(text)
    extra = found - comp - CITED_FRACTIONS
    if extra:
        problems.append(("fractions neither computed nor cited", sorted(extra)))
    if comp - found:
        problems.append(("computed fractions missing", sorted(comp - found)))
    # 2. the rival table, exactly as rival_table_rows generates it
    lines = text.split("\n")
    for row in es.rival_table_rows(report):
        if row not in lines:
            problems.append(("rival table row", row[:60]))
    # 3. Section 6's requirement table, value by value
    rr = es.row_requirements()
    for key in ("R1", "R2", "R3", "R4", "R5"):
        tail = f"| x_r > {rr['residue_point'][key]} | x_r > {rr['corner'][key]} |"
        hits = [ln for ln in lines if ln.startswith(f"| {key}: ")]
        if len(hits) != 1 or not hits[0].endswith(tail):
            problems.append(("requirement row", key))
    flat = " ".join(text.split())  # phrases may break across lines
    pairs = {(str(rr["residue_point"][k]), str(rr["corner"][k])) for k in ("R1", "R2", "R3", "R4", "R5")}
    found_pairs = re.findall(r"x_r > (\S+) at the residue point and x_r > (\S+) at", flat)
    if not found_pairs or any(m not in pairs for m in found_pairs):
        problems.append(("floor pair", found_pairs))
    slack = (str(Fr(7, 8) - rr["residue_point"]["R1"]), str(Fr(7, 8) - rr["corner"]["R1"]))
    if re.findall(r"slack against 7/8 is (\S+) at the residue point and (\S+) at", flat) != [slack]:
        problems.append(("slack", slack))
    # 4. headline counts: every match of each pattern carries the pinned value
    groups = Counter(es.CONSUMER_SCAN_LINES.values())
    patterns = [
        (r"(\d+) (?:line )?citations", HEADLINE["citations"]),
        (r"all (\d+), each on its stated line", HEADLINE["citations"]),
        (r"finds (\d+) lines outside Section 7\.2", len(es.CONSUMER_SCAN_LINES)),
        (r"(\d+) lines found", len(es.CONSUMER_SCAN_LINES)),
        (r"D_1 or D_2, (\d+) lines", len(es.CONSUMER_SCAN_LINES)),
        (r"The (\d+) of them that use the second region", groups["principal"] + groups["every_row"]),
        (r"with no requirement \((\d+) lines\)", groups["pointer"]),
        (r"Region one only \((\d+) lines\)", groups["region_one"]),
        (r"principal row u = 1 \((\d+) lines\)", groups["principal"]),
        (r"at every row u \((\d+) lines\)", groups["every_row"]),
        (r"with no bound \((\d+) lines\)", groups["identity"]),
        (r"(\d+) prime\s+ideals of norm at most 10\^4", HEADLINE["ideals_1e4"]),
        (r"(\d+) split and 12 inert", HEADLINE["split_1e4"]),
        (r"all (\d+) prime ideals of norm at\s+most 1000", HEADLINE["ideals_1000"]),
        (r"window of (\d+) cases", HEADLINE["table_cases"]),
        (r"m up to r \+ 3: (\d+) cases", HEADLINE["table_cases"]),
        (r"(\d+) under a row", HEADLINE["table_row_cases"]),
        (r"(\d+) under none", HEADLINE["table_omitted"]),
        (r"(\d+) primes of norm at most 500", HEADLINE["reciprocity_primes"]),
        (r"(\d+) ordered pairs", HEADLINE["reciprocity_pairs"]),
        (r"(\d+) of them with R = -1", HEADLINE["reciprocity_minus"]),
        (r"all (\d+) inert ell", HEADLINE["inert_ells"]),
        (r"(\d+) rational primes up to 10\^4", HEADLINE["rational_primes_1e4"]),
        (r"(\d+) norms up to 2000", HEADLINE["epstein_norms"]),
        (r"(\d+) good norms up to 200", HEADLINE["limit_control_differences"]),
        (r"(\d+) rational points", HEADLINE["grid_points"]),
        (r"all (\d+) points of a grid", HEADLINE["grid_points"]),
        (r"(\d+) pairs of distinct norms", report["DH"]["n_pairs"]),
    ]
    for pat, want in patterns:
        got = re.findall(pat, flat)
        if not got or any(int(g) != want for g in got):
            problems.append(("count", pat, got, want))
    words = {19: "nineteen"}
    if f"Planted faults: {words[HEADLINE['faults']]}," not in flat:
        problems.append(("fault count", HEADLINE["faults"]))
    return problems


def test_doc_sync(rivals):
    """The fractions, the rival table, the requirement table and the headline
    counts of EULER_STEP.md agree with the computations."""
    assert doc_sync_problems(_doc_text(), rivals) == []


def test_doc_sync_catches_planted_changes(rivals):
    """Planted faults: a Section 6 floor changed to a nearby fraction, one count
    of the rival table changed by one, a requirement swapped for another
    computed value, and a headline count changed by one each turn the
    doc-sync red."""
    text = _doc_text()
    near = f"{Fr(401, 600).numerator}/{Fr(401, 600).denominator + 1}"
    assert "x_r > 401/600" in text and "66 of 231" in text and "| x_r > 3/5 | x_r > 301/500 |" in text
    for mutated in (text.replace("x_r > 401/600", "x_r > " + near, 1),
                    text.replace("66 of 231", "67 of 231", 1),
                    text.replace("| x_r > 3/5 | x_r > 301/500 |", "| x_r > 2/3 | x_r > 301/500 |", 1),
                    text.replace("1234 prime", "1235 prime", 1)):
        assert mutated != text
        assert doc_sync_problems(mutated, rivals) != []


# ---------------------------------------------------------------------------
# the full ranges (slow)
# ---------------------------------------------------------------------------

@pytest.mark.slow
@needs_flint
def test_prime_gauss_identities_every_prime_ideal_to_norm_10000():
    r = es.run_prime_gauss(10 ** 4, balls=True, jacobi=True)
    assert r["counts"] == {"split": HEADLINE["split_1e4"], "inert": HEADLINE["inert_1e4"]}
    assert r["fails"] == []


@pytest.mark.slow
@needs_flint
def test_appendix_a1_form_at_every_prime_to_norm_10000():
    primes = es.primes_of_norm_upto(10 ** 4)
    assert len(primes) == HEADLINE["ideals_1e4"]
    assert [P.pi for P in primes if not es.a1_form_at_prime(P)] == []


@pytest.mark.slow
@needs_flint
def test_gamma_of_p_powers_by_direct_summation_to_norm_100():
    """The same at both primes over every split ell <= 100 (t <= 3), at the inert
    5 and 11 (t <= 3) and at the inert 17 (t <= 2): 25 prime ideals."""
    r = es.p_power_quadratic_run(100, tmax=3, inert=((5, 3), (11, 3), (17, 2)))
    assert r == {"n": 25, "bad": []}


@pytest.mark.slow
def test_inert_direct_sums_to_ell_300():
    r = es.inert_bruteforce(300, balls=False)
    assert r["n"] == 32 and r["bad"] == []


@pytest.mark.slow
@needs_flint
def test_lemma71_with_true_gauss_sums_to_norm_1000():
    primes = es.primes_of_norm_upto(1000)
    assert len(primes) == HEADLINE["ideals_1000"]
    bad = [P.pi for P in primes if not all(es.lemma71_at_prime(P).values())]
    assert bad == []


@pytest.mark.slow
def test_cp_bruteforce_full_ranges():
    P7, P7b = es.split_primes(7)
    assert es.cp_bruteforce(P7, 7, 1) == {"checked": 104, "bad": []}
    assert es.cp_bruteforce(P7b, 7, 1) == {"checked": 104, "bad": []}
    assert es.cp_bruteforce(P7, 4, 3) == {"checked": 100, "bad": []}
    assert es.gauss_lift_bruteforce(P7, 7) == []
    P13 = es.split_primes(13)[0]
    assert es.cp_bruteforce(P13, 4, 2) == {"checked": 75, "bad": []}
    assert es.gauss_lift_bruteforce(P13, 4) == []
    P5 = es.inert_prime(5)
    assert es.cp_bruteforce(P5, 3, 2) == {"checked": 54, "bad": []}
    assert es.gauss_lift_bruteforce(P5, 3) == []
    P11 = es.inert_prime(11)
    assert es.cp_bruteforce(P11, 2, 2) == {"checked": 36, "bad": []}
