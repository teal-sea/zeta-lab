"""Fast checks for hunts/rh_claim_statements (about a minute on one core).

Every claim of the fast tier is rerun from claims.json on a reduced range,
and EVERY mutant is rerun and must be rejected with a witness: a test that
passes its own mutant is not a test. The recorded run (results.json) is
checked against the ledger, and the instruments are checked against planted
faults. Nothing here reads the archive unless RH_CLAIM_ARCHIVE names it, and
nothing writes into the tree.
"""
from __future__ import annotations

import hashlib
import json
import math
import os
import random
from fractions import Fraction
from pathlib import Path

import pytest
from flint import acb, acb_series, arb, ctx

from hunts.rh_claim_statements import checks_analytic as ca
from hunts.rh_claim_statements import checks_exact as ce
from hunts.rh_claim_statements import common as C
from hunts.rh_claim_statements import runner

HERE = Path(__file__).resolve().parent
LEDGER = json.loads((HERE / "claims.json").read_text(encoding="utf-8"))
CLAIMS = LEDGER["claims"]
RESULTS = json.loads((HERE / "results.json").read_text(encoding="utf-8"))
BY_ID = {c["id"]: c for c in CLAIMS}
FAST = [c for c in CLAIMS if c["test"]["fast"] is not None]
MUTANTS = [(c["id"], m["id"]) for c in CLAIMS for m in c["mutants"]]


# ------------------------------------------------------------------ the ledger

def test_ledger_shape():
    assert len(CLAIMS) >= 40
    assert len({c["id"] for c in CLAIMS}) == len(CLAIMS)
    for c in CLAIMS:
        assert hashlib.sha256(c["verbatim"].encode("utf-8")).hexdigest() == c["sha256"], c["id"]
        assert c["verbatim"].lstrip().startswith(("theorem", "lemma", "private")), c["id"]
        assert c["math"] and c["quantifiers"] and c["conventions"], c["id"]
        assert c["grade_if_it_holds"] in runner.GRADES
        # every identifier is resolved: Mathlib with a definition site, core, or a quoted local definition
        for i in c["identifiers"]:
            assert i["origin"] in ("Mathlib", "core", "archive"), (c["id"], i)
            if i["origin"] == "Mathlib":
                assert i["defined_at"].startswith("Mathlib/") and i["definition_line"]
        local = {n.strip().split(".")[-1] for d in c["local_definitions"] for n in d["name"].split(",")}
        for i in c["identifiers"]:
            if i["origin"] == "archive":
                assert i["written"].split(".")[-1] in local, (c["id"], i["written"])
        # no archive declaration can capture a Mathlib identifier of the statement
        cap = c["capture_check"]["archive_declarations_that_could_capture"]
        assert all(h["written"].split(".")[-1] in local for h in cap), (c["id"], cap)
        assert not c["context"]["notations"] and not c["context"]["local_overrides"], c["id"]


def test_every_mutant_is_one_change_of_the_statement():
    n = 0
    for c in CLAIMS:
        assert c["mutants"], f"{c['id']} has no mutant"
        for m in c["mutants"]:
            n += 1
            if m["change"] is None:                       # an explicit prime: n is replaced by n + k
                assert "offset" in m["params"]
                continue
            old, new = m["change"]
            assert c["verbatim"].count(old) == 1
            assert m["statement"] == c["verbatim"].replace(old, new) != c["verbatim"]
    assert n == LEDGER["meta"]["mutants"] == len(MUTANTS)


def test_the_ledger_prefers_number_theory():
    topics = [c["topic"] for c in CLAIMS]
    assert sum(t in ("zeta", "L", "primes", "finite_field") for t in topics) >= 40


# ------------------------------------------------------------------ the claims, fast tier

@pytest.mark.parametrize("cid", [c["id"] for c in FAST])
def test_claim_survives_on_the_fast_range(cid):
    c = BY_ID[cid]
    r = runner.run_claim(c, level="fast", with_mutants=False)
    assert r["holds"] is True, (cid, c["name"], r.get("witness"), r.get("notes"))
    assert r["grade"] == c["grade_if_it_holds"]


@pytest.mark.parametrize("cid,mid", MUTANTS)
def test_mutant_is_rejected_with_a_witness(cid, mid):
    c = BY_ID[cid]
    m = next(x for x in c["mutants"] if x["id"] == mid)
    r = runner.run_mutant(c, m, level="fast")
    assert r["rejected"] is True, (mid, m["change"], r)
    assert r["witness"], mid


# ------------------------------------------------------------------ the recorded run

def test_recorded_run_covers_the_ledger_and_nothing_fails():
    recs = {r["id"]: r for r in RESULTS["claims"]}
    assert set(recs) == set(BY_ID)
    assert RESULTS["meta"]["level"] == "full" and RESULTS["meta"]["prec_scale"] == 1
    assert RESULTS["meta"]["archive_tarball_sha256"] == LEDGER["meta"]["tarball_sha256"]
    s = RESULTS["summary"]
    assert s["fail"] == [] and s["undecided"] == []
    assert s["hold"] == len(CLAIMS)
    assert s["mutants_rejected"] == s["mutants"] == len(MUTANTS)
    by_grade = {g: sum(1 for r in recs.values() if r["grade"] == g) for g in runner.GRADES}
    assert by_grade == s["by_grade"] and sum(by_grade.values()) == len(CLAIMS)
    for cid, r in recs.items():
        assert r["grade"] == BY_ID[cid]["grade_if_it_holds"], cid
        assert all(m["rejected"] and m["witness"] for m in r["mutants"]), cid


@pytest.mark.parametrize("cid", ["C01", "C11", "C21", "C29", "C61", "C62", "C65", "C72"])
def test_recorded_numbers_recompute(cid):
    """Claims whose fast and full parameters coincide must reproduce the recorded record."""
    c = BY_ID[cid]
    assert c["test"]["fast"] == c["test"]["params"]
    old = next(r for r in RESULTS["claims"] if r["id"] == cid)
    new = runner.run_claim(c, level="fast", with_mutants=False)
    assert new["holds"] is old["holds"] is True
    assert new["cases"] == old["cases"]
    if isinstance(old["margin"], (int, float)):
        assert new["margin"] == pytest.approx(old["margin"], rel=1e-9, abs=1e-12)


def test_the_tightest_claims_are_tight():
    recs = {r["id"]: r for r in RESULTS["claims"]}
    assert recs["C21"]["tightest"]["m"] == 113                      # pi(m) log m / m peaks at 113
    assert 1.2550 < recs["C21"]["sharp_constant"] < 1.2551
    assert 0.49309 < recs["C28"]["sharp_constant"][0] <= recs["C28"]["sharp_constant"][1] < 0.49310
    assert recs["C53"]["margin"] == 0 and recs["C74"]["margin"] == 0
    lo_, hi_ = recs["C01"]["sharp_constant"]
    assert lo_ <= 1.4603545088 <= hi_                               # |zeta(1/2)|


def test_precision_response():
    """Doubling every working precision moves no verdict and no reported margin beyond its enclosure."""
    p2 = json.loads((HERE / "results_prec2.json").read_text(encoding="utf-8"))
    assert p2["meta"]["prec_scale"] == 2
    one = {r["id"]: r for r in RESULTS["claims"]}
    for r in p2["claims"]:
        a = one[r["id"]]
        assert r["holds"] is a["holds"] is True, r["id"]
        if isinstance(a.get("sup_ratio"), list):
            assert max(a["sup_ratio"][0], r["sup_ratio"][0]) <= min(a["sup_ratio"][1], r["sup_ratio"][1]) + 1e-9, r["id"]
        elif isinstance(a.get("margin"), (int, float)) and isinstance(r.get("margin"), (int, float)):
            # C17 reports the largest branch-and-bound upper bound over 80 characters, each found to
            # tolerance 5e-3; every other margin here is an enclosure endpoint or an exact number
            # (C08's margin is an adaptive lower bound, which moves with the subdivision: 2e-7 here)
            tol = 1.1e-2 if r["id"] == "C17" else 1e-5
            assert r["margin"] == pytest.approx(a["margin"], rel=1e-6, abs=tol), r["id"]


# ------------------------------------------------------------------ the instruments see red

def test_taylor_model_encloses_zeta_and_its_derivative():
    rng = random.Random(7)
    with ctx.workprec(64):
        for (x, y, r) in [(0.5, 3.0, 0.04), (0.2, 0.1, 0.04), (1.1, 50.0, 0.05), (1.05, 0.35, 0.02), (0.6, 14.1, 0.1)]:
            S = acb(arb(x, r), arb(y, r))
            val, der = ca._zeta_tb(S)
            for _ in range(40):
                pt = acb(x + r * rng.uniform(-1, 1), y + r * rng.uniform(-1, 1))
                z = acb_series([pt, 1], prec=2).zeta()
                assert val.contains(acb(z[0].real.mid(), z[0].imag.mid()))
                assert der.contains(acb(z[1].real.mid(), z[1].imag.mid()))
            # and it is tight to first order: the radius is about |zeta'(c)| (rx + ry), where plain
            # ball evaluation is 3 to 50 times wider
            d1 = acb_series([acb(x, y), 1], prec=2).zeta()[1]
            assert C.up(val.real.rad()) <= 1.25 * C.up(d1.abs_upper()) * 2 * r, (x, y, r)
            assert C.up(val.real.rad()) < 0.4 * C.lo(S.zeta().real.rad()), (x, y, r)
        assert ca._zeta_tb(acb(arb(1.0, 0.05), arb(0.1, 0.05))) is None       # a disc reaching the pole is refused


def test_branch_and_bound_finds_a_known_supremum_and_a_planted_violation():
    f = lambda box: (C.ball(*box[0]) * (1 - C.ball(*box[0])))            # sup 1/4 at 1/2
    res = C.sup_bnb(f, [(b,) for b in C.grid(0.0, 1.0, 4)], tol=1e-6)
    assert res["lo"] <= 0.25 <= res["hi"] and res["hi"] - res["lo"] <= 1e-6
    res = C.sup_bnb(lambda box: f(box) * 5, [(b,) for b in C.grid(0.0, 1.0, 4)], tol=1e-6, stop_above=1.0)
    assert C.verdict_from_sup(res) is False


def test_lean_conventions_are_the_ones_implemented():
    assert C.monus(3, 5) == 0 and C.nat_log(1, 10) == 0 and C.nat_log(2, 0) == 0 and C.nat_log(2, 8) == 3
    assert C.padic_val(2, 0) == 0 and C.padic_val(1, 8) == 0 and C.padic_val(2, 40) == 3
    assert C.totient(0) == 0 and C.totient(1) == 1
    assert C.prime_power_base(1) is None and C.prime_power_base(8) == 2 and C.prime_power_base(12) is None
    assert float(ce._lean_log(0)) == 0.0
    # the statement of C25 as Lean reads it holds at N = 0 and 1 (1/(5 * 0) = 0) and fails at N = 2..7
    r = ce.inv_log_prime_sum(dict(K="5", N0=0, N1=1))
    assert r["holds"] is True
    assert ce.inv_log_prime_sum(dict(K="5", N0=2, N1=7))["holds"] is False
    assert ce.inv_log_prime_sum(dict(K="5", N0=8, N1=99))["holds"] is True


def test_own_number_theory_against_pari():
    import cypari2
    pari = cypari2.Pari()
    assert all(C.kronecker(a, n) == int(pari.kronecker(a, n)) for a in range(-30, 31) for n in range(1, 40))
    assert all(C.totient(n) == int(pari.eulerphi(n)) for n in range(1, 400))
    assert [n for n in range(2, 200) if ce._miller_rabin(n, ce._MR_BASES) is None] == [int(p) for p in C.primes_upto(199)]
    assert ce._lucas_proof(10 ** 9 + 7, [2, 500000003]) is not None
    assert ce._lucas_proof(10 ** 9 + 9, [2, 3, 5, 7]) is None            # an incomplete factor list proves nothing
    assert ce._miller_rabin(3215031751, (2, 3, 5, 7)) is None            # a strong pseudoprime to four bases...
    assert ce._miller_rabin(3215031751, ce._MR_BASES) is not None        # ...is caught by twelve


def test_finite_field_tables_are_fields():
    for p, e in ((2, 2), (2, 3), (3, 2), (5, 2), (3, 3)):
        F = C.GF(p, e)
        q = F.q
        assert all(F.power(a, q) == a for a in range(q))                 # Fermat
        assert sorted(F.power(a, q - 2) and int(F.mul[a][F.power(a, q - 2)]) for a in range(1, q)) == [1] * (q - 1)
        a, b, c = 2 % q, q - 1, q // 2
        assert int(F.mul[a][F.add[b][c]]) == int(F.add[F.mul[a][b]][F.mul[a][c]])


def test_decoy_hurwitz_zeta_fails_the_real_zero_statement():
    assert ca.real_nonvanishing(dict(a="0", b="1", hurwitz="1/4"))["holds"] is False
    assert ca.real_nonvanishing(dict(a="0", b="1", hurwitz="3/4"))["holds"] is True
    d = RESULTS["decoys"]
    assert d["hurwitz_real_zeros"]["by_parameter"]["1/4"]["holds"] is False
    assert d["cramer_prime_count"]["fraction_violating"] > 0.5
    assert all(v["fraction_negative"] > 0.2 for v in d["random_sequences_l1"]["by_period"].values())


# ------------------------------------------------------------------ optional: against the archive itself

@pytest.mark.skipif(not os.environ.get("RH_CLAIM_ARCHIVE"), reason="set RH_CLAIM_ARCHIVE to the archive's lean/src to re-read the statements")
def test_statements_still_match_the_archive():
    import runpy
    b = runpy.run_path(str(HERE / "build_ledger.py"), run_name="ledger")
    arch = Path(os.environ["RH_CLAIM_ARCHIVE"])
    for c in CLAIMS:
        raw = (arch / c["path"]).read_text(encoding="utf-8")
        assert hashlib.sha256(raw.encode("utf-8")).hexdigest() == c["file_sha256"], c["id"]
        st = b["statement"](b["strip_comments"](raw).split("\n"), c["line"])
        assert st == c["verbatim"], c["id"]
