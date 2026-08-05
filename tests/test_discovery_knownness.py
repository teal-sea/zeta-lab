"""Tests for ``ontology.knownness`` — the already-known gate.

The gate is only worth having if it is hard to fool in the flattering
direction, so most of what is pinned here is a *refusal*: a spurious relation
that dissolves at higher precision, a value matched outside its own error bar, a
catalogue entry with no source, and above all any attempt to render "the
literature was not consulted" as "this is new".

Numeric entries in the catalogues are re-derived here from mpmath rather than
copied, per the house rule that a number in the source is a claim.
"""

from __future__ import annotations

import ast
import json
import math
import re
import subprocess
import sys
from pathlib import Path

import pytest
from mpmath import mp, mpf

from ontology import knownness as K
from ontology.schema import (
    Candidate,
    CandidateKind,
    Precision,
    Verdict,
    VerdictStatus,
    capture_provenance,
    validate_candidate,
    verdict_reasons,
)

REPO_ROOT = Path(__file__).resolve().parent.parent
MODULE_PATH = REPO_ROOT / "ontology" / "knownness.py"


# ---------------------------------------------------------------------------
# fixtures / builders
# ---------------------------------------------------------------------------


def _provenance(**overrides):
    kwargs = dict(
        generator="test.generator",
        generator_version="1.0",
        lab_object="test.object",
        parameters={"n": 1},
        precision=Precision("dps", 40),
    )
    kwargs.update(overrides)
    return capture_provenance(**kwargs)


def constant_candidate(subject: str, value, uncertainty, **kwargs) -> Candidate:
    return Candidate(
        kind=CandidateKind.CONSTANT,
        claim={"subject": subject, "value": value},
        evidence={"uncertainty": uncertainty},
        provenance=_provenance(),
        **kwargs,
    )


def structural_candidate(family: str) -> Candidate:
    return Candidate(
        kind=CandidateKind.STRUCTURAL,
        claim={"family": family, "predicate": "P holds", "scope": "n <= 10"},
        evidence={
            "witnesses": ["a", "b", "c"],
            "n_checked": 3,
            "n_satisfied": 3,
            "controls": [{"id": "control-1", "satisfied": False}],
        },
        provenance=_provenance(),
    )


def lambda1_provider(dps: int):
    """lambda_1 computed by the laboratory's Cauchy-integral route.

    Deliberately *not* the closed form: identifying a closed form from a value
    produced by that same closed form would be circular.
    """
    from zeta.li import li_coefficient

    return li_coefficient(1, method="cauchy", dps=dps)


LAMBDA1_TEXT = "0.0230957089661210338143102479064952916219"


def exact_provider(expression: str):
    """A provider that honours the precision it is asked for."""

    def provider(dps: int):
        return K.safe_eval_expression(expression, dps + 5)

    return provider



# ---------------------------------------------------------------------------
# A domain-populated catalogue, as a *fixture*.
#
# The operative zeta catalogue lives in ``discovery/domains/zeta_domain.py`` and
# is keyed on laboratory symbol paths. This one is keyed on literature names and
# exists here to exercise the registry mechanism end to end without coupling
# these tests to a domain module. Its ids carry a ``lit-`` prefix so the two can
# be registered into the same registry without colliding.
#
# Every quoted number below is re-derived in TestDomainFacts.
# ---------------------------------------------------------------------------

ZETA_LITERATURE_FACTS: tuple[K.KnownFact, ...] = (
    K.KnownFact(
        id="lit-li-lambda-1-closed-form",
        statement=(
            "The first Li coefficient has a closed form: "
            "lambda_1 = 1 + gamma/2 - log(4 pi)/2."
        ),
        canonical_form="lambda_1 = 1 + gamma/2 - log(4 pi)/2 = 0.02309570896612103381...",
        source=(
            "Li (1997), J. Number Theory 65, 325-333; "
            "Bombieri-Lagarias (1999), J. Number Theory 77, 274-287; "
            "zeta.li.li_closed_form_lambda1"
        ),
        domain="zeta",
        aliases=("lambda_1", "lambda_1 by contour integral", "first li coefficient"),
        value="0.0230957089661210338143102479064952916219",
        tolerance="1e-38",
        tags=("li-criterion", "closed-form"),
    ),
    K.KnownFact(
        id="lit-li-criterion",
        statement=(
            "Li's criterion: RH holds if and only if lambda_n >= 0 for every "
            "n >= 1. An equivalence, not a step towards a proof."
        ),
        canonical_form="RH  <=>  lambda_n >= 0 for all n >= 1",
        source="Li (1997), J. Number Theory 65, 325-333",
        domain="zeta",
        aliases=("li's criterion", "li criterion"),
        tags=("equivalence",),
    ),
    K.KnownFact(
        id="lit-li-asymptotic-growth",
        statement=(
            "Under RH the Li coefficients grow like "
            "lambda_n ~ (n/2)(log n - log(2 pi) + gamma - 1), with an "
            "oscillating remainder of size O(sqrt(n) log n)."
        ),
        canonical_form="lambda_n = (n/2)(log n - log(2 pi) + gamma - 1) + O(sqrt(n) log n)",
        source=(
            "Bombieri-Lagarias (1999), J. Number Theory 77, 274-287; "
            "Voros (2006), Ann. Inst. Fourier 56, 1-27"
        ),
        domain="zeta",
        keys=("lambda_n", "n*log(n)/2"),
        tags=("asymptotic", "conditional-on-rh"),
    ),
    K.KnownFact(
        id="lit-riemann-von-mangoldt",
        statement=(
            "The Riemann-von Mangoldt formula for the number of zeros with "
            "0 < Im(rho) <= T."
        ),
        canonical_form=(
            "N(T) = (T/2pi) log(T/2pi) - T/2pi + 7/8 + S(T) + O(1/T)"
        ),
        source=(
            "von Mangoldt (1905); Titchmarsh, The Theory of the Riemann "
            "Zeta-Function, 2nd ed., section 9.3"
        ),
        domain="zeta",
        aliases=("n(t)", "riemann-von mangoldt formula", "zero counting function"),
        tags=("counting", "theorem"),
    ),
    K.KnownFact(
        id="lit-hardy-zeros-on-critical-line",
        statement="Infinitely many zeros of zeta lie on the critical line.",
        canonical_form="#{rho : Re(rho) = 1/2, 0 < Im(rho) <= T} -> infinity",
        source="Hardy (1914), C. R. Acad. Sci. Paris 158, 1012-1014",
        domain="zeta",
        aliases=("hardy's theorem", "hardy 1914"),
        tags=("theorem",),
    ),
    K.KnownFact(
        id="lit-montgomery-pair-correlation",
        statement=(
            "Montgomery's pair-correlation conjecture: the normalised pair "
            "correlation of the zeros is the GUE form."
        ),
        canonical_form="R_2(u) = 1 - (sin(pi u)/(pi u))^2",
        source=(
            "Montgomery (1973), Proc. Sympos. Pure Math. 24, 181-193; "
            "Odlyzko (1987), Math. Comp. 48, 273-308"
        ),
        domain="zeta",
        aliases=("pair correlation of zeta zeros", "montgomery pair correlation"),
        tags=("random-matrix", "conjecture"),
    ),
    K.KnownFact(
        id="lit-robin-criterion",
        statement=(
            "Robin's criterion: RH holds if and only if "
            "sigma(n) < e^gamma n log log n for every n > 5040."
        ),
        canonical_form="RH  <=>  sigma(n) < e^gamma n log log n for all n > 5040",
        source=(
            "Robin (1984), J. Math. Pures Appl. 63, 187-213; "
            "Lagarias (2002), Amer. Math. Monthly 109, 534-543"
        ),
        domain="zeta",
        aliases=("robin's criterion", "robin criterion"),
        tags=("equivalence",),
    ),
    K.KnownFact(
        id="lit-robin-constant",
        statement="The constant in Robin's criterion and Mertens' third theorem.",
        canonical_form="e^gamma = 1.78107241799019798523650410310717954917...",
        source="Robin (1984), J. Math. Pures Appl. 63, 187-213; DLMF 5.2.3",
        domain="zeta",
        aliases=("e^gamma", "robin's constant", "exp(euler gamma)"),
        value="1.7810724179901979852365041031071795491696",
        tolerance="1e-38",
        tags=("constant",),
    ),
    K.KnownFact(
        id="lit-mertens-conjecture-disproved",
        statement=(
            "Mertens' conjecture |M(x)| < sqrt(x) is false: Odlyzko and te Riele "
            "showed limsup M(x)/sqrt(x) > 1.06 and liminf M(x)/sqrt(x) < -1.009, "
            "without exhibiting a counterexample."
        ),
        canonical_form="limsup M(x)/sqrt(x) > 1.06,  liminf M(x)/sqrt(x) < -1.009",
        source=(
            "Odlyzko and te Riele (1985), J. reine angew. Math. 357, 138-160"
        ),
        domain="zeta",
        aliases=("mertens' conjecture", "m(x)/sqrt(x)"),
        tags=("disproof",),
    ),
    K.KnownFact(
        id="lit-de-bruijn-newman-nonnegative",
        statement=(
            "The de Bruijn-Newman constant satisfies Lambda >= 0, so RH is "
            "equivalent to Lambda = 0: 'the Riemann hypothesis, if true, is only "
            "barely so'."
        ),
        canonical_form="0 <= Lambda <= 0.2",
        source=(
            "Rodgers and Tao (2020), Duke Math. J. 169, 3517-3556; "
            "Platt and Trudgian (2021), Bull. LMS 53, 792-797; "
            "Newman (1976), Proc. Amer. Math. Soc. 61, 245-251"
        ),
        domain="zeta",
        aliases=("de bruijn-newman constant", "lambda"),
        tags=("theorem", "heat-flow"),
    ),
    K.KnownFact(
        id="lit-littlewood-sign-changes",
        statement=(
            "pi(x) - li(x) changes sign infinitely often, so any finite "
            "computation showing pi(x) < li(x) is not evidence for a general "
            "inequality."
        ),
        canonical_form="pi(x) - li(x) changes sign infinitely often",
        source="Littlewood (1914), C. R. Acad. Sci. Paris 158, 1869-1872",
        domain="zeta",
        aliases=("pi(x) - li(x)", "littlewood's theorem"),
        tags=("theorem", "anti-extrapolation"),
    ),
    K.KnownFact(
        id="lit-davenport-heilbronn-counterexample",
        statement=(
            "The Davenport-Heilbronn function satisfies a Riemann-type functional "
            "equation, has real coefficients and a real Hardy-style Z, and has "
            "zeros off the critical line. Any structural property it also "
            "satisfies distinguishes nothing about RH."
        ),
        canonical_form="f(s) = f(1-s) with zeros off Re(s) = 1/2",
        source=(
            "Davenport and Heilbronn (1936), J. London Math. Soc. 11, 181-185; "
            "Titchmarsh, 2nd ed., section 10.25; zeta.epstein.battery"
        ),
        domain="zeta",
        aliases=("davenport-heilbronn function", "epstein zeta counterexample"),
        tags=("counterexample-battery",),
    ),
    K.KnownFact(
        id="lit-speiser-criterion",
        statement=(
            "Speiser's theorem: RH is equivalent to the absence of non-real "
            "zeros of zeta' in the strip 0 < Re(s) < 1/2."
        ),
        canonical_form="RH  <=>  zeta'(s) has no zeros with 0 < Re(s) < 1/2",
        source=(
            "Speiser (1934), Math. Ann. 110, 514-521; "
            "Levinson and Montgomery (1974), Acta Math. 133, 49-65"
        ),
        domain="zeta",
        aliases=("speiser's criterion", "speiser criterion"),
        tags=("equivalence",),
    ),
    K.KnownFact(
        id="lit-baez-duarte-criterion",
        statement=(
            "The Baez-Duarte reformulation of the Nyman-Beurling criterion: RH "
            "holds if and only if the distances d_N tend to zero."
        ),
        canonical_form="RH  <=>  d_N -> 0, with d_N^2 >= (conjecturally) C/log N",
        source=(
            "Baez-Duarte (2003), Rend. Mat. Acc. Lincei 14, 5-11; "
            "Nyman (1950); Beurling (1955), PNAS 41, 312-314"
        ),
        domain="zeta",
        aliases=("baez-duarte criterion",),
        tags=("equivalence",),
    ),
    K.KnownFact(
        id="lit-xi-at-zero",
        statement="The value of the Riemann Xi function at the origin.",
        canonical_form="Xi(0) = xi(1/2) = 0.49712077818831410991277373968539771981...",
        source="Titchmarsh, 2nd ed., section 2.1; zeta.core.Xi",
        domain="zeta",
        aliases=("xi(0)", "xi(1/2)"),
        value="0.4971207781883141099127737396853977198073",
        tolerance="1e-38",
        tags=("constant",),
    ),
    K.KnownFact(
        id="lit-first-zero-ordinate",
        statement="The ordinate of the first non-trivial zero of zeta.",
        canonical_form="gamma_1 = 14.13472514173469379045725198356247027078...",
        source="Sloane, OEIS A058303; Odlyzko's tables; mpmath.zetazero(1)",
        domain="zeta",
        aliases=("gamma_1", "first zeta zero ordinate", "first non-trivial zero"),
        value="14.134725141734693790457251983562470270785",
        tolerance="1e-37",
        tags=("constant",),
    ),
)


def register_zeta_facts(registry, *, replace: bool = False):
    """What a domain module does at registration time."""
    return registry.register_all(ZETA_LITERATURE_FACTS, replace=replace)


ZETA_FACTS = ZETA_LITERATURE_FACTS

# ---------------------------------------------------------------------------
# 1. the constant basis and the helpers
# ---------------------------------------------------------------------------


class TestBasis:
    def test_names_are_unique(self):
        table = K.basis_by_name()
        assert len(table) == len(K.DEFAULT_BASIS)

    def test_every_element_evaluates_at_working_precision(self):
        with mp.workdps(60):
            for element in K.DEFAULT_BASIS:
                value = element.value()
                assert mp.isfinite(value)
                assert value != 0

    def test_duplicate_names_are_refused(self):
        duplicated = K.DEFAULT_BASIS + (K.DEFAULT_BASIS[0],)
        with pytest.raises(K.KnownnessError):
            K.basis_by_name(duplicated)

    def test_identify_names_are_understood_by_mpmath(self):
        # Each identify_name must be a string mpmath.identify can consume; the
        # cross-check silently degrades to None otherwise.
        for element in K.DEFAULT_BASIS:
            got = K.safe_eval_expression(element.identify_name, 30)
            with mp.workdps(30):
                assert abs(got - element.value()) < mpf(10) ** -25

    @pytest.mark.parametrize(
        "value,expected",
        [
            (1.5, 2),
            ("0.0230957089661210338143", 21),
            ("1.500", 2),  # trailing zeros are not measured digits
            (0.1, 1),  # the *literal* is one digit; floats go via FLOAT64_DIGITS
            (LAMBDA1_TEXT, 39),  # not 28: Decimal.normalize() would have capped it
        ],
    )
    def test_significant_digits(self, value, expected):
        assert K._significant_digits(value) == expected

    def test_a_long_literal_is_not_capped_by_the_decimal_context(self):
        import decimal

        assert decimal.getcontext().prec == 28
        assert K._available_digits(LAMBDA1_TEXT, None) == 39

    def test_float_is_credited_with_fifteen_digits(self):
        assert K._available_digits(0.023095708966121034, None) == K.FLOAT64_DIGITS
        assert K.FLOAT64_DIGITS == 15


class TestSafeEval:
    def test_integer_division_is_exact(self):
        got = K.safe_eval_expression("(1/7)", 40)
        with mp.workdps(40):
            assert abs(got - mpf(1) / 7) < mpf(10) ** -38
        # a plain Python eval would have produced a double here
        assert abs(float(got) - 1 / 7) < 1e-15

    def test_mpmath_identify_output_round_trips(self):
        with mp.workdps(30):
            target = 1 + mp.euler / 2 - mp.log(4 * mp.pi) / 2
            text = mp.identify(target, ["euler", "log(2)", "log(pi)"])
        assert text is not None
        got = K.safe_eval_expression(text, 40)
        with mp.workdps(40):
            assert abs(got - (1 + mp.euler / 2 - mp.log(4 * mp.pi) / 2)) < mpf(10) ** -35

    @pytest.mark.parametrize(
        "bad",
        [
            "__import__('os').system('true')",
            "open('/etc/passwd')",
            "pi.__class__",
            "[1, 2, 3]",
            "lambda: 1",
            "pi if 1 else 2",
        ],
    )
    def test_disallowed_syntax_is_refused(self, bad):
        with pytest.raises(K.KnownnessError):
            K.safe_eval_expression(bad, 20)

    def test_syntax_error_is_a_knownness_error(self):
        with pytest.raises(K.KnownnessError):
            K.safe_eval_expression("1 +", 20)


# ---------------------------------------------------------------------------
# 2. closed-form identification — the positive case
# ---------------------------------------------------------------------------


class TestIdentifyKnownConstants:
    def test_lambda_1_is_identified_from_the_laboratory_value(self):
        """Feed it lambda_1 and it must return the closed form.

        The value comes from ``zeta.li.li_coefficient`` (a contour integral over
        xi), not from the closed form, so the identification is a real find.
        """
        report = K.identify_constant(provider=lambda1_provider)
        assert report.identified is True
        match = report.match
        assert match is not None
        # The expression is 1 + gamma/2 - log(4 pi)/2 rewritten over a common
        # denominator; compare mathematically, not lexically.
        used = {name for _, name in match.terms if name != "1"}
        assert used == {"gamma", "log(2)", "log(pi)"}
        with mp.workdps(50):
            expected = 1 + mp.euler / 2 - mp.log(4 * mp.pi) / 2
            assert abs(match.evaluate(50) - expected) < mpf(10) ** -45
        assert match.confidence is K.IdentificationConfidence.CONFIRMED
        assert match.survived_escalation is True
        assert match.escalated_digits == K.DEFAULT_ESCALATED_DIGITS
        assert match.digits_confirmed >= 35
        assert match.surplus_digits >= K.DEFAULT_MIN_SURPLUS_DIGITS

    def test_lambda_1_cross_check_agrees_with_mpmath_identify(self):
        report = K.identify_constant(provider=lambda1_provider)
        assert report.match is not None
        text = report.match.cross_check
        assert text is not None, "mpmath.identify should confirm this one"
        got = K.safe_eval_expression(text, 45)
        with mp.workdps(45):
            assert abs(got - (1 + mp.euler / 2 - mp.log(4 * mp.pi) / 2)) < mpf(10) ** -40

    def test_the_provider_route_is_not_circular(self):
        """The laboratory value and the closed form agree but are not the same code."""
        with mp.workdps(45):
            lab = mpf(str(lambda1_provider(45)))
            closed = 1 + mp.euler / 2 - mp.log(4 * mp.pi) / 2
            assert abs(lab - closed) < mpf(10) ** -38

    def test_a_simple_rational_is_identified_at_level_zero(self):
        report = K.identify_constant(provider=exact_provider("1/7"))
        assert report.identified is True
        assert report.match.expression == "1/7"
        assert report.match.n_terms == 0
        # Occam: only the rational level was searched, so the budget is small.
        assert report.search_space_log10 < 4.0

    def test_a_one_term_constant_is_identified(self):
        report = K.identify_constant(provider=exact_provider("(3*pi)/4"))
        assert report.identified is True
        assert report.match.expression == "3*pi/4"
        assert report.match.n_terms == 1

    def test_closed_form_convenience(self):
        assert K.closed_form(provider=exact_provider("1/7")) == "1/7"
        assert K.closed_form("0.4720384756019283746501928374650192837465") is None


# ---------------------------------------------------------------------------
# 3. closed-form identification — the refusals
# ---------------------------------------------------------------------------


class TestIdentifyRefuses:
    NON_SPECIAL = "0.4720384756019283746501928374650192837465"

    def test_a_random_constant_is_not_identified(self):
        report = K.identify_constant(self.NON_SPECIAL)
        assert report.identified is False
        assert report.match is None
        assert report.n_provisional == 0
        assert "no integer relation" in report.reason

    def test_a_second_structureless_constant_is_not_identified(self):
        report = K.identify_constant("0.8391027465019283746510293847561029384756")
        assert report.identified is False
        assert report.n_provisional == 0

    def test_the_search_is_live_on_the_same_settings(self):
        """The control for the two negatives above: e/10 *is* found."""
        report = K.identify_constant("2.7182818284590452353602874713526624977572e-1")
        assert report.identified is True
        assert report.match.expression == "e/10"

    def test_low_precision_false_positive_is_caught_by_the_escalation(self):
        """The escalation test: a match that dissolves is *not* a find."""

        def perturbed(dps):
            with mp.workdps(dps + 10):
                return +(mp.pi / 4 - mp.log(2) / 3 + mpf(10) ** -11)

        report = K.identify_constant(
            provider=perturbed,
            base_digits=9,
            escalated_digits=30,
            max_provisional=500,  # keep the whole list so the assertion is exact
        )
        assert report.identified is False
        assert report.match is None
        # It really did find the near-relation at nine digits ...
        assert report.n_provisional >= 1
        expressions = {i.expression for i in report.provisional}
        assert "(3*pi - 4*log(2))/12" in expressions
        # ... and every provisional match failed at thirty.
        assert report.n_rejected == report.n_provisional
        for item in report.provisional:
            assert item.confidence is K.IdentificationConfidence.REJECTED
            assert item.survived_escalation is False
        assert "dissolved" in report.reason

    def test_the_same_value_unperturbed_is_identified(self):
        """The control for the previous test: without the 1e-11 nudge it holds."""

        def exact(dps):
            with mp.workdps(dps + 10):
                return +(mp.pi / 4 - mp.log(2) / 3)

        report = K.identify_constant(provider=exact, base_digits=9, escalated_digits=30)
        assert report.identified is True
        assert report.match.expression == "(3*pi - 4*log(2))/12"

    def test_nine_digit_search_produces_many_coincidences(self):
        """The reason the escalation exists, measured rather than asserted."""

        def perturbed(dps):
            with mp.workdps(dps + 10):
                return +(mp.pi / 4 - mp.log(2) / 3 + mpf(10) ** -11)

        report = K.identify_constant(
            provider=perturbed, base_digits=9, escalated_digits=30
        )
        # A three-term search over eleven constants at nine digits is not a
        # sharp instrument: it returns dozens of relations, all of them noise.
        assert report.n_provisional > 20
        assert report.search_space_log10 > 9.0

    def test_float64_cannot_confirm_a_three_term_relation(self):
        """A double has 15 digits; the search space costs ~10.7. That is not enough."""
        value = float(LAMBDA1_TEXT)
        report = K.identify_constant(value, base_digits=10, escalated_digits=15)
        assert report.identified is False
        found = [i for i in report.provisional if i.n_terms == 3 and i.survived_escalation]
        assert found, "the true relation should still be visible, just unconfirmed"
        assert found[0].confidence is K.IdentificationConfidence.UNCONFIRMED
        assert found[0].surplus_digits < K.DEFAULT_MIN_SURPLUS_DIGITS
        assert "surplus" in report.reason

    def test_no_precision_headroom_is_reported_as_such(self):
        report = K.identify_constant(float(LAMBDA1_TEXT))
        assert report.identified is False
        assert report.escalated_digits is None
        assert "could not be escalated" in report.reason

    def test_a_high_precision_literal_supplies_its_own_headroom(self):
        report = K.identify_constant(LAMBDA1_TEXT, base_digits=15)
        assert report.identified is True
        # the literal carries 39 digits, so that is the ceiling — not the 40 the
        # caller asked for. The escalation never uses digits nobody wrote down.
        assert report.escalated_digits == 39
        assert report.match.digits_confirmed >= 30

    def test_bad_arguments_are_refused(self):
        with pytest.raises(K.KnownnessError):
            K.identify_constant()
        with pytest.raises(K.KnownnessError):
            K.identify_constant("1.5", base_digits=2)
        with pytest.raises(K.KnownnessError):
            K.identify_constant("1.5", max_terms=99)
        with pytest.raises(K.KnownnessError):
            K.identify_constant("1.5", known_digits=0)

    def test_report_is_json_serialisable(self):
        report = K.identify_constant(provider=exact_provider("1/7"))
        text = json.dumps(report.to_dict(), allow_nan=False)
        assert "1/7" in text

    def test_relation_involving_only_the_basis_is_discarded(self):
        # pslq over [x, 1, pi, pi^2] on a structureless x can return a relation
        # with a zero leading coefficient; those are not identifications.
        for item in K.identify_constant(self.NON_SPECIAL).provisional:
            assert item.terms  # never an empty expression


class TestEscalationMechanics:
    def test_surplus_is_digits_confirmed_minus_search_space(self):
        report = K.identify_constant(provider=lambda1_provider)
        match = report.match
        assert match.surplus_digits == pytest.approx(
            match.digits_confirmed - match.search_space_log10, abs=1e-9
        )

    def test_search_space_grows_with_the_number_of_terms(self):
        small = K._level_space_log10(11, 1, 24)
        large = K._level_space_log10(11, 3, 24)
        assert large > small + 3

    def test_raising_the_surplus_bar_can_refuse_a_true_relation(self):
        """The bar is a real bar: it refuses, it is not decorative."""
        strict = K.identify_constant(provider=lambda1_provider, min_surplus_digits=100.0)
        assert strict.identified is False
        assert strict.provisional[0].survived_escalation is True
        assert strict.provisional[0].confidence is K.IdentificationConfidence.UNCONFIRMED

    def test_a_provider_that_ignores_the_requested_precision_is_caught(self):
        """The escalation also catches a *provider* that does not escalate."""
        lazy = K.identify_constant(provider=lambda d: mpf(1) / 7)  # ignores d
        assert lazy.identified is False
        assert lazy.n_rejected >= 1

    def test_identification_evaluates_to_its_own_value(self):
        report = K.identify_constant(provider=lambda1_provider)
        with mp.workdps(45):
            assert abs(report.match.evaluate(45) - mpf(str(lambda1_provider(45)))) < (
                mpf(10) ** -35
            )


# ---------------------------------------------------------------------------
# 4. the known-facts registry
# ---------------------------------------------------------------------------


class TestKnownFactRegistry:
    def test_general_facts_are_registered_by_default(self):
        registered = {f.id for f in K.KNOWN_FACTS}
        assert {f.id for f in K.GENERAL_FACTS} <= registered

    def test_this_module_contributes_only_domain_neutral_entries(self):
        """The seam: subject-matter entries arrive from a domain module."""
        for fact in K.GENERAL_FACTS:
            assert fact.domain == "general"

    def test_a_bare_import_yields_a_general_only_registry(self):
        """Checked in a fresh interpreter, so no other import can muddy it."""
        code = (
            "import ontology.knownness as K; "
            "print(','.join(K.KNOWN_FACTS.domains()))"
        )
        proc = subprocess.run(
            [sys.executable, "-c", code],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            timeout=120,
        )
        assert proc.returncode == 0, proc.stderr
        assert proc.stdout.strip() == "general"

    def test_every_entry_has_the_four_mandatory_parts(self):
        for fact in list(K.GENERAL_FACTS) + list(ZETA_FACTS):
            assert fact.statement.strip()
            assert fact.canonical_form.strip()
            assert fact.source.strip()
            assert fact.match is not None
            assert K.KnownFactRegistry.reasons(fact) == ()

    def test_ids_are_unique_across_both_tables(self):
        ids = [f.id for f in list(K.GENERAL_FACTS) + list(ZETA_FACTS)]
        assert len(ids) == len(set(ids))

    def test_registration_refuses_a_sourceless_entry(self):
        registry = K.KnownFactRegistry()
        with pytest.raises(K.KnownnessError, match="source"):
            registry.register(
                K.KnownFact(
                    id="x", statement="s", canonical_form="c", source="  ", keys=("k",)
                )
            )

    def test_registration_refuses_an_unmatchable_entry(self):
        registry = K.KnownFactRegistry()
        with pytest.raises(K.KnownnessError, match="can never match"):
            registry.register(
                K.KnownFact(id="x", statement="s", canonical_form="c", source="src")
            )

    def test_registration_refuses_a_value_without_a_tolerance(self):
        registry = K.KnownFactRegistry()
        with pytest.raises(K.KnownnessError, match="tolerance"):
            registry.register(
                K.KnownFact(
                    id="x",
                    statement="s",
                    canonical_form="c",
                    source="src",
                    value="1.5",
                )
            )

    def test_registration_refuses_a_machine_local_path(self):
        registry = K.KnownFactRegistry()
        with pytest.raises(K.KnownnessError, match="machine-local"):
            registry.register(
                K.KnownFact(
                    id="x",
                    statement="s",
                    canonical_form="c",
                    # assembled at runtime so this file contains no such path
                    source="/Users" + "/someone/notes.md",
                    keys=("k",),
                )
            )

    def test_duplicate_ids_are_refused_unless_replaced(self):
        registry = K.KnownFactRegistry(K.GENERAL_FACTS)
        with pytest.raises(K.KnownnessError, match="already registered"):
            registry.register(K.GENERAL_FACTS[0])
        registry.register(K.GENERAL_FACTS[0], replace=True)
        assert len(registry) == len(K.GENERAL_FACTS)

    def test_value_match_uses_the_candidate_s_own_error_bound(self):
        registry = K.KnownFactRegistry(K.GENERAL_FACTS)
        with mp.workdps(30):
            gamma_text = mp.nstr(mp.euler, 25)
        candidate = constant_candidate("some limit", gamma_text, "1e-24")
        hit = registry.match(candidate)
        assert hit is not None
        assert hit.fact_id == "euler-mascheroni-constant"
        assert hit.match_kind == "value"
        assert hit.detail["defect"] <= hit.detail["tolerance"]

    def test_value_match_refuses_a_number_outside_its_own_error_bar(self):
        registry = K.KnownFactRegistry(K.GENERAL_FACTS)
        # gamma displaced by 1e-10, claimed to 1e-20. A generous global
        # tolerance would call this a match; its own error bar does not.
        candidate = constant_candidate(
            "some limit", "0.57721566500153286060", "1e-20"
        )
        assert registry.match(candidate) is None

    def test_an_alias_alone_suffices(self):
        registry = K.KnownFactRegistry(K.GENERAL_FACTS)
        for spelling in ("Hasse bound", "Hasse-Weil bound", "Weil bound"):
            hit = registry.match(structural_candidate(spelling))
            assert hit is not None and hit.fact_id == "hasse-weil-bound"
        assert registry.match(structural_candidate("Hasse-ish bound")) is None

    def test_keys_are_conjunctive(self):
        fact = K.KnownFact(
            id="both",
            statement="s",
            canonical_form="c",
            source="src",
            keys=("some family", "P holds"),
        )
        registry = K.KnownFactRegistry([fact])
        assert registry.match(structural_candidate("some family")) is not None
        fact_three = K.KnownFact(
            id="three",
            statement="s",
            canonical_form="c",
            source="src",
            keys=("some family", "P holds", "a scope nobody used"),
        )
        assert K.KnownFactRegistry([fact_three]).match(
            structural_candidate("some family")
        ) is None

    def test_alias_match_is_case_and_space_insensitive(self):
        registry = K.KnownFactRegistry(K.GENERAL_FACTS)
        assert registry.match(structural_candidate("  HASSE   BOUND ")) is not None

    def test_custom_matcher_is_used_when_supplied(self):
        seen = []

        def matcher(candidate, fact):
            seen.append(candidate.id)
            return K.FactMatch(
                fact_id=fact.id,
                match_kind="statement",
                source=fact.source,
                canonical_form=fact.canonical_form,
            )

        registry = K.KnownFactRegistry(
            [
                K.KnownFact(
                    id="always",
                    statement="s",
                    canonical_form="c",
                    source="src",
                    matcher=matcher,
                )
            ]
        )
        candidate = constant_candidate("anything", "1.5", "1e-9")
        assert registry.match(candidate).fact_id == "always"
        assert seen == [candidate.id]

    def test_known_entry_bridge_matches_the_schema_type(self):
        from ontology.schema import KnownEntry, match_known

        entries = K.KnownFactRegistry(K.GENERAL_FACTS).known_entries()
        assert all(isinstance(e, KnownEntry) for e in entries)
        with mp.workdps(30):
            gamma_text = mp.nstr(mp.euler, 25)
        candidate = constant_candidate("some limit", gamma_text, "1e-24")
        verdict = match_known(candidate, entries)
        assert verdict is not None and verdict.status is VerdictStatus.KNOWN

    def test_get_and_lookup(self):
        registry = K.KnownFactRegistry(K.GENERAL_FACTS)
        assert registry.get("hasse-weil-bound").domain == "general"
        assert "hasse-weil-bound" in registry
        with pytest.raises(K.KnownnessError):
            registry.get("no-such-fact")

    def test_clear_and_snapshot(self):
        registry = K.KnownFactRegistry(K.GENERAL_FACTS)
        snapshot = registry.snapshot()
        registry.clear()
        assert len(registry) == 0
        registry.register_all(snapshot)
        assert len(registry) == len(snapshot)

    def test_fact_to_dict_is_json_safe(self):
        for fact in list(K.GENERAL_FACTS) + list(ZETA_FACTS):
            json.dumps(fact.to_dict(), allow_nan=False)


# ---------------------------------------------------------------------------
# 5. the domain table: every quoted number is re-derived, not copied
# ---------------------------------------------------------------------------


class TestDomainFacts:
    def test_zeta_facts_register_into_a_fresh_registry(self):
        registry = K.KnownFactRegistry(K.GENERAL_FACTS)
        register_zeta_facts(registry)
        assert set(registry.domains()) == {"general", "zeta"}
        assert len(registry) == len(K.GENERAL_FACTS) + len(ZETA_FACTS)
        with pytest.raises(K.KnownnessError):
            register_zeta_facts(registry)
        register_zeta_facts(registry, replace=True)

    def test_general_numeric_entries_are_correct(self):
        expected = {
            "euler-mascheroni-constant": lambda: mp.euler,
            "catalan-constant": lambda: mp.catalan,
            "apery-constant": lambda: mp.zeta(3),
        }
        with mp.workdps(60):
            for fact_id, compute in expected.items():
                fact = next(f for f in K.GENERAL_FACTS if f.id == fact_id)
                quoted = mpf(str(fact.value))
                assert abs(quoted - compute()) < mpf(str(fact.tolerance))

    def test_zeta_numeric_entries_are_correct(self):
        from zeta.core import Xi

        with mp.workdps(60):
            checks = {
                "lit-li-lambda-1-closed-form": 1 + mp.euler / 2 - mp.log(4 * mp.pi) / 2,
                "lit-robin-constant": mp.exp(mp.euler),
                "lit-xi-at-zero": mpf(str(Xi(0, dps=55))),
                "lit-first-zero-ordinate": mp.zetazero(1).imag,
            }
            for fact_id, truth in checks.items():
                fact = next(f for f in ZETA_FACTS if f.id == fact_id)
                quoted = mpf(str(fact.value))
                assert abs(quoted - truth) < mpf(str(fact.tolerance)), fact_id

    def test_lambda_1_entry_matches_the_laboratory_routine(self):
        from zeta.li import li_closed_form_lambda1

        fact = next(f for f in ZETA_FACTS if f.id == "lit-li-lambda-1-closed-form")
        with mp.workdps(50):
            assert abs(mpf(str(fact.value)) - mpf(str(li_closed_form_lambda1(dps=45)))) < (
                mpf(str(fact.tolerance))
            )

    def test_the_domain_table_carries_the_counterexample_battery(self):
        """AGENTS.md: a property the Davenport-Heilbronn function shares is empty."""
        ids = {f.id for f in ZETA_FACTS}
        assert "lit-davenport-heilbronn-counterexample" in ids
        assert "lit-littlewood-sign-changes" in ids


# ---------------------------------------------------------------------------
# 6. the literature interface, and the novelty prohibition
# ---------------------------------------------------------------------------


class TestLiterature:
    def test_offline_lookup_returns_unknown(self):
        candidate = constant_candidate("q", "1.5", "1e-9")
        result = K.check_literature(candidate)
        assert result.status is K.LiteratureStatus.UNKNOWN
        assert result.online is False
        assert result.backend == "offline"
        assert result.sources_queried == ()
        assert result.references == ()

    def test_offline_lookup_labels_itself_not_recognised_offline(self):
        result = K.check_literature(constant_candidate("q", "1.5", "1e-9"))
        assert result.label == K.NOT_RECOGNISED_OFFLINE == "not-recognised-offline"

    def test_offline_detail_names_the_sources_it_could_not_reach(self):
        result = K.check_literature(constant_candidate("q", "1.5", "1e-9"))
        for source in ("OEIS", "arXiv", "MathSciNet"):
            assert source in result.detail
        assert "not consulted" in result.detail or "not checked" in result.detail

    def test_unknown_never_establishes_novelty(self):
        result = K.check_literature(constant_candidate("q", "1.5", "1e-9"))
        assert result.establishes_novelty is False

    def test_not_found_requires_named_sources(self):
        with pytest.raises(K.KnownnessError, match="name them"):
            K.LiteratureResult(
                status=K.LiteratureStatus.NOT_FOUND,
                label="checked",
                backend="pretend",
                online=True,
            )
        # with sources named it is allowed
        ok = K.LiteratureResult(
            status=K.LiteratureStatus.NOT_FOUND,
            label="checked",
            backend="pretend",
            online=True,
            sources_queried=("OEIS",),
        )
        assert ok.status is K.LiteratureStatus.NOT_FOUND

    def test_an_online_backend_may_not_return_unknown(self):
        with pytest.raises(K.KnownnessError):
            K.LiteratureResult(
                status=K.LiteratureStatus.UNKNOWN,
                label="x",
                backend="pretend",
                online=True,
            )

    def test_a_custom_backend_is_used(self):
        class Found(K.LiteratureBackend):
            name = "stub"
            online = True

            def lookup(self, candidate):
                return K.LiteratureResult(
                    status=K.LiteratureStatus.FOUND,
                    label="known-literature",
                    backend=self.name,
                    online=True,
                    sources_queried=("OEIS",),
                    references=("OEIS A001620",),
                )

        result = K.check_literature(constant_candidate("q", "1.5", "1e-9"), Found())
        assert result.status is K.LiteratureStatus.FOUND
        assert result.references == ("OEIS A001620",)

    def test_result_is_json_safe(self):
        result = K.check_literature(constant_candidate("q", "1.5", "1e-9"))
        text = json.dumps(result.to_dict(), allow_nan=False)
        assert '"establishes_novelty": false' in text


class TestNoveltyProhibition:
    @pytest.mark.parametrize(
        "label",
        [
            "novel",
            "novel-constant",
            "possibly novel",
            "NOVELTY",
            "unpublished-result",
            "original observation",
            "first-sighting",
            "unknown to science",
        ],
    )
    def test_novelty_labels_are_refused(self, label):
        with pytest.raises(K.KnownnessError, match="novelty"):
            K.funnel_label(label)

    @pytest.mark.parametrize(
        "label", ["not-recognised-offline", "known-catalogued", "known-closed-form"]
    )
    def test_honest_labels_pass(self, label):
        assert K.funnel_label(label) == label

    def test_empty_labels_are_refused(self):
        with pytest.raises(K.KnownnessError):
            K.funnel_label("   ")

    def test_no_outcome_of_the_gate_claims_novelty(self):
        for member in K.Knownness:
            K.funnel_label(member.value)
        assert set(K.Knownness) == {
            K.Knownness.KNOWN,
            K.Knownness.NOT_RECOGNISED_OFFLINE,
        }

    def test_the_forbidden_words_are_actually_screened_for(self):
        assert "novel" in K.FORBIDDEN_LABEL_WORDS
        for word in K.FORBIDDEN_LABEL_WORDS:
            with pytest.raises(K.KnownnessError):
                K.funnel_label(f"candidate-{word}")


# ---------------------------------------------------------------------------
# 7. the gate
# ---------------------------------------------------------------------------


class TestScreenKnown:
    def test_a_catalogued_constant_is_known_by_value(self):
        registry = K.KnownFactRegistry(K.GENERAL_FACTS)
        with mp.workdps(30):
            gamma_text = mp.nstr(mp.euler, 25)
        candidate = constant_candidate("a limit of harmonic sums", gamma_text, "1e-24")
        report = K.screen_known(candidate, facts=registry)
        assert report.outcome is K.Knownness.KNOWN
        assert report.is_known is True
        assert report.label == "known-catalogued"
        assert report.fact_match.fact_id == "euler-mascheroni-constant"
        assert report.references == (report.fact_match.source,)

    def test_a_known_verdict_satisfies_the_schema(self):
        registry = K.KnownFactRegistry(K.GENERAL_FACTS)
        with mp.workdps(30):
            gamma_text = mp.nstr(mp.euler, 25)
        candidate = constant_candidate("a limit of harmonic sums", gamma_text, "1e-24")
        report = K.screen_known(candidate, facts=registry)
        assert verdict_reasons(report.verdict) == ()
        assert report.verdict.status is VerdictStatus.KNOWN
        validate_candidate(candidate.with_verdict(report.verdict))

    def test_the_catalogue_runs_before_the_expensive_search(self):
        registry = K.KnownFactRegistry(K.GENERAL_FACTS)
        with mp.workdps(30):
            gamma_text = mp.nstr(mp.euler, 25)
        candidate = constant_candidate("a limit", gamma_text, "1e-24")
        report = K.screen_known(candidate, facts=registry)
        assert report.identification is None

    def test_a_closed_form_makes_a_candidate_known(self):
        registry = K.KnownFactRegistry()  # empty: force the search to decide
        candidate = constant_candidate("lambda_1 by contour integral", LAMBDA1_TEXT, "1e-38")
        report = K.screen_known(
            candidate, facts=registry, value_provider=lambda1_provider
        )
        assert report.outcome is K.Knownness.KNOWN
        assert report.label == "known-closed-form"
        assert report.identification.identified is True
        assert verdict_reasons(report.verdict) == ()
        assert report.verdict.evidence["match_kind"] == "identity"
        assert any("closed-form:" in r for r in report.references)

    def test_a_structureless_constant_is_not_recognised_offline(self):
        registry = K.KnownFactRegistry()
        candidate = constant_candidate(
            "a quantity", "0.8391027465019283746510293847561029384756", "1e-38"
        )
        report = K.screen_known(candidate, facts=registry)
        assert report.outcome is K.Knownness.NOT_RECOGNISED_OFFLINE
        assert report.label == "not-recognised-offline"
        assert report.verdict is None, "not recognised is not a verdict"
        assert report.references == ()
        assert report.literature.status is K.LiteratureStatus.UNKNOWN
        assert report.establishes_novelty is False

    def test_the_report_says_why_it_concluded_nothing(self):
        registry = K.KnownFactRegistry()
        candidate = constant_candidate(
            "a quantity", "0.8391027465019283746510293847561029384756", "1e-38"
        )
        report = K.screen_known(candidate, facts=registry)
        assert any("not recognised offline" in n for n in report.notes)
        assert any("not searched" in n for n in report.notes)
        assert any("closed-form search" in n for n in report.notes)

    def test_no_screening_outcome_is_ever_labelled_novel(self):
        registry = K.KnownFactRegistry(K.GENERAL_FACTS)
        candidates = [
            constant_candidate("a", "0.839102746501928374651029384756", "1e-28"),
            constant_candidate("b", "1.5", "1e-9"),
            structural_candidate("some family nobody has named"),
        ]
        for candidate in candidates:
            report = K.screen_known(candidate, facts=registry, identify=False)
            assert K.funnel_label(report.label) == report.label
            assert report.establishes_novelty is False
            record = report.to_dict()
            # The only place the word may appear is in a sentence forbidding it.
            for field in ("label", "outcome"):
                assert "novel" not in record[field].casefold()
            assert record["establishes_novelty"] is False
            assert record["literature"]["establishes_novelty"] is False

    def test_a_found_literature_hit_becomes_known(self):
        class Found(K.LiteratureBackend):
            name = "stub"
            online = True

            def lookup(self, candidate):
                return K.LiteratureResult(
                    status=K.LiteratureStatus.FOUND,
                    label="known-literature",
                    backend=self.name,
                    online=True,
                    sources_queried=("OEIS",),
                    references=("OEIS A000001",),
                )

        report = K.screen_known(
            constant_candidate("q", "1.5", "1e-9"),
            facts=K.KnownFactRegistry(),
            literature=Found(),
            identify=False,
        )
        assert report.outcome is K.Knownness.KNOWN
        assert report.label == "known-literature"
        assert verdict_reasons(report.verdict) == ()

    def test_a_non_constant_candidate_skips_the_numeric_search(self):
        report = K.screen_known(
            structural_candidate("an unnamed family"), facts=K.KnownFactRegistry()
        )
        assert report.identification is None
        assert report.outcome is K.Knownness.NOT_RECOGNISED_OFFLINE

    def test_a_zeta_domain_fact_is_caught_once_the_domain_is_registered(self):
        """The seam in action: the gate learns lambda_1 only from the domain."""
        bare = K.KnownFactRegistry(K.GENERAL_FACTS)
        candidate = constant_candidate("lambda_1", LAMBDA1_TEXT, "1e-30")
        assert K.screen_known(candidate, facts=bare, identify=False).outcome is (
            K.Knownness.NOT_RECOGNISED_OFFLINE
        )
        loaded = K.KnownFactRegistry(K.GENERAL_FACTS)
        register_zeta_facts(loaded)
        report = K.screen_known(candidate, facts=loaded, identify=False)
        assert report.outcome is K.Knownness.KNOWN
        assert report.fact_match.fact_id == "lit-li-lambda-1-closed-form"

    def test_report_is_json_serialisable(self):
        registry = K.KnownFactRegistry(K.GENERAL_FACTS)
        report = K.screen_known(
            constant_candidate("q", "1.5", "1e-9"), facts=registry, identify=False
        )
        json.dumps(report.to_dict(), allow_nan=False)

    def test_uncertainty_ceiling_is_respected(self):
        """A value claimed to four digits may not be identified to forty."""
        registry = K.KnownFactRegistry()
        candidate = constant_candidate("q", LAMBDA1_TEXT, "1e-6")
        report = K.screen_known(candidate, facts=registry)
        assert report.outcome is K.Knownness.NOT_RECOGNISED_OFFLINE
        assert report.identification.escalated_digits is None


# ---------------------------------------------------------------------------
# 8. module hygiene
# ---------------------------------------------------------------------------


class TestHygiene:
    def test_knownness_imports_no_laboratory_module(self):
        tree = ast.parse(MODULE_PATH.read_text(encoding="utf-8"))
        roots = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                roots.update(a.name.split(".")[0] for a in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module:
                roots.add(node.module.split(".")[0])
        assert "zeta" not in roots
        assert roots <= {
            "__future__",
            "ast",
            "datetime",
            "itertools",
            "math",
            "re",
            "collections",
            "dataclasses",
            "decimal",
            "enum",
            "typing",
            "mpmath",
            "ontology",
        }

    def test_importing_knownness_does_not_import_the_laboratory(self):
        code = (
            "import sys; import ontology.knownness; "
            "banned=[m for m in ('zeta','numpy','scipy','matplotlib','sympy') "
            "if m in sys.modules]; print(banned)"
        )
        proc = subprocess.run(
            [sys.executable, "-c", code],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            timeout=120,
        )
        assert proc.returncode == 0, proc.stderr
        assert proc.stdout.strip() == "[]", proc.stdout

    def test_no_machine_local_paths_in_the_sources(self):
        # The literal "/Users/" appears in the path *detector*; what must never
        # appear is a path with a username in it.
        pattern = re.compile(r"(?:/Users|/home)/[A-Za-z0-9._-]+/")
        for path in (MODULE_PATH, Path(__file__)):
            assert not pattern.search(path.read_text(encoding="utf-8")), path

    def test_public_surface_is_exported(self):
        for name in K.__all__:
            assert hasattr(K, name), name

    def test_mpmath_global_precision_is_left_alone(self):
        before = mp.dps
        K.identify_constant(provider=exact_provider("1/7"))
        K.safe_eval_expression("pi", 50)
        assert mp.dps == before

    def test_math_and_mp_are_not_confused(self):
        # a cheap guard that DEFAULT_MIN_SURPLUS_DIGITS is a real threshold
        assert K.DEFAULT_MIN_SURPLUS_DIGITS > 0
        assert math.isfinite(K.DEFAULT_MIN_SURPLUS_DIGITS)


# ---------------------------------------------------------------------------
# 9. honest-scope guards
# ---------------------------------------------------------------------------


class TestScope:
    def test_known_is_not_a_claim_about_significance(self):
        registry = K.KnownFactRegistry()
        candidate = constant_candidate("lambda_1 by contour integral", LAMBDA1_TEXT, "1e-38")
        report = K.screen_known(
            candidate, facts=registry, value_provider=lambda1_provider
        )
        assert "not" in report.verdict.notes.casefold()
        assert "significance" in report.verdict.notes.casefold()

    def test_the_gate_never_produces_a_survives_verdict(self):
        registry = K.KnownFactRegistry(K.GENERAL_FACTS)
        seen = []
        for candidate in (
            constant_candidate("a", "0.839102746501928374651029384756", "1e-28"),
            structural_candidate("Hasse bound"),
        ):
            report = K.screen_known(candidate, facts=registry, identify=False)
            seen.append(report.verdict)
            if report.verdict is not None:
                assert report.verdict.status is VerdictStatus.KNOWN
        # A conditional assertion is vacuous if the condition never holds, so
        # pin the shape of the population: exactly one of these is recognised.
        assert [v is None for v in seen] == [True, False], seen

    def test_an_unrecognised_candidate_stays_open(self):
        registry = K.KnownFactRegistry()
        candidate = constant_candidate(
            "a quantity", "0.8391027465019283746510293847561029384756", "1e-38"
        )
        report = K.screen_known(candidate, facts=registry)
        assert report.verdict is None
        assert candidate.verdict.status is VerdictStatus.OPEN
        assert Verdict.open().status is VerdictStatus.OPEN


# ---------------------------------------------------------------------------
# 10. adversarial review: two holes found by attacking the module
# ---------------------------------------------------------------------------


class TestTheWordNew:
    """The module's own rule is 'not "novel", not "new", not "unpublished"'.

    The first review of this module found that ``new`` was documented as
    forbidden and was not in the list, so ``funnel_label("new-result")`` was
    accepted. A rule the code does not enforce is not a rule.
    """

    @pytest.mark.parametrize(
        "label",
        [
            "new-result",
            "brand-new",
            "a new constant",
            "newly-identified",
            "undiscovered-value",
            "unrecorded-observation",
        ],
    )
    def test_a_label_claiming_the_observation_is_new_is_refused(self, label):
        with pytest.raises(K.KnownnessError, match="novelty"):
            K.funnel_label(label)

    def test_every_word_the_docstring_forbids_is_in_the_list(self):
        for word in ("novel", "new", "unpublished"):
            assert word in K.FORBIDDEN_LABEL_WORDS

    @pytest.mark.parametrize("label", ["renewed-search", "originally-catalogued"])
    def test_the_screen_is_whole_word_and_does_not_over_reach(self, label):
        assert K.funnel_label(label) == label

    def test_no_label_this_module_can_emit_is_refused_by_its_own_screen(self):
        for label in (
            K.NOT_RECOGNISED_OFFLINE,
            "known-catalogued",
            "known-closed-form",
            "known-literature",
        ):
            assert K.funnel_label(label) == label


class TestFoundMustCiteSomething:
    """``found`` is the claim that manufactures a terminal ``known`` verdict.

    ``not_found`` was already required to name the sources it consulted, but
    ``found`` — the stronger claim — was not required to cite anything, so a
    backend could make the gate emit a verdict that ``verdict_reasons``
    refuses, which aborts a funnel run three layers away.
    """

    def test_found_without_a_reference_is_refused_at_construction(self):
        with pytest.raises(K.KnownnessError, match="cite"):
            K.LiteratureResult(
                status=K.LiteratureStatus.FOUND,
                label="known-elsewhere",
                backend="sloppy",
                online=True,
                sources_queried=("OEIS",),
                references=(),
            )

    def test_blank_references_do_not_count_as_references(self):
        with pytest.raises(K.KnownnessError, match="cite"):
            K.LiteratureResult(
                status=K.LiteratureStatus.FOUND,
                label="known-elsewhere",
                backend="sloppy",
                online=True,
                references=("   ",),
            )

    def test_found_with_a_reference_is_accepted(self):
        result = K.LiteratureResult(
            status=K.LiteratureStatus.FOUND,
            label="known-elsewhere",
            backend="careful",
            online=True,
            sources_queried=("OEIS",),
            references=("OEIS A001620",),
        )
        assert result.references == ("OEIS A001620",)
        assert result.establishes_novelty is False

    def test_the_gate_never_returns_a_verdict_its_own_schema_refuses(self):
        """Every ``known`` verdict ``screen_known`` hands back is already earned."""

        class Careful(K.LiteratureBackend):
            name = "careful"
            online = True

            def lookup(self, candidate):
                return K.LiteratureResult(
                    status=K.LiteratureStatus.FOUND,
                    label="known-elsewhere",
                    backend=self.name,
                    online=True,
                    sources_queried=("OEIS",),
                    references=("OEIS A001620",),
                )

        candidate = constant_candidate(
            "an unmatched quantity", "1.98765432109876543210", "1e-18"
        )
        report = K.screen_known(
            candidate, facts=K.KnownFactRegistry(), identify=False, literature=Careful()
        )
        assert report.outcome is K.Knownness.KNOWN
        assert report.verdict is not None
        assert not verdict_reasons(report.verdict)

    def test_the_guard_fires_when_a_verdict_is_not_earned(self):
        """``_earned`` is the belt-and-braces check; exercise it directly."""
        unearned = Verdict(
            status=VerdictStatus.KNOWN,
            decided_by="x",
            decided_by_version="1",
            decided_at="2026-01-01T00:00:00+00:00",
            evidence={"references": [], "match_kind": "statement"},
        )
        with pytest.raises(K.KnownnessError, match="unearned"):
            K._earned(unearned)
        earned = Verdict(
            status=VerdictStatus.KNOWN,
            decided_by="x",
            decided_by_version="1",
            decided_at="2026-01-01T00:00:00+00:00",
            evidence={"references": ["a source"], "match_kind": "statement"},
        )
        assert K._earned(earned) is earned
