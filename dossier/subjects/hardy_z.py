"""The Hardy Z dossier — the one worked example.

Hardy's Z was chosen for the experiment because it is the object in this
repository where "formally valid, semantically wrong" is not hypothetical.
Three distinct functions in the tree are called some form of theta
(`AGENTS.md` devotes a section to the collision), Z is defined through one of
them, and there is a fourth near-miss — `|zeta(1/2+it)|` — which is real, has
exactly the same zeros, and is useless for the purpose Z exists to serve.

A definition that produced `|zeta(1/2+it)|` would satisfy "real-valued on the
critical line" and "vanishes exactly at the critical-line zeros" and would
still be the wrong object, because the entire point of Z is that it *changes
sign*. That is what a semantic obligation is for, and why this dossier marks
that obligation discriminating.

Everything asserted below is either measured by
``tests/test_dossier_hardy_z.py`` or marked not-attempted. Nothing here is
evidence for RH.
"""

from __future__ import annotations

from mpmath import mp

from dossier.schema import (
    Definition,
    Dependency,
    Dossier,
    Intent,
    OpenQuestion,
    RejectedAlternative,
    SemanticObligation,
)
from dossier.status import (
    AxisRecord,
    CertifiedStatus,
    FormalStatus,
    LiteratureStatus,
    NumericStatus,
    Support,
)

DOSSIER_NAME = "hardy_Z"

#: Sample ordinates used by every numeric obligation below, including two
#: known zeros so that the sign-change obligation has something to see.
SAMPLE_TS: tuple[float, ...] = (
    0.5,
    14.134725141734694,
    21.022039638771555,
    50.0,
    100.0,
    200.0,
    1000.0,
)

#: Worst |Z_completed(t) - Z(t)| over ``SAMPLE_TS`` at dps=30, measured
#: 2026-08-06 and pinned in tests/test_dossier_hardy_z.py.
DEFINITION_AGREEMENT_DEFECT = "3.4e-31"

__all__ = ["DOSSIER_NAME", "SAMPLE_TS", "DEFINITION_AGREEMENT_DEFECT", "Z_via_completed", "build"]


def Z_via_completed(t, dps: int = 30):
    """Hardy's Z by the completed-zeta route, with no branch of log Gamma.

        Z(t) = Lambda(1/2 + it) / (pi^(-1/4) * |Gamma(1/4 + it/2)|)

    This is the route ``lean/ZetaLean/HardyZ.lean`` takes, transcribed so the
    two definitions can be compared numerically rather than by inspection.

    Why it needs no branch: Lambda(1/2+it) = pi^(-1/4-it/2) Gamma(1/4+it/2)
    zeta(1/2+it), and dividing by the positive real pi^(-1/4)|Gamma| leaves
    (Gamma/|Gamma|) pi^(-it/2) zeta = e^{i(arg Gamma - (t/2)log pi)} zeta.
    The quotient Gamma/|Gamma| is an honest complex number; nobody had to pick
    a branch to form it. A branch is needed only when theta is wanted as a
    *real, continuous* phase counter — for Gram points and N(T) — which is a
    different requirement from defining Z.
    """
    with mp.workdps(dps + 10):
        s = mp.mpc(mp.mpf(1) / 2, t)
        completed = mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)
        denominator = mp.pi ** (mp.mpf(-1) / 4) * abs(mp.gamma(mp.mpc(mp.mpf(1) / 4, mp.mpf(t) / 2)))
        return completed / denominator


def build() -> Dossier:
    """Assemble the dossier. Pure data — no computation runs here."""
    return Dossier(
        name=DOSSIER_NAME,
        intent=Intent(
            purpose=(
                "A real-valued function of a real variable whose sign changes locate "
                "the zeros of zeta on the critical line. Real-valuedness is not the "
                "goal and neither is having the right zeros; the goal is that a "
                "bisection on Z finds an ordinate, which requires Z to take both "
                "signs."
            ),
            distinguishes_from=(
                "|zeta(1/2+it)| — real, and vanishes at exactly the same points, but "
                "never negative, so it has no sign changes to find and cannot serve "
                "the purpose",
                "rs_theta, the Riemann-Siegel phase theta(t) — the *phase* Z is built "
                "from, not Z itself (AGENTS.md, 'three different thetas')",
                "zeta.core.theta, the Jacobi theta function of the heat kernel — "
                "unrelated, same name",
                "explicit.theta_cheb, Chebyshev's prime sum — unrelated, same name",
                "Xi(t) = xi(1/2+it) — also real on the real line, also has the "
                "critical-line zeros, but is not |zeta|-normalised and decays "
                "super-exponentially, so it is unusable for zero-hunting at height",
            ),
            non_goals=(
                "Z is not a tool for deciding RH; it locates zeros that are on the "
                "line and is silent about any that are not",
                "Z is not defined here for complex argument",
            ),
        ),
        definition=Definition(
            statement="Z(t) = exp(i*theta(t)) * zeta(1/2 + i*t), for real t",
            notation="Z(t); theta(t) is the Riemann-Siegel phase, zeta.core.rs_theta",
            convention_choices={
                "theta branch": (
                    "theta = Im log Gamma(1/4 + it/2) - (t/2) log pi via mpmath's "
                    "loggamma, on the branch continuous with theta(0) = 0. NOT via "
                    "arg Gamma, which wraps at +-pi. The wrap does not affect Z "
                    "itself (see the completed-zeta route) but destroys theta as a "
                    "continuous phase counter, and Gram points and N(T) need that."
                ),
                "sign at t=0": (
                    "Z(0) = zeta(1/2) < 0. Fixed by theta(0) = 0; an implementation "
                    "that returned +|zeta(1/2)| has silently taken an absolute value."
                ),
            },
            domain_of_validity="real t; the formula as written is for the critical line only",
            reference="Titchmarsh, The Theory of the Riemann Zeta-Function, ch. IV; Edwards ch. 6",
        ),
        rejected=(
            RejectedAlternative(
                statement="Z(t) = |zeta(1/2 + i*t)|",
                why_rejected=(
                    "Real and vanishes exactly at the critical-line zeros, so it "
                    "passes the two obvious checks — and it is non-negative, so it "
                    "never changes sign and no bisection can find a zero with it. "
                    "This is the worked example of formally-defensible and "
                    "semantically wrong."
                ),
                would_be_correct_if="the purpose were to plot magnitude rather than to locate zeros",
            ),
            RejectedAlternative(
                statement="theta(t) = arg Gamma(1/4 + i*t/2) - (t/2) log pi",
                why_rejected=(
                    "The principal argument wraps at +-pi, so theta acquires jumps of "
                    "2*pi. Z is unaffected because only exp(i*theta) enters, but the "
                    "Gram points solve theta(g_n) = n*pi and N(T) counts theta(T)/pi, "
                    "and both are wrong the moment theta is discontinuous."
                ),
                would_be_correct_if="theta were never needed as a real-valued continuous phase",
            ),
            RejectedAlternative(
                statement="Z as a function returning a complex value near the critical line",
                why_rejected=(
                    "The realness that makes sign-hunting work is a property of the "
                    "critical line only. A Z typed as complex invites callers to "
                    "evaluate off the line, where the sign has no meaning."
                ),
                would_be_correct_if=(
                    "an intermediate formalisation needs complex algebra before "
                    "extracting realness — which is exactly the shape the current "
                    "Lean draft takes, deliberately"
                ),
            ),
        ),
        dependencies=(
            Dependency(name="zeta", relation="evaluated on the critical line", location="zeta.core.zeta"),
            Dependency(name="rs_theta", relation="supplies the phase", location="zeta.core.rs_theta"),
            Dependency(
                name="completed zeta / Gamma",
                relation="alternative route to the same function",
                location="lean/ZetaLean/HardyZ.lean",
            ),
        ),
        obligations=(
            SemanticObligation(
                name="real_valued",
                statement="Z(t) is real for real t",
                rationale=(
                    "Necessary, and nowhere near sufficient: |zeta(1/2+it)| satisfies "
                    "it too. Kept because a violation would mean the phase is wrong."
                ),
                discriminating=False,
                support=Support(
                    numeric=AxisRecord(
                        status=NumericStatus.AGREES_TO_TOLERANCE,
                        detail="|Im Z| < 1e-28 at dps=30 across the sample ordinates",
                        artifact="tests/test_dossier_hardy_z.py::test_Z_is_real_on_the_sample",
                    ),
                    literature=AxisRecord(
                        status=LiteratureStatus.STANDARD,
                        detail="Titchmarsh ch. IV",
                        artifact="references/papers.md",
                    ),
                    formal=AxisRecord(
                        status=FormalStatus.PROVED,
                        detail=(
                            "hardyZ_is_real: kernel run observed 2026-08-07 — "
                            "lake build, 8706 jobs, leanprover/lean4:v4.33.0-rc2, "
                            "root import wired"
                        ),
                        artifact="lean/ZetaLean/HardyZ.lean",
                    ),
                ),
            ),
            SemanticObligation(
                name="changes_sign",
                statement="Z takes both signs; in particular Z(0) < 0 < Z(100)",
                rationale=(
                    "THE discriminating obligation. |zeta(1/2+it)| passes every other "
                    "check in this dossier and fails this one, which is the whole "
                    "reason the dossier distinguishes them."
                ),
                discriminating=True,
                support=Support(
                    numeric=AxisRecord(
                        status=NumericStatus.AGREES_TO_TOLERANCE,
                        detail="Z(0) = zeta(1/2) = -1.4603545088... < 0 and Z(100) = +2.6926970... > 0",
                        artifact="tests/test_dossier_hardy_z.py::test_Z_changes_sign_but_the_rejected_alternative_does_not",
                    ),
                    literature=AxisRecord(
                        status=LiteratureStatus.STANDARD,
                        detail="the basis of every sign-change zero search since Gram",
                        artifact="references/papers.md",
                    ),
                    formal=AxisRecord(
                        status=FormalStatus.NOT_ATTEMPTED,
                        detail=(
                            "NOTHING in lean/ZetaLean/HardyZ.lean is about the sign of Z. "
                            "Four properties are formalised and this one, the only "
                            "discriminating obligation in the dossier, is not among them. "
                            "continuous_hardyZ is the prerequisite for an "
                            "intermediate-value argument, so the groundwork exists and the "
                            "statement does not."
                        ),
                    ),
                ),
            ),
            SemanticObligation(
                name="magnitude_matches_zeta",
                statement="|Z(t)| = |zeta(1/2 + i*t)|",
                rationale=(
                    "Discriminating against a mis-normalised phase: any e^{i*psi} with "
                    "psi != theta still gives |Z| = |zeta|, but a definition that "
                    "picked up a real factor — an extra Gamma, a stray pi power — "
                    "fails here while still being real and still vanishing correctly."
                ),
                discriminating=True,
                support=Support(
                    numeric=AxisRecord(
                        status=NumericStatus.AGREES_TO_TOLERANCE,
                        detail="agrees to < 1e-28 at dps=30 across the sample ordinates",
                        artifact="tests/test_dossier_hardy_z.py::test_magnitude_matches_zeta",
                    ),
                    formal=AxisRecord(
                        status=FormalStatus.PROVED,
                        detail=(
                            "abs_hardyZ_eq_abs_zeta: kernel run observed 2026-08-07 — "
                            "lake build, 8706 jobs, leanprover/lean4:v4.33.0-rc2, "
                            "root import wired"
                        ),
                        artifact="lean/ZetaLean/HardyZ.lean",
                    ),
                ),
            ),
            SemanticObligation(
                name="agrees_with_completed_zeta_route",
                statement=(
                    "exp(i*theta(t))*zeta(1/2+it) equals "
                    "Lambda(1/2+it)/(pi^(-1/4)*|Gamma(1/4+it/2)|)"
                ),
                rationale=(
                    "The two definitions in this tree must be the same function. The "
                    "Python one goes through a branch-sensitive real theta; the Lean "
                    "draft avoids any branch. Agreement is what licenses treating the "
                    "Lean statement as being about this object — the exact place a "
                    "formalisation usually drifts from what was meant."
                ),
                discriminating=True,
                support=Support(
                    numeric=AxisRecord(
                        status=NumericStatus.AGREES_TO_TOLERANCE,
                        detail=f"worst |difference| = {DEFINITION_AGREEMENT_DEFECT} at dps=30",
                        artifact="tests/test_dossier_hardy_z.py::test_the_two_definitions_agree",
                    ),
                    formal=AxisRecord(
                        status=FormalStatus.NOT_ATTEMPTED,
                        detail=(
                            "the Lean draft states the definition only; the equivalence "
                            "is not stated there"
                        ),
                    ),
                ),
            ),
            SemanticObligation(
                name="even",
                statement="Z(-t) = Z(t)",
                rationale="Follows from the functional equation; a cheap check that the phase has the right parity.",
                discriminating=False,
                support=Support(
                    numeric=AxisRecord(
                        status=NumericStatus.AGREES_TO_TOLERANCE,
                        detail="agrees to < 1e-28 at dps=30 across the sample ordinates",
                        artifact="tests/test_dossier_hardy_z.py::test_Z_is_even",
                    ),
                    formal=AxisRecord(
                        status=FormalStatus.PROVED,
                        detail=(
                            "hardyZ_even: kernel run observed 2026-08-07 — "
                            "lake build, 8706 jobs, leanprover/lean4:v4.33.0-rc2, "
                            "root import wired"
                        ),
                        artifact="lean/ZetaLean/HardyZ.lean",
                    ),
                ),
            ),
        ),
        support=Support(
            numeric=AxisRecord(
                status=NumericStatus.AGREES_TO_TOLERANCE,
                detail=(
                    "every obligation above is measured; the two independent "
                    "definitions agree to 3.4e-31 at dps=30"
                ),
                artifact="tests/test_dossier_hardy_z.py",
            ),
            certified=AxisRecord(
                status=CertifiedStatus.NOT_ATTEMPTED,
                detail=(
                    "zeta/rigor.py can enclose Z at a point, but no enclosure of any "
                    "obligation in this dossier has been run. Nothing here is certified "
                    "and the word is not being used."
                ),
            ),
            literature=AxisRecord(
                status=LiteratureStatus.STANDARD,
                detail=(
                    "Hardy's Z is textbook material: Titchmarsh ch. IV, Edwards ch. 6. "
                    "Nothing in this dossier is a new claim."
                ),
                artifact="references/papers.md",
            ),
            formal=AxisRecord(
                status=FormalStatus.PROVED,
                detail=(
                    "lean/ZetaLean/HardyZ.lean: the definition and five complete lemmas "
                    "— hardyZ_is_real, abs_hardyZ_eq_abs_zeta, hardyZ_even, "
                    "hardyZ_zero_iff, continuous_hardyZ — accepted by the kernel in a "
                    "watched run: lake build, 8706 jobs, leanprover/lean4:v4.33.0-rc2, "
                    "observed 2026-08-07. The root import has wired ZetaLean.HardyZ "
                    "since 150ac05 (whose build compiled it for the first time); the "
                    "file itself is unchanged since d11f297. 'Proved' is a statement "
                    "about these five lemmas, not the dossier: the discriminating sign "
                    "obligation remains not-attempted, so the formalisation is still "
                    "complete about everything except the thing that makes Z worth "
                    "defining. History kept deliberately: this record read "
                    "stated-unchecked — correctly at the time, HardyZ.lean was outside "
                    "the root import — and then stayed stale for ~3 hours after "
                    "150ac05's green build, because nothing coupled build evidence to "
                    "recorded status. That coupling now exists: the tripwire tests in "
                    "tests/test_dossier_hardy_z.py."
                ),
                artifact="lean/ZetaLean/HardyZ.lean",
            ),
        ),
        open_questions=(
            OpenQuestion(
                question=(
                    "Should the Lean definition return R or C? The draft returns C and "
                    "notes the question in its own docstring."
                ),
                what_would_settle_it=(
                    "proving hardyZ_is_real in Lean; until the realness is a theorem "
                    "rather than a comment, a C-valued Z is the honest type"
                ),
                blocked_on="riemannZeta_conj and completedRiemannZeta_one_sub in Mathlib",
            ),
            OpenQuestion(
                question=(
                    "Is the completed-zeta route the one to upstream to Mathlib, or "
                    "should Mathlib get rs_theta first and define Z from it?"
                ),
                what_would_settle_it=(
                    "a check_target run in ~/contrib-lab on both, plus whether Mathlib "
                    "already has a continuous log-Gamma branch"
                ),
                blocked_on="contrib-lab target file for hardyZ",
            ),
            OpenQuestion(
                question=(
                    "The formalisation covers every obligation except the discriminating "
                    "one. Lean has hardyZ_is_real, abs_hardyZ_eq_abs_zeta, hardyZ_even, "
                    "hardyZ_zero_iff and continuous_hardyZ — and nothing about the sign "
                    "of Z, which is the only property that makes Z the right object "
                    "rather than |zeta(1/2+it)|. Is that a gap or a deliberate ordering?"
                ),
                what_would_settle_it=(
                    "a Lean statement that Z takes both signs — e.g. hardyZ 0 < 0 and "
                    "0 < hardyZ 100, or an existence-of-sign-change lemma. "
                    "continuous_hardyZ is already there, so the intermediate value "
                    "theorem is available and the missing piece is two numeric bounds, "
                    "which is exactly what lean/ZetaLean/Rigor.lean is for"
                ),
                blocked_on="rigorous numeric evaluation of Z at a point in Lean",
            ),
            OpenQuestion(
                question=(
                    "Does anything in this dossier deserve an enclosure rather than a "
                    "float check?"
                ),
                what_would_settle_it=(
                    "running zeta.rigor.enclose_Z on the sign-change obligation; that "
                    "would move one axis from agrees-to-tolerance to certified and is "
                    "the single most informative next step"
                ),
            ),
        ),
        notes=(
            "Experiment, side project, probe. This dossier records research state "
            "about a textbook object. It is not evidence for anything, and Hardy's Z "
            "locating zeros on the line says nothing about zeros off it."
        ),
    )
