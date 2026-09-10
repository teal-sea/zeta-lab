"""A guard for the Epstein evaluator, with the faults that make it fire.

`zeta/epstein.py` is outside what a hunt may write, so this is a reference
implementation and its test, not a landed change.  What it has to be is a rule
that refuses rather than a constant in a comment: `hunts/gate5_p6_c/probe.py`
already carries the constant, and the constant did not stop anything.

The rule.  For `Lambda_Q(s)` computed as `epstein_completed` computes it, the
decimal digits lost to cancellation are

    L(sigma, t) = 0.68219 t - (sigma - 1/2) log10 t - 0.399,

and the working precision a caller actually receives is `dps + 20`, because
`epstein_zeta` opens `workdps(dps + 10)` and then calls `epstein_completed`
with `dps = mp.dps`, which opens `workdps(dps + 10)` again.  So the answer
carries about `dps + 20 - L(sigma, t)` correct decimal digits and the guard
refuses when that falls below the caller's stated need.

Run this file to execute its own planted-fault ladder.
"""
from __future__ import annotations

import math
import sys
from pathlib import Path

from mpmath import mp

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(Path(__file__).resolve().parent))

from law import digits_lost, required_dps            # noqa: E402
from zeta.epstein import epstein_zeta                # noqa: E402

#: what a caller who says nothing should be assumed to want
DEFAULT_WANTED_DIGITS = 10


class PrecisionTooLow(ArithmeticError):
    """Raised instead of returning a value with no correct digits."""


def guarded_epstein_zeta(s, form, dps: int = 30, want_digits: int = DEFAULT_WANTED_DIGITS):
    """`epstein_zeta` that refuses rather than returning noise.

    The refusal is the point.  `count_zeros_box`'s integrality check cannot
    catch this, because noise winds to an integer as readily as signal does,
    which is the same argument `tests/test_interface_dps_is_honoured.py` makes
    for its own guard.
    """
    s = mp.mpc(s)
    sigma, t = float(mp.re(s)), abs(float(mp.im(s)))
    need = required_dps(sigma, t, want_digits)
    if dps < need:
        raise PrecisionTooLow(
            f"epstein_zeta at sigma={sigma:g}, t={t:g} loses about "
            f"{digits_lost(sigma, t):.0f} digits to cancellation; dps={dps} "
            f"carries about {dps + 20 - digits_lost(sigma, t):.0f} correct "
            f"digits and {want_digits} were asked for. Use dps >= {need}.")
    return epstein_zeta(s, form, dps=dps)


# --- the planted-fault ladder -------------------------------------------------

def _lattice_truth(s, form, qmax=20000, work=None):
    from probe import direct_lattice
    with mp.workdps(work or (60 + int(0.6822 * abs(float(mp.im(mp.mpc(s))))))):
        val, tail = direct_lattice(mp.mpc(s), form, qmax)
        return mp.mpc(val), tail


def main() -> None:
    form = (1, 1, 4)
    failures = []

    def check(name, cond, detail=""):
        print(f"  {'PASS' if cond else 'FAIL'}  {name}{(' -- ' + detail) if detail else ''}")
        if not cond:
            failures.append(name)

    print("planted faults, each of which the guard must catch:")

    # 1. the exact case hunts/dps_cap measured: 0.8 + 85.7i at a low precision
    try:
        guarded_epstein_zeta(mp.mpc("0.8", "85.7"), (2, 1, 3), dps=20)
        check("refuses 0.8 + 85.7i at dps 20", False, "it returned a value")
    except PrecisionTooLow as exc:
        check("refuses 0.8 + 85.7i at dps 20", True, str(exc)[:70] + "...")

    # 2. a height where the unguarded routine is wrong by many orders of magnitude
    truth, _ = _lattice_truth(mp.mpc(5, 120), form)
    with mp.workdps(60):
        bad = mp.mpc(epstein_zeta(mp.mpc(5, 120), form, dps=15))
        rel = abs(bad - truth) / abs(truth)
    check("the unguarded routine really is wrong at t=120, dps=15", rel > 1.0,
          f"relative error {float(rel):.3e}")
    try:
        guarded_epstein_zeta(mp.mpc(5, 120), form, dps=15)
        check("refuses t=120 at dps 15", False, "it returned a value")
    except PrecisionTooLow:
        check("refuses t=120 at dps 15", True)

    # 3. the control: it must NOT refuse where the routine is fine
    try:
        v = guarded_epstein_zeta(mp.mpc(5, 20), form, dps=30)
        truth20, _ = _lattice_truth(mp.mpc(5, 20), form)
        with mp.workdps(60):
            rel = abs(mp.mpc(v) - truth20) / abs(truth20)
        check("allows t=20 at dps 30, and the value is right", rel < 1e-12,
              f"relative error {float(rel):.3e}")
    except PrecisionTooLow as exc:
        check("allows t=20 at dps 30", False, f"refused: {exc}")

    # 4. the guard must be sensitive to sigma, since the critical line is worst
    check("the critical line needs more precision than sigma = 5 at the same height",
          required_dps(0.5, 100) > required_dps(5.0, 100),
          f"{required_dps(0.5, 100)} vs {required_dps(5.0, 100)}")

    # 5. a guard that cannot fire is broken: break the constant and watch it stop
    import law
    saved = law.LEAD
    try:
        law.LEAD = 0.0                      # the fault: pretend nothing cancels
        try:
            guarded_epstein_zeta(mp.mpc(5, 120), form, dps=15)
            check("with the cancellation constant set to zero the guard stops firing",
                  True, "as it must, which is what makes rung 2 meaningful")
        except PrecisionTooLow:
            check("with the cancellation constant set to zero the guard stops firing",
                  False, "it still fired, so rung 2 was not testing the constant")
    finally:
        law.LEAD = saved

    print()
    print("failures:", failures or "none")
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
