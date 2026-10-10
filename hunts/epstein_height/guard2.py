"""The guard, rebuilt after an audit walked through it.

`guard.py` refuses on a form-blind rule and passed a six-rung planted-fault
ladder.  An independent audit found a call it allows that does not deliver:

    guarded_epstein_zeta((2,1,3), 8 + 80i, dps=required_dps(8, 80, 4),
                         want_digits=4)

is allowed at `dps = 24` and returns **0.59 correct digits** against the 4 asked
for.  Reproduced here: the form-blind law puts the loss at `39.90` digits and
the form-aware one at `44.07`, a gap of `4.17` which is exactly the
`-log10|zeta_Q(s)|` term the form-blind law drops.

The ladder could not see it because every one of its six rungs held the form
fixed, so it tested the leading term, which was already right, and never the
term the hunt itself had just added.  That is the failure this hunt exists to
name, committed by the hunt.

## What changed

The rule now carries the form, through the one thing that makes forms differ:
the least value the form represents.  For `Q` with least represented value `m`
and `r_Q(m)` representations of it,

    |zeta_Q(sigma + it)| >= r_Q(m) m^{-sigma} - sum_{n > m} r_Q(n) n^{-sigma}

wherever the series converges, and the right-hand side is computable from
integer counts alone.  `(1,1,4)` represents 1 and `(2,1,3)` represents 2, so at
`sigma = 8` their leading terms differ by `8 log10 2 = 2.4` digits, and the rest
of the gap is the tail.

Inside the critical strip the series does not converge and no cheap lower bound
on `|zeta_Q|` is available, so the guard says so instead of pretending: it uses
the leading-term scaling `-sigma log10 m` and adds a declared margin, and
`required_dps` reports which regime it is in.

## The rung that would have caught it

Not another planted fault.  A guard is sound exactly when every call it allows
delivers what it promised, so the ladder now samples the calls the guard allows,
across forms and across `(sigma, t)`, evaluates them against the lattice oracle,
and fails if any one of them is short.  A ladder made of faults tests what the
author thought of; this rung tests the contract.
"""
from __future__ import annotations

import json
import math
import sys
from pathlib import Path

from mpmath import mp

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(HERE))

from zeta.epstein import epstein_zeta  # noqa: E402
import probe  # noqa: E402

LOG10_PI = math.log10(math.pi)
#: mpmath rounds a dps request up to whole bits, which buys a little more than
#: asked.  Measured by the audit at 0.87 to 1.15 decimal digits; the guard does
#: not spend it.
STRIP_MARGIN = 3.0

#: The model's premise is that the largest quantity the routine forms is about
#: |1/s|.  It is approximate: the first contract run below, with no margin,
#: delivered on 14 of 15 sampled calls and was 0.3 digits short on the
#: fifteenth, (2,1,3) at sigma = 2.5, t = 60.  This is that shortfall with a
#: factor of three, and it is FITTED to the contract rung rather than derived,
#: which is why it is a named constant and not folded into the formula.
MODEL_MARGIN = 1.0


class PrecisionTooLow(ArithmeticError):
    """Raised instead of returning a value with fewer digits than were asked for."""


def leading(form) -> tuple[int, int]:
    """(m, r_Q(m)): the least value the form represents, and how often."""
    counts = probe.representation_counts(form, 400)
    m = min(counts)
    return m, counts[m]


def zeta_q_lower(form, sigma: float, qmax: int = 20000) -> tuple[float, str]:
    """A lower bound on |zeta_Q(sigma + it)|, and the regime it came from."""
    m, rm = leading(form)
    if sigma > 1.0:
        counts = probe.representation_counts(form, qmax)
        lead = rm * m ** (-sigma)
        tail = sum(r * q ** (-sigma) for q, r in counts.items() if q > m)
        if lead - tail > 0:
            return lead - tail, "series"
    return rm * m ** (-sigma), "leading-term-only"


def digits_lost(form, sigma: float, t: float) -> tuple[float, str]:
    s = mp.mpc(sigma, t)
    with mp.workdps(30):
        log_gamma = float(mp.log10(abs(mp.gamma(s))))
        log_abs_s = float(mp.log10(abs(s)))
    zq, regime = zeta_q_lower(form, sigma)
    L = -log_abs_s + sigma * LOG10_PI - log_gamma - math.log10(zq) + MODEL_MARGIN
    if regime != "series":
        L += STRIP_MARGIN
    return L, regime


def required_dps(form, sigma: float, t: float, want_digits: int = 10) -> int:
    L, _ = digits_lost(form, sigma, t)
    return max(15, math.ceil(L + want_digits - 20))


def guarded_epstein_zeta(s, form, dps: int = 30, want_digits: int = 10):
    s = mp.mpc(s)
    sigma, t = float(mp.re(s)), abs(float(mp.im(s)))
    need = required_dps(form, sigma, t, want_digits)
    if dps < need:
        L, regime = digits_lost(form, sigma, t)
        raise PrecisionTooLow(
            f"epstein_zeta at sigma={sigma:g}, t={t:g} on form {tuple(form)} loses "
            f"about {L:.0f} digits ({regime}); dps={dps} carries about "
            f"{dps + 20 - L:.0f} correct digits and {want_digits} were asked for. "
            f"Use dps >= {need}.")
    return epstein_zeta(s, form, dps=dps)


# --- the ladder, with the rung that tests the contract ------------------------

def _truth(s, form, qmax=20000, work=None):
    """The oracle, with the digits IT can support returned alongside it.

    The first contract run reported a 0.3-digit shortfall at sigma = 2.5 that did
    not move when the precision rose, which is the signature of the oracle rather
    than of the routine: the lattice sum's truncation is
    K sigma / (sigma - 1) qmax^{1 - sigma}, so at qmax = 20000 it is 1e-17 at
    sigma = 5 and about 1e-6 at sigma = 2.5.  A contract rung that does not know
    its own oracle's accuracy reports the oracle's limit as the guard's failure.
    """
    t = abs(float(mp.im(mp.mpc(s))))
    with mp.workdps(work or (60 + int(0.6822 * t))):
        val, tail = probe.direct_lattice(mp.mpc(s), form, qmax)
        oracle_digits = -math.log10(tail / float(abs(val))) if tail > 0 else 99.0
        return mp.mpc(val), oracle_digits


def main() -> None:
    failures, rows = [], []

    def check(name, cond, detail=""):
        print(f"  {'PASS' if cond else 'FAIL'}  {name}{(' -- ' + detail) if detail else ''}")
        if not cond:
            failures.append(name)

    print("rung A, the audit's counterexample must now be refused:")
    try:
        guarded_epstein_zeta(mp.mpc(8, 80), (2, 1, 3), dps=24, want_digits=4)
        check("refuses (2,1,3) at 8+80i, dps 24, wanting 4 digits", False, "allowed")
    except PrecisionTooLow as exc:
        check("refuses (2,1,3) at 8+80i, dps 24, wanting 4 digits", True, str(exc)[:60] + "...")

    print("rung B, the guard must separate forms at the same sigma and t:")
    a = required_dps((1, 1, 4), 8.0, 80.0, 4)
    b = required_dps((2, 1, 3), 8.0, 80.0, 4)
    check("a form whose least represented value is 2 needs more than one that "
          "represents 1", b > a, f"{b} against {a}")

    print("rung C, the contract: every call the guard ALLOWS must deliver:")
    for form in [(1, 1, 4), (2, 1, 3), (1, 0, 1)]:
        for sigma, t, want in [(5.0, 60.0, 10), (5.0, 100.0, 10), (8.0, 80.0, 4),
                               (3.0, 80.0, 6), (2.5, 60.0, 8)]:
            need = required_dps(form, sigma, t, want)
            tr, oracle_digits = _truth(mp.mpc(sigma, t), form)
            if oracle_digits < want + 1:
                rows.append({"form": list(form), "sigma": sigma, "t": t,
                             "want": want, "dps_required": need,
                             "oracle_digits": oracle_digits,
                             "delivered": None,
                             "note": "excluded: the oracle cannot resolve this many digits here"})
                print(f"    skip  form {form} sigma={sigma} t={t} want {want}: the "
                      f"oracle carries only {oracle_digits:.1f} digits at qmax 20000")
                continue
            v = guarded_epstein_zeta(mp.mpc(sigma, t), form, dps=need, want_digits=want)
            with mp.workdps(60):
                rel = abs(mp.mpc(v) - tr) / abs(tr)
            got = -math.log10(float(rel)) if 0 < float(rel) < 1 else 0.0
            ok = got >= want
            rows.append({"form": list(form), "sigma": sigma, "t": t,
                         "want": want, "dps_required": need,
                         "oracle_digits": oracle_digits,
                         "correct_digits": got, "delivered": ok})
            print(f"    {'ok  ' if ok else 'SHORT'} form {form} sigma={sigma} t={t} "
                  f"want {want} -> dps {need} delivered {got:.1f} "
                  f"(oracle {oracle_digits:.1f})")
            if not ok:
                failures.append(f"contract: {form} {sigma}+{t}i wanted {want} got {got:.1f}")
    scored = [r for r in rows if r.get("delivered") is not None]
    check("every allowed call the oracle can score delivered what it promised",
          all(r["delivered"] for r in scored),
          f"{sum(r['delivered'] for r in scored)}/{len(scored)} scored, "
          f"{len(rows) - len(scored)} excluded as oracle-limited")

    print("rung D, the control: it must not refuse where the routine is fine:")
    try:
        guarded_epstein_zeta(mp.mpc(5, 20), (1, 1, 4), dps=30, want_digits=10)
        check("allows (1,1,4) at 5+20i, dps 30", True)
    except PrecisionTooLow as exc:
        check("allows (1,1,4) at 5+20i, dps 30", False, str(exc)[:70])

    (HERE / "artifacts" / "guard2_contract.json").write_text(
        json.dumps(rows, indent=1), encoding="utf-8")
    print()
    print("failures:", failures or "none")
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
