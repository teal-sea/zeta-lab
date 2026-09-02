"""Every zeta-like interface must pass the caller's dps through.

`epstein_interface`, `zeta_interface` and `dh_interface` each used to wire
their `count_zeros_box` with `dps=min(_d, 20)`, silently overriding a caller
who asked for more. `hunts/dps_cap` measured the cost at 0.8 + 85.7i:
`epstein_completed` returns 3.1e-33 against a converged 1.6e-58 -- a factor of
1.9e25, and not one correct digit -- because the routine's absolute error
floor sits near 1e-(D+13) and nothing correct appears below D ~ 46.

`count_zeros_box`'s own integrality check does not catch it. Noise winds to an
integer as readily as signal does, so the capped path returned a plausible
wrong zero count rather than raising, which is the whole reason this needs a
test rather than a comment.

**The interfaces are DISCOVERED, not listed.** While this fix was in review a
fourth one, `shifted_interface`, was added on main with the clamp copied in
from its siblings. A test naming three interfaces would have passed over it.
Anything in this module ending `_interface` and returning a `count_zeros_box`
is checked, so the next one is covered before it is written.
"""
from __future__ import annotations

import inspect

import pytest

from zeta import epstein

#: One representative argument set per interface, since they take different
#: leading parameters. A discovered interface with no entry here fails the
#: coverage test below rather than being silently skipped.
ARGS: dict[str, tuple] = {
    "epstein_interface": ((2, 1, 3),),
    "zeta_interface": (),
    "dh_interface": (),
    "shifted_interface": (),
}


def _interfaces() -> list[str]:
    return sorted(
        n for n in dir(epstein)
        if n.endswith("_interface") and callable(getattr(epstein, n))
    )


def _build(name: str, dps: int):
    fn = getattr(epstein, name)
    args = ARGS.get(name, ())
    try:
        return fn(*args, dps=dps)
    except TypeError as exc:                     # pragma: no cover - diagnostic
        pytest.fail(f"{name} could not be built with {args!r}, dps={dps}: {exc}")


def test_every_interface_in_the_module_is_covered_here():
    """The discovery is only as good as ARGS: a new interface this file does
    not know how to build must fail loudly, not vanish from the sweep."""
    missing = [n for n in _interfaces() if n not in ARGS]
    assert not missing, (
        f"interfaces with no ARGS entry, so untested: {missing}. "
        "Add how to build them; do not delete them from the sweep."
    )


@pytest.mark.parametrize("name", _interfaces())
def test_the_interface_does_not_clamp_the_requested_dps(name):
    """Read off the closure rather than by running it: calling
    count_zeros_box at dps=60 costs seconds, and the defect is entirely in
    what the lambda captures."""
    iface = _build(name, 60)
    if "count_zeros_box" not in iface:
        pytest.skip(f"{name} exposes no count_zeros_box")
    defaults = {
        p_name: p.default
        for p_name, p in inspect.signature(iface["count_zeros_box"]).parameters.items()
        if p.default is not inspect.Parameter.empty
    }
    assert defaults.get("_d") == 60, (
        f"{name} captured _d={defaults.get('_d')!r} for a caller who asked for 60"
    )


@pytest.mark.parametrize("name", _interfaces())
def test_no_clamp_survives_inside_the_counting_lambda(name):
    """A captured default of 60 is necessary but NOT sufficient: the clamp was
    `min(_d, 20)` applied inside the closure, so the default read 60 the whole
    time it was broken. This is the assertion that actually caught it."""
    iface = _build(name, 60)
    if "count_zeros_box" not in iface:
        pytest.skip(f"{name} exposes no count_zeros_box")
    src = inspect.getsource(iface["count_zeros_box"])
    body = src.split("count_zeros_box(", 1)[-1]
    assert "min(" not in body, f"a min() survives in {name}'s wiring:\n{src}"
