"""The three zeta-like interfaces must pass the caller's dps through.

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
"""
from __future__ import annotations

import inspect

import pytest

from zeta.epstein import dh_interface, epstein_interface, zeta_interface

BUILDERS = [
    pytest.param(lambda d: epstein_interface((2, 1, 3), dps=d), id="epstein"),
    pytest.param(lambda d: zeta_interface(dps=d), id="zeta"),
    pytest.param(lambda d: dh_interface(dps=d), id="dh"),
]


@pytest.mark.parametrize("build", BUILDERS)
def test_the_interface_does_not_clamp_the_requested_dps(build):
    """The regression proper, read off the closure rather than by running it.

    Calling count_zeros_box at dps=60 costs seconds; the defect is entirely in
    what the lambda captures, so the default is the thing to assert.
    """
    fn = build(60)["count_zeros_box"]
    defaults = {
        name: p.default
        for name, p in inspect.signature(fn).parameters.items()
        if p.default is not inspect.Parameter.empty
    }
    assert defaults.get("_d") == 60, (
        f"the interface captured _d={defaults.get('_d')!r} for a caller who "
        "asked for 60"
    )


@pytest.mark.parametrize("build", BUILDERS)
def test_no_literal_20_is_wired_into_the_counting_lambda(build):
    """The clamp was `min(_d, 20)` inside the closure, so a captured default of
    60 is necessary but not sufficient -- the constant could be applied at call
    time instead. Read the source of the lambda and require the clamp gone."""
    src = inspect.getsource(build(60)["count_zeros_box"])
    assert "min(" not in src.split("count_zeros_box(", 1)[-1], (
        "a min() survives in the count_zeros_box wiring:\n" + src
    )
