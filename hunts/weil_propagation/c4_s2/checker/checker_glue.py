"""checker/: the seam to kernel/ and two_adic/.

Phase 1 (ebf0eae): nothing routed, every loader raised NotRouted.
Phase 2 (after the coordinator routed kernel/ af756a5 and two_adic/ c7e9f57):
only the call glue below changed; the properties in test_checker_props.py
did not.

Routed entry points (read-only use):
- kernel/sonin.py: T_inf_matrix(c, N, dps) = A + E (CC Thm 4.7).
- two_adic/ta_ts.py: T_S_matrix(c, N, dps, local_data, arch_type, s_inf);
  refuses non-unitary data (ta_data.NonUnitaryLocalData), refuses Gamma_C
  (FrameworkLimit), raises KernelUnavailable while its provider is unwired.

Expected shapes (mission interface contract): Hermitian (2N+1) x (2N+1)
mpmath matrices on U_n, n = -N..N, index 0 is n = -N, F(f) = v^* M v.
"""

from __future__ import annotations

import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
KERNEL = os.path.abspath(os.path.join(HERE, "..", "kernel"))
TWO_ADIC = os.path.abspath(os.path.join(HERE, "..", "two_adic"))


class NotRouted(RuntimeError):
    """kernel/ or two_adic/ output has not been routed to checker/ yet, or
    the routed module cannot yet produce the requested object."""


class NotExposed(RuntimeError):
    """The routed builder has no code path for the requested variant."""


class Refused(RuntimeError):
    """The routed builder refused the data (the provider's own refusal,
    translated here). Any other exception propagates and fails the test:
    a TypeError is not a refusal."""


def _import(folder, name):
    if folder not in sys.path:
        sys.path.insert(0, folder)
    return __import__(name)


def _sonin():
    return _import(KERNEL, "sonin")


def _ta():
    ta_ts = _import(TWO_ADIC, "ta_ts")
    ta_data = _import(TWO_ADIC, "ta_data")
    return ta_ts, ta_data


def T_inf(c, N: int, dps: int = 40):
    """kernel/: the S = {inf} trace term T_inf(c, N, dps)."""
    return _sonin().T_inf_matrix(c, N, dps)


def _call_builder(c, N, dps, local_data, arch_type="Gamma_R", s_inf=None):
    ta_ts, ta_data = _ta()
    try:
        return ta_ts.T_S_matrix(c, N, dps, local_data, arch_type=arch_type, s_inf=s_inf)
    except ta_data.NonUnitaryLocalData as e:
        raise Refused(f"NonUnitaryLocalData: {e}") from e
    except ta_ts.FrameworkLimit as e:
        raise NotExposed(f"FrameworkLimit: {e}") from e
    except ta_ts.KernelUnavailable as e:
        raise NotRouted(f"two_adic/ T_S_matrix: KernelUnavailable: {e}") from e


def T_S(c, N: int, dps: int = 40):
    """two_adic/: T_S for S = {inf, 2}, zeta's data (alpha = 1), Gamma_R."""
    _, ta_data = _ta()
    return _call_builder(c, N, dps, ta_data.ZETA)


def T_S_places(c, N: int, dps: int = 40, places=("inf", 2)):
    """two_adic/: places=("inf",) is the builder's local_data=None path.
    two_adic/'s own provider is unwired, so kernel/'s module is passed as the
    S_inf provider (the only thing that path consumes is T_inf_matrix)."""
    if tuple(places) == ("inf",):
        return _call_builder(c, N, dps, None, s_inf=_sonin())
    return T_S(c, N, dps)


# The data each control feeds the builder. Epstein's tower is the checker's
# own (checker_gate, exact), not two_adic's copy of numerics' tower.
def _local_data_for(obj: str):
    import checker_gate as CG

    _, ta_data = _ta()
    if obj == "zeta":
        return ta_data.ZETA, "Gamma_R"
    if obj == "W_a(a=1/4)":
        import sympy

        two = sympy.Integer(2)
        return ("satake", (two ** sympy.Rational(1, 4), two ** sympy.Rational(-1, 4))), "Gamma_R"
    if obj == "epstein_(1,1,6)":
        lam = CG.lambda_vectors(CG.coeffs_epstein_116())
        tower = {k: lam[2**k].get(2, 0) for k in range(1, 8)}
        return ("tower", tower, 2), "Gamma_R"
    if obj == "dedekind_Q(sqrt-23)":
        lam = CG.lambda_vectors(CG.coeffs_dedekind_m23())
        tower = {k: lam[2**k].get(2, 0) for k in range(1, 8)}
        return ("tower", tower, 2), "Gamma_C"
    raise KeyError(obj)


def T_S_with_data(c, N: int, dps: int, obj: str):
    """two_adic/: the builder fed the named object's data at 2 and its
    archimedean type (kill-controls 2 and 3). obj is a key of
    checker_gate.OBJECTS. Must raise Refused for W_a and Epstein (control 2)."""
    data, arch = _local_data_for(obj)
    return _call_builder(c, N, dps, data, arch_type=arch)


def validate_local(data, degree=None):
    """two_adic/'s validator alone (for the in-window-truncation lesion)."""
    _, ta_data = _ta()
    try:
        return ta_data.validate(data, degree=degree)
    except ta_data.NonUnitaryLocalData as e:
        raise Refused(f"NonUnitaryLocalData: {e}") from e
