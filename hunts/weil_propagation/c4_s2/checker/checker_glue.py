"""checker/: the seam to kernel/ and two_adic/.

Phase 1 (ebf0eae): nothing routed, every loader raised NotRouted.
Phase 2 (after the coordinator routed kernel/ af756a5 and two_adic/ c7e9f57):
only the call glue below changed; the properties in test_checker_props.py
did not.

Routed entry points (read-only use):
- kernel/sonin.py: T_inf_matrix(c, N, dps) = A + E (CC Thm 4.7).
- two_adic/ta_ts.py: T_S_matrix(c, N, dps, local_data, arch_type, s_inf);
  refuses non-unitary data (ta_data.NonUnitaryLocalData), refuses Gamma_C
  (FrameworkLimit). From ad97abf it builds T_S = T_inf + Delta_T as a float64
  array through ta_ts.KernelProvider(nvec, S) (Delta_T measured grade).

Phase 3: T_S is served from a snapshot keyed to the HEAD blobs of its
inputs, and refused while any input is dirty (see ts_key).

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


# two_adic/'s "converged rows" (its INTERFACE.md): (nvec, S) per N.
TS_SETTINGS = {8: (80, 1200), 16: (120, 1600), 32: (200, 2400)}
TS_SNAPSHOT = os.path.join(HERE, "checker_ts_snapshot.json")
C4S2 = "hunts/weil_propagation/c4_s2"


def _git(*args):
    """git at the repository root. check=True: a git error raises and is
    never read as "clean" (the fail-open lesson of scripts/check_secrets.py)."""
    import subprocess

    top = subprocess.run(["git", "rev-parse", "--show-toplevel"], cwd=HERE,
                         capture_output=True, text=True, check=True).stdout.strip()
    return subprocess.run(["git", *args], cwd=top, capture_output=True, text=True, check=True).stdout


def ts_input(path):
    """True for a file T_S imports or reads: a non-test .py under two_adic/
    or kernel/ (T_S imports ta_ts, ta_data, ta_prolate, ta_mellin, sonin and
    nothing else outside the venv), or a kernel/*.json (T_inf's moments).
    two_adic/'s RESULTS, INTERFACE and JSON outputs do not enter T_S."""
    rel = path.split(C4S2 + "/", 1)[-1]
    folder, _, name = rel.partition("/")
    base = os.path.basename(name)
    if folder not in ("two_adic", "kernel"):
        return False
    if base.endswith(".py"):
        return not (base.startswith("test_") or base == "conftest.py")
    return folder == "kernel" and base.endswith(".json")


def dirty_inputs(porcelain):
    """Lines of `git status --porcelain` output naming a tracked T_S input in
    any changed state (modified, staged, deleted, renamed). The snapshot key
    reads HEAD while the import reads the working tree, so any such line
    means the two can disagree. Untracked files are not inputs (the key and
    this check cover tracked files); an untracked module that T_S actually
    imports is caught by loaded_inputs_outside_key() after the build."""
    bad = []
    for line in porcelain.splitlines():
        if len(line) < 4 or line.startswith("??"):
            continue
        for p in line[3:].split(" -> "):
            if ts_input(p.strip().strip('"')):
                bad.append(line)
                break
    return bad


def _porcelain():
    return _git("status", "--porcelain", "--untracked-files=all", "--",
                f"{C4S2}/two_adic", f"{C4S2}/kernel")


def ts_key():
    """Digest of the HEAD blobs of every T_S input (ls-tree lines), plus the
    list of inputs dirty in the working tree. A snapshot is valid only for
    an equal digest and an empty dirty list."""
    import hashlib

    lines = _git("ls-tree", "-r", "HEAD", "--", f"{C4S2}/two_adic", f"{C4S2}/kernel").splitlines()
    ins = sorted(ln for ln in lines if ts_input(ln.split("\t", 1)[1]))
    if not ins:
        raise RuntimeError("no T_S inputs found at HEAD: refusing to key a snapshot on nothing")
    return hashlib.sha256("\n".join(ins).encode()).hexdigest(), dirty_inputs(_porcelain())


def loaded_inputs_outside_key(modules=None):
    """Modules loaded from two_adic/ or kernel/ that are not clean tracked
    T_S inputs at HEAD (for example an untracked helper a module imports).
    run_checker_ts.py refuses the unit if this is non-empty."""
    mods = sys.modules if modules is None else modules
    tracked = set(_git("ls-tree", "-r", "--name-only", "HEAD", "--",
                       f"{C4S2}/two_adic", f"{C4S2}/kernel").split())
    dirty = " ".join(dirty_inputs(_porcelain()))
    out = []
    for m in list(mods.values()):
        f = getattr(m, "__file__", None) or ""
        f = os.path.abspath(f)
        if not (f.startswith(TWO_ADIC + os.sep) or f.startswith(KERNEL + os.sep)):
            continue
        rel = C4S2 + "/" + os.path.relpath(f, os.path.join(HERE, "..")).replace(os.sep, "/")
        if rel not in tracked or not ts_input(rel) or rel in dirty:
            out.append(rel)
    return sorted(out)


class SnapshotUnavailable(NotRouted):
    """No valid snapshot row: absent, stale, or the T_S inputs are dirty.
    Fail closed: T_S() raises rather than build live from a working tree
    the snapshot key cannot see."""


def _snapshot_rows(c, N, dps, key=None):
    """Rows of the snapshot for (c, N, dps), or None. None whenever the
    working tree has a dirty T_S input, the digest differs, or the unit is
    absent. No dps fallback: a dps-60 request is served only by a dps-60
    unit."""
    import json

    digest, dirty = key if key is not None else ts_key()
    if dirty or not os.path.exists(TS_SNAPSHOT):
        return None
    with open(TS_SNAPSHOT) as fh:
        snap = json.load(fh)
    if snap["meta"].get("ts_inputs_digest") != digest:
        return None
    nv, S = TS_SETTINGS[int(N)]
    return snap["T_S"].get(f"{c}|{int(N)}|{int(dps)}|{nv}|{S}")


def T_S_live(c, N: int, dps: int = 40, nvec=None, S=None):
    """two_adic/: a live call (float64 numpy array), converged-row settings
    unless (nvec, S) are given. Used by run_checker_ts.py and by one test."""
    ta_ts, ta_data = _ta()
    nv, SS = TS_SETTINGS[int(N)]
    prov = ta_ts.KernelProvider(nvec or nv, S or SS)
    return _call_builder(c, N, dps, ta_data.ZETA, s_inf=prov)


def T_S(c, N: int, dps: int = 40):
    """two_adic/: T_S for S = {inf, 2}, zeta's data (alpha = 1), Gamma_R, as an
    mpmath matrix holding two_adic/'s float64 entries exactly. Served only
    from checker_ts_snapshot.json (run_checker_ts.py) while every T_S input
    is clean and matches the snapshot's digest; otherwise raises
    SnapshotUnavailable, never a live build."""
    from mpmath import mp

    digest, dirty = ts_key()
    if dirty:
        raise SnapshotUnavailable("T_S inputs dirty in the working tree: " + "; ".join(dirty))
    rows = _snapshot_rows(c, N, dps, key=(digest, dirty))
    if rows is None:
        raise SnapshotUnavailable(
            f"no snapshot unit for (c={c}, N={N}, dps={dps}) at T_S input digest {digest[:12]}. "
            "T_S is float64 (Delta_T measured grade): dps 60 is built at N = 8 only, where it "
            "measures the float64 floor; the banded pins are in test_checker_ts.py")
    n = len(rows)
    M = mp.matrix(n)
    for i in range(n):
        for j in range(n):
            M[i, j] = mp.mpf(float(rows[i][j]))
    return M


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
    ta_ts, _ = _ta()
    # explicit (nvec, S): the provider's default nvec at N = 32 is 364 modes (Kmax 15)
    prov = ta_ts.KernelProvider(*TS_SETTINGS[int(N)])
    return _call_builder(c, N, dps, data, arch_type=arch, s_inf=prov)


def validate_local(data, degree=None):
    """two_adic/'s validator alone (for the in-window-truncation lesion)."""
    _, ta_data = _ta()
    try:
        return ta_data.validate(data, degree=degree)
    except ta_data.NonUnitaryLocalData as e:
        raise Refused(f"NonUnitaryLocalData: {e}") from e
