"""Circularity challenger's check for spectral_operator (hunt #150).

The builder's provenance test scans source text: the six DEFINITION functions,
the ``BallTruncation`` class and two ``ccm_common`` helpers. A text scan does
not see module-level helpers those call, module constants they read (for
instance ``wp_common.GAMMA_OFF``, DH's off-line ordinate), or files they open.
This module checks provenance at run time instead:

* every zero source the tree offers is replaced by a trap that records the
  call: mpmath's ``zetazero``, ``siegelz``, ``siegeltheta``, ``grampoint``,
  ``nzeros`` (on ``mp`` and on the module); Arb's ``zeta_zero``, ``zeta_zeros``
  and ``zeta_nzeros``; every public function of ``zeta.zeros``; ``zeta.core.xi`` and
  ``rs_theta``; ``zeta.statistics.riemann_siegel_theta``;
* every module-level constant of ``wp_common`` and ``enclosures`` whose name
  mentions a zero, an ordinate or an offset is replaced by a poisoned value
  that records any arithmetic, comparison or conversion on it;
* every file opened (``builtins.open``, ``io.open``, ``numpy.load``) is logged;

then the operator is built through the builder's definition functions, for
zeta and DH. A planted control calls the comparison routine
``zeta_ordinates`` under the same traps and must be caught.

It also recomputes the spectrum of D' with mpmath's eigensolver, a route the
builder does not use (they use ``acb_mat.eig`` and the secular equation).
Writes nothing into the tree.
"""
from __future__ import annotations

import ast
import builtins
import io
import os
import re
import sys
import tempfile
from contextlib import contextmanager
from pathlib import Path

import numpy as np
from mpmath import mp

HERE = Path(__file__).resolve().parent
MECH = HERE.parent
ROOT = HERE.parents[3]
for _p in (str(MECH), str(ROOT)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import spo_common as S  # noqa: E402  (puts weil_trunc, wp numerics, ccm on sys.path)
import enclosures as EN  # noqa: E402
import wp_common as WP  # noqa: E402
import ccm_common  # noqa: E402,F401  (imported lazily by spo_common.ground; loaded here so the scan sees it)
import zeta.core as ZC  # noqa: E402
import zeta.statistics as ZS  # noqa: E402
import zeta.zeros as ZZ  # noqa: E402

GAMMA_1 = mp.mpf("14.134725141734693790457251983562")
_CONST = re.compile(r"(ZERO|GAMMA|DELTA|RHO|ORDINATE|OFF)", re.I)


class Poison:
    """A value that records any use of itself and then raises."""

    def __init__(self, name, log):
        self._name, self._log = name, log

    def _hit(self, *a, **k):
        self._log.append(("const", self._name))
        raise RuntimeError("poisoned constant read: " + self._name)

    __add__ = __radd__ = __sub__ = __rsub__ = __mul__ = __rmul__ = _hit
    __truediv__ = __rtruediv__ = __pow__ = __float__ = __int__ = __str__ = _hit
    __lt__ = __le__ = __gt__ = __ge__ = __neg__ = __abs__ = __index__ = _hit

    def __repr__(self):
        return "Poison(%s)" % self._name


@contextmanager
def traps(extra=()):
    log: list = []
    saved: list = []

    def patch(obj, name, value):
        saved.append((obj, name, getattr(obj, name)))
        setattr(obj, name, value)

    def trap(label):
        def f(*a, **k):
            log.append(("call", label))
            raise RuntimeError("zero source called: " + label)
        return f

    import mpmath

    for name in ("zetazero", "siegelz", "siegeltheta", "grampoint", "nzeros"):
        patch(mp, name, trap("mpmath." + name))
        patch(mpmath, name, trap("mpmath module " + name))
    for name in dir(ZZ):
        if not name.startswith("_") and callable(getattr(ZZ, name)) and getattr(getattr(ZZ, name), "__module__", "") == ZZ.__name__:
            patch(ZZ, name, trap("zeta.zeros." + name))
    import flint

    for cls in (flint.acb, flint.arb):
        for name in dir(cls):
            if name in ("zeta_zero", "zeta_zeros", "zeta_nzeros"):
                patch(cls, name, trap("flint.%s.%s" % (cls.__name__, name)))
    patch(ZC, "xi", trap("zeta.core.xi"))
    patch(ZC, "rs_theta", trap("zeta.core.rs_theta"))
    patch(ZS, "riemann_siegel_theta", trap("zeta.statistics.riemann_siegel_theta"))
    poisoned = []
    for mod in (WP, EN):
        for name in list(vars(mod)):
            v = getattr(mod, name)
            if name.isupper() and _CONST.search(name) and isinstance(v, (str, int, float)):
                patch(mod, name, Poison(mod.__name__ + "." + name, log))
                poisoned.append(mod.__name__ + "." + name)
    import importlib

    for modname, name in extra:
        mod = importlib.import_module(modname)
        if mod.__name__ + "." + name not in poisoned:
            patch(mod, name, Poison(mod.__name__ + "." + name, log))
            poisoned.append(mod.__name__ + "." + name)
    opened: list = []
    real_open, real_io_open, real_np_load = builtins.open, io.open, np.load

    def logged_open(file, *a, **k):
        opened.append(str(file))
        return real_open(file, *a, **k)

    def logged_np_load(file, *a, **k):
        opened.append(str(file))
        return real_np_load(file, *a, **k)

    builtins.open = logged_open
    io.open = logged_open
    np.load = logged_np_load
    try:
        yield {"log": log, "opened": opened, "poisoned": poisoned}
    finally:
        builtins.open, io.open, np.load = real_open, real_io_open, real_np_load
        for obj, name, value in reversed(saved):
            setattr(obj, name, value)


def build(kind: str, c, N: int) -> dict:
    """The builder's definition path, end to end, for one cell."""
    prec = S.prec_for(kind, c, N)
    bt, Te, To = S.sectors(kind, c, N, prec)
    rq, v = S.ground(Te)
    digits = int(prec / 3.32)
    with mp.workdps(digits):
        xi = S.xi_full(v)
        Dp = S.operator(xi)
        eps = mp.mpf(rq.mid().str(digits, radius=False))
    return {"prec": prec, "bt": bt, "xi": xi, "Dp": Dp, "eps": eps, "L": mp.log(c), "digits": digits}


def _module_file(modname: str) -> str:
    for name, f in path_modules():
        if name == modname:
            return f
    return sys.modules[modname].__file__


def assigned_names(hits) -> list:
    """(module, name) for every module-level assignment on a literal-hit line,
    including the names that alias such a constant (``X = WP.GAMMA_OFF``)."""
    out = set()
    for modname, lineno, _, _ in hits:
        tree = ast.parse(Path(_module_file(modname)).read_text(encoding="utf-8"))
        for node in tree.body:
            if isinstance(node, (ast.Assign, ast.AnnAssign)) and node.lineno <= lineno <= node.end_lineno:
                targets = node.targets if isinstance(node, ast.Assign) else [node.target]
                for t in targets:
                    if isinstance(t, ast.Name):
                        out.add((modname, t.id))
    # aliases: module-level names bound to an attribute of a poisoned constant
    for modname, f in path_modules():
        tree = ast.parse(Path(f).read_text(encoding="utf-8"))
        for node in tree.body:
            if isinstance(node, ast.Assign) and isinstance(node.value, ast.Attribute):
                if any(node.value.attr == n for _, n in list(out)):
                    for t in node.targets:
                        if isinstance(t, ast.Name):
                            out.add((modname, t.id))
    return sorted(out)


def hit_kind(modname: str, lineno: int) -> str:
    """'assignment', 'docstring' or 'comment' for a literal-scan hit."""
    import tokenize

    src = Path(_module_file(modname)).read_text(encoding="utf-8")
    tree = ast.parse(src)
    for node in tree.body:
        if isinstance(node, (ast.Assign, ast.AnnAssign)) and node.lineno <= lineno <= node.end_lineno:
            return "assignment"
    for node in ast.walk(tree):
        if (isinstance(node, ast.Expr) and isinstance(node.value, ast.Constant)
                and isinstance(node.value.value, str) and node.lineno <= lineno <= node.end_lineno):
            return "docstring"
    for tok in tokenize.generate_tokens(io.StringIO(src).readline):
        if tok.type == tokenize.COMMENT and tok.start[0] == lineno:
            return "comment"
    return "other"


_SCAN_CACHE: dict = {}


def scan_once() -> tuple:
    if "hits" not in _SCAN_CACHE:
        hits = literal_scan()
        _SCAN_CACHE["hits"] = hits
        _SCAN_CACHE["names"] = assigned_names(hits)
    return _SCAN_CACHE["hits"], _SCAN_CACHE["names"]


def provenance_report(kind: str, c=13, N: int = 16) -> dict:
    hits, names = scan_once()
    with traps(names) as t:
        cell = build(kind, c, N)
    zero_files = [f for f in t["opened"] if re.search(r"zero|gram|xi_cache|radical", os.path.basename(f), re.I)]
    return {"hits": t["log"], "opened": t["opened"], "zero_files": zero_files,
            "poisoned": t["poisoned"], "cell": cell}


def planted_control() -> list:
    """Under the same traps, the comparison routine must be caught."""
    with traps() as t:
        path = os.path.join(tempfile.mkdtemp(), "none.json")
        try:
            S.zeta_ordinates(3, path=path)
        except RuntimeError:
            pass
    return t["log"]


_DECIMAL = re.compile(r"(?<![\w.])-?\d+\.\d{4,}")


_PATH_MODULES: list = []


def path_modules() -> list:
    """Every module loaded from hunts/ or zeta/ when the definition path is imported
    and run (a (13, 8) cell for zeta and DH), listed from a fresh interpreter so that
    modules other code loaded do not enter."""
    if not _PATH_MODULES:
        import json
        import subprocess

        code = (
            "import sys, json; sys.path.insert(0, %r); sys.path.insert(0, %r)\n"
            "import spo_common as S, ccm_common\n"
            "for kind in ('zeta', 'dh'):\n"
            "    p = S.prec_for(kind, 13, 8); bt, Te, To = S.sectors(kind, 13, 8, p); rq, v = S.ground(Te)\n"
            "    S.operator(S.xi_full(v)); S.full_matrix(bt)\n"
            "print(json.dumps(sorted((n, getattr(m, '__file__', None) or '') for n, m in sys.modules.items())))"
        ) % (str(ROOT), str(MECH))
        res = subprocess.run([sys.executable, "-c", code], capture_output=True, text=True, check=True, cwd=str(ROOT))
        for name, f in json.loads(res.stdout.strip().splitlines()[-1]):
            if f.endswith(".py") and ("/hunts/" in f or "/zeta/" in f):
                _PATH_MODULES.append((name, f))
    return list(_PATH_MODULES)


def literal_scan(n_zeros: int = 200, rel: float = 1e-6, files=None) -> list:
    """Decimal literals (4+ places, code, strings or comments) in the path modules
    that sit within ``rel`` of a zeta ordinate gamma_k (k <= n_zeros), of
    gamma_k L / (2 pi) for L = log 13 and log 60 (the operator's s-variable), or of
    DH's and Epstein (1,1,6)'s off-line zeros. The zeros are computed here, by the
    challenger, outside any trap."""
    with mp.workdps(20):
        gam = [float(mp.im(mp.zetazero(k))) for k in range(1, n_zeros + 1)]
        targets = [("gamma_%d" % (k + 1), g) for k, g in enumerate(gam)]
        for c in (13, 60):
            sc = float(mp.log(c) / (2 * mp.pi))
            targets += [("gamma_%d*L/2pi (c=%d)" % (k + 1, c), g * sc) for k, g in enumerate(gam)]
    targets += [("DH Im", 85.69934848537759), ("DH Re", 0.80851718245663738), ("DH offset", 0.30851718245663738),
                ("Epstein Im 16.29", 16.2902157203904), ("Epstein Re 0.953", 0.953260474794661),
                ("Epstein Im 29.55", 29.5517610986291), ("Epstein Re 0.798", 0.7979971571787)]
    hits = []
    for name, f in (files or path_modules()):
        for lineno, line in enumerate(Path(f).read_text(encoding="utf-8").splitlines(), 1):
            for m in _DECIMAL.finditer(line):
                v = float(m.group())
                if abs(v) < 0.1:
                    continue
                for label, t in targets:
                    if abs(v - t) <= rel * abs(t):
                        hits.append((name, lineno, m.group(), label))
    return hits


def spectrum_mpmath(cell: dict, dps: int = 60) -> list:
    """Eigenvalues of D' by mpmath's eig, as z = 2 pi s / L."""
    with mp.workdps(dps):
        A = mp.matrix([[mp.mpf(x) for x in row] for row in cell["Dp"]])
        ev = mp.eig(A, left=False, right=False)
        fac = 2 * mp.pi / cell["L"]
        return sorted((mp.mpc(e) * fac for e in ev), key=lambda z: abs(mp.re(z)))


def main() -> int:
    for kind in ("zeta", "dh"):
        r = provenance_report(kind)
        print(kind, "trap hits:", r["hits"], "| files opened:", r["opened"], "| zero-like files:", r["zero_files"])
        print("   poisoned constants:", r["poisoned"])
        spec = spectrum_mpmath(r["cell"])
        im = max(abs(mp.im(z)) for z in spec)
        pos = sorted(mp.re(z) for z in spec if mp.re(z) > 1)
        print("   mpmath eig: max |Im| = %s, lowest positive eigenvalues %s" % (mp.nstr(im, 5), [mp.nstr(x, 15) for x in pos[:3]]))
        if kind == "zeta":
            print("   first eigenvalue minus gamma_1:", mp.nstr(pos[0] - GAMMA_1, 5))
    print("planted control (comparison routine under traps):", planted_control())
    hits, names = scan_once()
    print("modules on the path:", [n for n, _ in path_modules()])
    for h in hits:
        print("   literal near a zero:", h, hit_kind(h[0], h[1]))
    print("module-level names poisoned from the scan:", names)
    return 0


if __name__ == "__main__":
    sys.exit(main())
