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
  ``rs_theta``; ``zeta.statistics.riemann_siegel_theta``; and every module-level
  alias of one of these in a loaded pure-Python module;
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

Arb's routines need their own kind of trap (corrected 2026-10-31). python-flint's
``acb`` and ``arb`` are static extension types: ``setattr(flint.acb, "zeta_zero",
...)`` raises TypeError in every release from 0.5.0 to 0.9.0. The version of
this module committed on 2026-10-26 did exactly that, outside its try/finally,
so it never installed the Arb traps and left the traps set before it in place
(``CHALLENGE_circularity.md``, correction of 2026-10-31). The trap now replaces
the type, not its attribute: a ``TrappedFlintType`` stand-in is bound at every
module-level name that holds ``flint.acb`` or ``flint.arb`` in a loaded
pure-Python module, among them ``spo_common``'s ``from flint import acb`` and
``flint.acb`` on the package (so a module first imported during the run binds
the stand-in too). Objects the stand-in builds are of a subclass of the real
type whose zero routines are traps, so ``arb(T).zeta_nzeros()`` is caught.
Objects flint returns from arithmetic are of the real type, so a call through
one of them (``(x + y).zeta_zero(1)``) is not seen; ``zero_routine_mentions``
checks that no module on the definition path names those routines at all.
``planted_arb_control`` is the planted fault that must be caught. Installation
is exception-safe: a failure while installing removes every trap already set.
"""
from __future__ import annotations

import ast
import builtins
import io
import os
import re
import sys
import tempfile
import types
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

with mp.workdps(40):  # built at 40 digits: at mpmath's default 53 bits it keeps only 16
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


#: Arb's zero routines, by the python-flint type that carries them
ARB_ZERO_ROUTINES = (("acb", ("zeta_zero", "zeta_zeros")), ("arb", ("zeta_nzeros",)))


class TrappedFlintType:
    """Stands in for an immutable python-flint type while the traps are set.

    Calling it builds an instance of a subclass of the real type whose zero
    routines are traps (so ``arb(T).zeta_nzeros()``, the only way that routine
    is called, is caught); the value is the real type's. ``isinstance`` and
    ``issubclass`` answer as for the real type, and every other attribute is
    the real type's. Objects that flint itself returns (sums, products, matrix
    entries) are of the real type and are not trapped.
    """

    def __init__(self, real, routines: dict):
        self._real = real
        self._routines = routines
        self._made = type(real.__name__, (real,), dict(routines))

    def __call__(self, *a, **k):
        return self._made(*a, **k)

    def __getattr__(self, name):
        d = object.__getattribute__(self, "__dict__")
        if "_real" not in d:
            raise AttributeError(name)
        if name in d["_routines"]:
            return d["_routines"][name]
        return getattr(d["_real"], name)

    def __instancecheck__(self, obj):
        return isinstance(obj, self._real)

    def __subclasscheck__(self, cls):
        return issubclass(cls, self._real)

    def __repr__(self):
        return "TrappedFlintType(%s)" % self._real.__name__


def _python_modules() -> list:
    """Loaded modules whose source is a .py file (extension modules are left alone)."""
    out = []
    for mod in list(sys.modules.values()):
        if not isinstance(mod, types.ModuleType):
            continue
        try:
            f = getattr(mod, "__file__", None) or ""
        except Exception:
            continue
        if isinstance(f, str) and f.endswith(".py"):
            out.append(mod)
    return out


def module_bindings(targets: dict) -> list:
    """(module, name, key) for each module-level name, in a loaded pure-Python
    module, bound to one of ``targets`` (a dict keyed by ``id`` of the object)."""
    out = []
    for mod in _python_modules():
        for name, v in list(vars(mod).items()):
            if id(v) in targets:
                out.append((mod, name, id(v)))
    return out


@contextmanager
def traps(extra=()):
    """Set every trap; remove them all on exit, or on any failure while setting them."""
    log: list = []
    saved: list = []
    installed: list = []  # labels of the zero routines trapped
    rebound: list = []  # "module.name" for each module-level alias replaced
    replace: dict = {}  # id(real object) -> (real object, its replacement)
    opened: list = []
    poisoned: list = []

    def patch(obj, name, value):
        old = getattr(obj, name)
        setattr(obj, name, value)
        saved.append((obj, name, old))

    def trap(label):
        def f(*a, **k):
            log.append(("call", label))
            raise RuntimeError("zero source called: " + label)
        return f

    real_open, real_np_load = builtins.open, np.load

    def logged_open(file, *a, **k):
        opened.append(str(file))
        return real_open(file, *a, **k)

    def logged_np_load(file, *a, **k):
        opened.append(str(file))
        return real_np_load(file, *a, **k)

    try:
        import importlib

        import flint
        import mpmath

        owned = []
        for name in ("zetazero", "siegelz", "siegeltheta", "grampoint", "nzeros"):
            owned.append((mp, name, "mpmath." + name))
            owned.append((mpmath, name, "mpmath module " + name))
        for name in dir(ZZ):
            if not name.startswith("_") and callable(getattr(ZZ, name)) and getattr(getattr(ZZ, name), "__module__", "") == ZZ.__name__:
                owned.append((ZZ, name, "zeta.zeros." + name))
        owned += [(ZC, "xi", "zeta.core.xi"), (ZC, "rs_theta", "zeta.core.rs_theta"),
                  (ZS, "riemann_siegel_theta", "zeta.statistics.riemann_siegel_theta")]
        for owner, name, label in owned:
            real = getattr(owner, name)
            t = trap(label)
            replace.setdefault(id(real), (real, t))
            patch(owner, name, t)
            installed.append(label)
        # Arb: the types are immutable, so the type itself is replaced wherever it is named
        for tname, routines in ARB_ZERO_ROUTINES:
            real = getattr(flint, tname)
            labels = {r: "flint.%s.%s" % (tname, r) for r in routines if hasattr(real, r)}
            stand_in = TrappedFlintType(real, {r: trap(lab) for r, lab in labels.items()})
            replace[id(real)] = (real, stand_in)
            installed += list(labels.values())
        for mod, name, key in module_bindings(replace):
            patch(mod, name, replace[key][1])
            rebound.append(mod.__name__ + "." + name)
        for mod in (WP, EN):
            for name in list(vars(mod)):
                v = getattr(mod, name)
                if name.isupper() and _CONST.search(name) and isinstance(v, (str, int, float)):
                    patch(mod, name, Poison(mod.__name__ + "." + name, log))
                    poisoned.append(mod.__name__ + "." + name)
        for modname, name in extra:
            mod = importlib.import_module(modname)
            if mod.__name__ + "." + name not in poisoned:
                patch(mod, name, Poison(mod.__name__ + "." + name, log))
                poisoned.append(mod.__name__ + "." + name)
        patch(builtins, "open", logged_open)
        patch(io, "open", logged_open)
        patch(np, "load", logged_np_load)
        yield {"log": log, "opened": opened, "poisoned": poisoned,
               "installed": installed, "rebound": rebound}
    finally:
        for obj, name, value in reversed(saved):
            setattr(obj, name, value)
        # a module first imported while the traps were set may hold a stand-in or a trap
        back = {id(new): real for real, new in replace.values()}
        for mod, name, key in module_bindings(back):
            setattr(mod, name, back[key])


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
            "poisoned": t["poisoned"], "installed": t["installed"],
            "rebound": t["rebound"], "cell": cell}


def planted_control() -> list:
    """Under the same traps, the comparison routine must be caught."""
    with traps() as t:
        path = os.path.join(tempfile.mkdtemp(), "none.json")
        try:
            S.zeta_ordinates(3, path=path)
        except RuntimeError:
            pass
    return t["log"]


_PLANTED_ARB_FAULT = '''\
"""Planted fault for the Arb traps: binds python-flint's types at import, as
spo_common does, and calls Arb's zero routines through them."""
import flint
from flint import acb, arb


def by_bound_name():
    return acb.zeta_zero(1)


def by_package():
    return flint.acb.zeta_zeros(1, 2)


def by_count():
    return arb(15).zeta_nzeros()


def by_instance():
    return acb(1).zeta_zero(1)
'''


def _load_scratch(name: str, source: str):
    """Import ``source`` as module ``name`` from a fresh temporary directory."""
    import importlib.util

    path = Path(tempfile.mkdtemp()) / (name + ".py")
    path.write_text(source, encoding="utf-8")
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


def planted_arb_control() -> dict:
    """Functions that really call Arb's zero routines, run under the traps.

    One scratch module is imported before the traps are set (as ``spo_common``
    is), one while they are set (as a lazily imported helper would be), and the
    names the definition path itself binds (``spo_common.acb``,
    ``enclosures.arb``) are called through directly. Returns the trap log, the
    calls that returned instead of being stopped (must be empty), and whether
    every binding is the real flint type again afterwards."""
    import flint

    names = ("planted_arb_fault_early", "planted_arb_fault_late")
    early = _load_scratch(names[0], _PLANTED_ARB_FAULT)
    calls = {
        "early: acb.zeta_zero": early.by_bound_name,
        "early: flint.acb.zeta_zeros": early.by_package,
        "early: arb.zeta_nzeros": early.by_count,
        "early: acb(1).zeta_zero": early.by_instance,
        "spo_common.acb.zeta_zero": lambda: S.acb.zeta_zero(1),
        "enclosures.arb.zeta_nzeros": lambda: EN.arb(15).zeta_nzeros(),
    }
    escaped = []
    try:
        with traps() as t:
            late = _load_scratch(names[1], _PLANTED_ARB_FAULT)
            calls["late: acb.zeta_zero"] = late.by_bound_name
            for label, fn in calls.items():
                try:
                    fn()
                    escaped.append(label)
                except RuntimeError:
                    pass
        restored = all(m.acb is flint.acb and m.arb is flint.arb for m in (early, late, S, EN, WP))
    finally:
        for name in names:
            sys.modules.pop(name, None)
    return {"log": t["log"], "escaped": escaped, "restored": restored, "installed": t["installed"]}


_ZERO_ROUTINE_NAME = re.compile(r"\bzeta_n?zeros?\b")


def zero_routine_mentions(files=None) -> list:
    """(module, line) for each mention of an Arb zero-routine name in the source
    of the path modules. The traps cannot see a call made through an ``acb`` or
    ``arb`` instance (``z.zeta_zero(1)``); such a call names the routine in the
    source, unless the name is built at run time."""
    hits = []
    for name, f in (files or path_modules()):
        for lineno, line in enumerate(Path(f).read_text(encoding="utf-8").splitlines(), 1):
            if _ZERO_ROUTINE_NAME.search(line):
                hits.append((name, lineno))
    return hits


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
        print("   zero routines trapped:", r["installed"])
        print("   aliases rebound:", r["rebound"])
        spec = spectrum_mpmath(r["cell"])
        with mp.workdps(60):
            im = max(abs(mp.im(z)) for z in spec)
            pos = sorted(mp.re(z) for z in spec if mp.re(z) > 1)
            print("   mpmath eig: max |Im| = %s, lowest positive eigenvalues %s" % (mp.nstr(im, 5), [mp.nstr(x, 15) for x in pos[:3]]))
            if kind == "zeta":
                print("   first eigenvalue minus gamma_1 (60 digits):", mp.nstr(pos[0] - GAMMA_1, 5))
    print("planted control (comparison routine under traps):", planted_control())
    arb_ctl = planted_arb_control()
    print("planted Arb control: log", arb_ctl["log"], "| escaped", arb_ctl["escaped"], "| restored", arb_ctl["restored"])
    print("Arb zero-routine names in the path modules' source:", zero_routine_mentions())
    hits, names = scan_once()
    print("modules on the path:", [n for n, _ in path_modules()])
    for h in hits:
        print("   literal near a zero:", h, hit_kind(h[0], h[1]))
    print("module-level names poisoned from the scan:", names)
    return 0


if __name__ == "__main__":
    sys.exit(main())
