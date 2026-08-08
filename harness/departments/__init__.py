"""``harness.departments`` — the subject-coupled side of the seam.

Everything under this package is allowed to know what is being studied, and
is the *only* part of :mod:`harness` allowed to. A department module imports
its laboratory freely, builds the four instrument roles out of whatever that
laboratory already has, and registers a
:class:`~harness.protocol.Department` at import time.

Importing this package does **not** import any department: a department drags
in its laboratory's dependencies, and the protocol must stay testable without
them. Ask for one by name.
"""

from __future__ import annotations

import importlib
from types import ModuleType

#: Department name -> module that registers it. Add a line when you add a
#: department; ``tests/test_department_conformance.py`` audits every entry.
KNOWN_DEPARTMENTS: dict[str, str] = {
    "zeta": "harness.departments.zeta_department",
    "finitefield": "harness.departments.finitefield_department",
    "compiler": "harness.departments.compiler_department",
}

__all__ = ["KNOWN_DEPARTMENTS", "load", "load_all"]


def load(name: str) -> ModuleType:
    """Import the module that registers department ``name`` and return it."""
    try:
        module_name = KNOWN_DEPARTMENTS[name]
    except KeyError:
        known = ", ".join(sorted(KNOWN_DEPARTMENTS)) or "(none)"
        raise KeyError(f"no department module for {name!r}; known: {known}") from None
    return importlib.import_module(module_name)


def load_all() -> tuple[str, ...]:
    """Import every known department module. Returns the names loaded."""
    for name in KNOWN_DEPARTMENTS:
        load(name)
    return tuple(sorted(KNOWN_DEPARTMENTS))
