"""``dossier.subjects``, the subject-coupled side of the dossier seam.

Modules here may import the laboratory freely. Importing this package does not
import any of them: the schema must stay testable without the laboratory's
dependencies, which is the whole point of the seam.
"""

from __future__ import annotations

import importlib
from types import ModuleType

#: Dossier name -> module that builds it.
KNOWN_DOSSIERS: dict[str, str] = {
    "hardy_Z": "dossier.subjects.hardy_z",
}

__all__ = ["KNOWN_DOSSIERS", "load", "build_all"]


def load(name: str) -> ModuleType:
    """Import the module that builds dossier ``name``."""
    try:
        module_name = KNOWN_DOSSIERS[name]
    except KeyError:
        known = ", ".join(sorted(KNOWN_DOSSIERS)) or "(none)"
        raise KeyError(f"no dossier module for {name!r}; known: {known}") from None
    return importlib.import_module(module_name)


def build_all() -> dict:
    """Build every known dossier. Returns ``{name: Dossier}``."""
    return {name: load(name).build() for name in KNOWN_DOSSIERS}
