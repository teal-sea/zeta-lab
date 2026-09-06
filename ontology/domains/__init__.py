"""ontology.domains, the only place in this package that knows its subject.

``ontology.schema``, ``funnel``, ``metrics`` and ``registry`` are
domain-agnostic; ``ontology.knownness`` knows general mathematics but not this
laboratory. Everything that names a quantity the laboratory computes lives here,
behind the registry interface.

Nothing is imported eagerly: a domain module is loaded by the code that wants it,
so importing ``discovery`` never drags in the science package.
"""

from __future__ import annotations

__all__: list[str] = []
