"""``telemetry.prompts``, recovering what an agent was actually asked.

A digest alone answers "did this change?" and not "what was it?". Both are
needed: without the text the record cannot be audited, and without the digest
the text cannot be shown to be the one that ran.

So a prompt is stored **content-addressed** at
``<root>/prompts/<sha256>.txt`` and the run record carries a reference. Two
consequences fall out of content addressing rather than being designed in: the
same prompt template used by forty runs is stored once, and tampering is
detectable by recomputation rather than by trust.

Where the text lives, and why it is not committed
-------------------------------------------------
``telemetry/.gitignore`` excludes the store, so prompt text stays local. This
repository is public and the operator already keeps strategy material off-tree
for a stated reason (``HANDOFF.md``: publishing a strategy document creates a
standing incentive to write the next one more flatteringly). Prompts routinely
carry that same material, plus private paths and third-party context.

The consequence is stated rather than hidden: **the digest is public and
durable, the text is local and mortal.** A clone of this repository can verify
that a prompt has not changed and cannot read it. If prompt text needs to
outlive one disk, it belongs in the operator's private store with
``store="external"`` and a reference recorded here, the same arrangement
``conjectures/`` already uses.

Nothing in this module writes outside ``<root>/prompts``.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from telemetry.registry import prompts_dir, utc_now

__all__ = [
    "PromptRef",
    "missing_locally",
    "STORES",
    "digest_text",
    "capture_text",
    "capture_file",
    "reference_external",
    "resolve",
    "verify_reasons",
]

#: Where the text actually is. ``absent`` is a real answer and is recorded as
#: one, a run whose prompt was never captured says so instead of omitting the
#: field, which would be indistinguishable from a capture bug.
STORES: tuple[str, ...] = ("local-private", "external", "absent")


@dataclass(frozen=True)
class PromptRef:
    """A durable reference to what an agent was asked."""

    digest: str | None
    store: str
    ref: str | None = None
    bytes: int | None = None
    source: str | None = None
    captured_at: str | None = None

    def as_dict(self) -> dict[str, Any]:
        return {
            "digest": self.digest,
            "store": self.store,
            "ref": self.ref,
            "bytes": self.bytes,
            "source": self.source,
            "captured_at": self.captured_at,
        }

    @classmethod
    def from_dict(cls, raw: Any) -> "PromptRef":
        if not isinstance(raw, dict):
            return cls(digest=None, store="absent")
        return cls(
            digest=raw.get("digest"),
            store=raw.get("store", "absent"),
            ref=raw.get("ref"),
            bytes=raw.get("bytes"),
            source=raw.get("source"),
            captured_at=raw.get("captured_at"),
        )


def digest_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def capture_text(root: Path | str, text: str, *, source: str | None = None) -> PromptRef:
    """Store prompt text in the local private store and return its reference.

    Writing is idempotent: the same text lands on the same path, and an
    existing file is left exactly as it is rather than rewritten, so a capture
    can never quietly change a prompt an earlier run already referenced.
    """
    digest = digest_text(text)
    directory = prompts_dir(root)
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / f"{digest}.txt"
    if not path.exists():
        path.write_text(text, encoding="utf-8")
    return PromptRef(
        digest=digest,
        store="local-private",
        ref=f"prompts/{digest}.txt",
        bytes=len(text.encode("utf-8")),
        source=source,
        captured_at=utc_now(),
    )


def capture_file(root: Path | str, path: Path | str, *, source: str | None = None) -> PromptRef:
    """Store the contents of a file as the run's prompt.

    ``source`` records the file's name, not its absolute path: run records are
    committed to a public repository and an absolute path leaks a home
    directory (``tests/test_repo_hygiene.py`` scans for that shape).
    """
    resolved = Path(path)
    text = resolved.read_text(encoding="utf-8")
    return capture_text(root, text, source=source or resolved.name)


def reference_external(digest: str, ref: str, *, source: str | None = None,
                       size: int | None = None) -> PromptRef:
    """Record a prompt held somewhere this package must not write.

    For material that may not enter even a gitignored directory inside a public
    checkout. The digest still travels, so the external copy can be checked
    against the record by whoever holds it.
    """
    return PromptRef(
        digest=digest,
        store="external",
        ref=ref,
        bytes=size,
        source=source,
        captured_at=utc_now(),
    )


def resolve(root: Path | str, ref: PromptRef) -> Path | None:
    """The local path holding this prompt's text, if this machine has it."""
    if ref.store != "local-private" or not ref.digest:
        return None
    path = prompts_dir(root) / f"{ref.digest}.txt"
    return path if path.exists() else None


def missing_locally(root: Path | str, ref: PromptRef) -> bool:
    """True when a local-private prompt's text is simply not on this machine.

    Not the same thing as a broken record, and the distinction is load-bearing.
    The store is gitignored by design, so **every fresh clone** is in this
    state: the digest travels, the text does not. Reporting that as a defect
    would make ``reconcile --strict`` fail on a clean checkout, and a guard
    that fires on correct behaviour is one nobody reads, which this
    repository has catalogued as a failure mode rather than tolerated.

    A *mismatching* digest is a different matter and stays a defect.
    """
    if ref.store != "local-private" or not ref.digest:
        return False
    return not (prompts_dir(root) / f"{ref.digest}.txt").exists()


def verify_reasons(root: Path | str, ref: PromptRef) -> tuple[str, ...]:
    """Every reason this prompt is not recoverable-and-intact, at once.

    An ``external`` or ``absent`` prompt is not a defect, it is a stated
    limitation, and it reports as one only when it lacks the fields that make
    it followable.
    """
    reasons: list[str] = []
    if ref.store not in STORES:
        reasons.append(f"store {ref.store!r} is not one of {list(STORES)}")
    if ref.store == "absent":
        if ref.digest is not None:
            reasons.append("store='absent' carries a digest; one of the two is wrong")
        return tuple(reasons)
    if not ref.digest:
        reasons.append(f"store={ref.store!r} without a digest, integrity uncheckable")
    if ref.store == "external":
        if not ref.ref:
            reasons.append("store='external' without a ref, the text is unfindable")
        return tuple(reasons)

    path = prompts_dir(root) / f"{ref.digest}.txt"
    if not path.exists():
        reasons.append(
            f"prompt {ref.digest[:12]}… is referenced but not present in this "
            f"machine's store; the text is unrecoverable here"
        )
        return tuple(reasons)
    actual = digest_text(path.read_text(encoding="utf-8"))
    if actual != ref.digest:
        reasons.append(
            f"prompt store content hashes to {actual[:12]}… but the run record "
            f"claims {ref.digest[:12]}…, the stored text is not the text that ran"
        )
    return tuple(reasons)
