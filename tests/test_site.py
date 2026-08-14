"""The presentation of this record is not built in this repository.

The generator, its build script, its own tests and the host config live in a
separate repository. This tree holds the record; the site that renders it is
built elsewhere, from a full clone of this one, so every figure it prints is
still derived from these artifacts at build time rather than typed in.

What is left here is the boundary. An abstraction with no consumer is a
liability, and so is a directory that quietly grows back: the site machinery
was removed once, and a later session adding a generator, a build script or a
host config to this tree would silently undo that without a test to say so.

Scope, stated so nobody reads more into a green run than it earns: this checks
that the presentation layer is absent from this repository. It says nothing
about whether the site builds, whether it is correct, or whether it agrees
with this tree. Those are checked where the generator lives.

Stdlib and pytest only, so it runs in the cheap tier.
"""

from __future__ import annotations

from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[1]

#: Paths that belonged to the presentation layer. Each is named rather than
#: matched by glob, because the point is to catch the specific thing coming
#: back, not to forbid every file that happens to look like a build.
MOVED = (
    Path("scripts") / "72_site.py",
    Path("scripts") / "build_site.sh",
    Path("vercel.json"),
)


@pytest.mark.parametrize("rel", MOVED, ids=lambda p: p.as_posix())
def test_the_presentation_layer_is_not_in_this_tree(rel: Path) -> None:
    assert not (REPO / rel).exists(), (
        f"{rel.as_posix()} is back in this repository. The site is built in "
        f"its own repository, from a full clone of this one. Putting the "
        f"generator here again puts the presentation of the record back into "
        f"the record."
    )
