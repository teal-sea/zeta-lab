#!/usr/bin/env python3
"""Regenerate the machine-readable knowledge index for this repository.

Why this exists
---------------
`AGENTS.md` carries *judgment*, house rules, traps, conventions we derived the
hard way.  This script carries *facts*, the public API surface, the document
index, the ground-truth constants, the current test count.  Facts go stale the
moment they are copied by hand, so they are extracted from the source instead:

    python scripts/make_context.py              # rewrite CONTEXT.md
    python scripts/make_context.py --flat       # also write CONTEXT_FLAT.md
    python scripts/make_context.py --check      # non-zero exit if CONTEXT.md is stale

`CONTEXT.md` is the file to hand a fresh agent (or paste into a context window)
when it needs to know what the lab already contains.  `--flat` additionally
concatenates every source and doc file into one pasteable blob, for the case
where the whole repository has to fit in a single prompt.

The parser uses `ast`, so nothing is imported and no numerics run: this is fast
and cannot be broken by a module that is mid-edit.
"""

from __future__ import annotations

import argparse
import ast
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PKG = ROOT / "zeta"
DISCOVERY = ROOT / "ontology"
HARNESS = ROOT / "harness"
DOSSIER = ROOT / "dossier"
DOCS = ROOT / "docs"
TESTS = ROOT / "tests"
SCRIPTS = ROOT / "scripts"
OUT = ROOT / "CONTEXT.md"
OUT_FLAT = ROOT / "CONTEXT_FLAT.md"

# Modules in reading order rather than alphabetical: the order tells a story.
MODULE_ORDER = [
    "core",
    "zeros",
    "explicit",
    "statistics",
    "moments",
    "heatflow",
    "weil",
    "epstein",
    "li",
    "finitefield",
    "criteria",
    "rigor",
    "inverse",
    "quasicrystal",
    "factorization",
    "detector",
    "leeyang",
    "relations",
    "synthesis",
    "plots",
]

# The discovery layer, in pipeline order. The first six are domain-agnostic and
# must stay that way; ``domains/`` is the only place the subject is named, and
# the split is enforced by the seam tests, see `ontology/README.md`.
DISCOVERY_ORDER = [
    "schema",
    "registry",
    "ledger",
    "funnel",
    "metrics",
    "knownness",
    "historical_cases",
]


def first_line(doc: str | None) -> str:
    """First sentence of a docstring, collapsed to one line."""
    if not doc:
        return ""
    line = doc.strip().split("\n", 1)[0].strip()
    return re.sub(r"\s+", " ", line)


def signature(node: ast.FunctionDef | ast.AsyncFunctionDef) -> str:
    """Render a def's signature without evaluating anything."""
    a = node.args
    parts: list[str] = []

    def render(arg: ast.arg, default: ast.expr | None) -> str:
        s = arg.arg
        if arg.annotation is not None:
            s += f": {ast.unparse(arg.annotation)}"
        if default is not None:
            s += f" = {ast.unparse(default)}"
        return s

    posonly = list(a.posonlyargs)
    args = list(a.args)
    defaults = list(a.defaults)
    positional = posonly + args
    pad = [None] * (len(positional) - len(defaults))
    for arg, default in zip(positional, pad + defaults):
        parts.append(render(arg, default))
        if posonly and arg is posonly[-1]:
            parts.append("/")
    if a.vararg is not None:
        parts.append("*" + a.vararg.arg)
    elif a.kwonlyargs:
        parts.append("*")
    for arg, default in zip(a.kwonlyargs, a.kw_defaults):
        parts.append(render(arg, default))
    if a.kwarg is not None:
        parts.append("**" + a.kwarg.arg)

    ret = f" -> {ast.unparse(node.returns)}" if node.returns is not None else ""
    return f"{node.name}({', '.join(parts)}){ret}"


def module_api(path: Path) -> dict:
    """Public API of one module: __all__ if present, else public top-level defs."""
    tree = ast.parse(path.read_text(encoding="utf-8"))
    declared: list[str] | None = None
    for node in tree.body:
        if isinstance(node, ast.Assign) and any(
            isinstance(t, ast.Name) and t.id == "__all__" for t in node.targets
        ):
            try:
                declared = [str(v) for v in ast.literal_eval(node.value)]
            except (ValueError, SyntaxError):
                declared = None

    functions: list[tuple[str, str]] = []
    classes: list[tuple[str, str]] = []
    constants: list[str] = []
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if node.name.startswith("_"):
                continue
            if declared is not None and node.name not in declared:
                continue
            functions.append((signature(node), first_line(ast.get_docstring(node))))
        elif isinstance(node, ast.ClassDef):
            if node.name.startswith("_"):
                continue
            if declared is not None and node.name not in declared:
                continue
            classes.append((node.name, first_line(ast.get_docstring(node))))
        elif isinstance(node, (ast.Assign, ast.AnnAssign)):
            targets = node.targets if isinstance(node, ast.Assign) else [node.target]
            for t in targets:
                if isinstance(t, ast.Name) and t.id.isupper() and not t.id.startswith("_"):
                    constants.append(t.id)

    return {
        "docstring": first_line(ast.get_docstring(tree)),
        "functions": functions,
        "classes": classes,
        "constants": constants,
        "lines": len(path.read_text(encoding="utf-8").splitlines()),
    }


def doc_index() -> list[tuple[str, str]]:
    """(filename, first heading or first non-empty line) for each doc, in order."""
    out = []
    for path in sorted(DOCS.glob("*.md")):
        title = ""
        for line in path.read_text(encoding="utf-8").splitlines():
            line = line.strip()
            if line.startswith("# "):
                title = line[2:].strip()
                break
            if line and not line.startswith("---"):
                title = line
                break
        out.append((path.name, title))
    return out


def shell_summary(text: str) -> str:
    """First line of a shell script's leading `#` comment block, minus the shebang."""
    for line in text.splitlines():
        if line.startswith("#!") or not line.strip():
            continue
        if line.startswith("#"):
            return first_line(line.lstrip("#").strip())
        break
    return ""


def script_index() -> list[tuple[str, str]]:
    out = []
    for path in sorted(SCRIPTS.glob("*.py")):
        try:
            tree = ast.parse(path.read_text(encoding="utf-8"))
            summary = first_line(ast.get_docstring(tree))
        except SyntaxError:
            summary = ""
        out.append((path.name, summary))
    # Shell helpers are listed too, a script an agent cannot see in the index
    # is a script that gets reinvented.
    for path in sorted(SCRIPTS.glob("*.sh")):
        out.append((path.name, shell_summary(path.read_text(encoding="utf-8"))))
    return out


def test_counts() -> list[tuple[str, int]]:
    """Number of test functions per test file (counted by ast, not by running)."""
    out = []
    for path in sorted(TESTS.glob("test_*.py")):
        try:
            tree = ast.parse(path.read_text(encoding="utf-8"))
        except SyntaxError:
            continue
        n = sum(
            1
            for node in ast.walk(tree)
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
            and node.name.startswith("test_")
        )
        out.append((path.name, n))
    return out


def build() -> str:
    lines: list[str] = []
    add = lines.append

    add("# CONTEXT.md, machine-readable index of this repository")
    add("")
    add("**Generated by `scripts/make_context.py`. Do not edit by hand, regenerate.**")
    add("")
    add(
        "This file carries *facts* extracted from the source: the public API, the "
        "document index, the script index, test counts. Judgment, house rules, "
        "naming traps, derived conventions, honest-scope policy, lives in "
        "[`AGENTS.md`](AGENTS.md) and is written by hand. Read both."
    )
    add("")

    # ---- orientation -------------------------------------------------
    add("## What this repository is")
    add("")
    add(
        "A computational laboratory for the Riemann zeta function: an instrument for "
        "building intuition and verified numerics about the Riemann Hypothesis. It is "
        "**not** a proof attempt, and nothing computed here is evidence for RH "
        "(`docs/08-why-it-is-hard.md`). The organising chain:"
    )
    add("")
    add("```")
    add("theta is the heat kernel on a circle")
    add("      -> Poisson summation gives theta(1/x) = sqrt(x) theta(x)")
    add("      -> the Mellin transform gives xi(s) = xi(1-s)")
    add("      -> whose mirror axis is Re(s) = 1/2")
    add("      -> the explicit formula rebuilds primes from the zeros")
    add("      -> the same heat flow applied to Xi gives de Bruijn-Newman Lambda,")
    add("         where RH <=> Lambda = 0 and Lambda >= 0 is a theorem")
    add("```")
    add("")

    # ---- API ---------------------------------------------------------
    add("## Package API (`zeta/`)")
    add("")
    seen = set()
    paths = []
    for name in MODULE_ORDER:
        p = PKG / f"{name}.py"
        if p.exists():
            paths.append(p)
            seen.add(p.name)
    for p in sorted(PKG.glob("*.py")):
        if p.name not in seen and p.name != "__init__.py":
            paths.append(p)

    for path in paths:
        api = module_api(path)
        add(f"### `zeta/{path.name}`, {api['docstring']}")
        add("")
        add(f"*{api['lines']} lines*")
        add("")
        if api["constants"]:
            add(f"Constants: {', '.join('`' + c + '`' for c in api['constants'])}")
            add("")
        for name, doc in api["classes"]:
            add(f"- `class {name}`, {doc}" if doc else f"- `class {name}`")
        for sig, doc in api["functions"]:
            add(f"- `{sig}`" + (f", {doc}" if doc else ""))
        add("")

    # ---- discovery layer ---------------------------------------------
    if DISCOVERY.exists():
        add("## Discovery layer API (`ontology/`), the conjecture factory")
        add("")
        add(
            "A domain-agnostic pipeline that generates candidate observations from the "
            "laboratory's computed objects, screens them, and **logs the whole funnel so "
            "the conversion rate per generator can be measured**. `schema`, `registry`, "
            "`ledger`, `funnel`, `metrics` and `historical_cases` name no quantity the "
            "laboratory computes and import nothing from `zeta`, the seam is enforced by "
            "tests. `knownness` is the documented one-step-less-strict module (it knows "
            "general mathematics, not this subject). Everything that names the subject "
            "lives in `ontology/domains/`. Design and honest limits: "
            "[`ontology/README.md`](ontology/README.md). Operator console: "
            "`scripts/13_discovery_run.py`. The ledger it writes (`conjectures/`) is "
            "**gitignored**: a private notebook of unreviewed leads, and nothing in it is "
            "evidence for anything. An empty `conjectures/` in a fresh clone is that rule "
            "working, not a fault, `scripts/ledger_sync.sh` shares one ledger across "
            "machines through a *separate private* repo, never this tree."
        )
        add("")
        seen_d = set()
        dpaths = []
        for name in DISCOVERY_ORDER:
            p = DISCOVERY / f"{name}.py"
            if p.exists():
                dpaths.append(p)
                seen_d.add(p.name)
        for p in sorted(DISCOVERY.glob("*.py")):
            if p.name not in seen_d and p.name != "__init__.py":
                dpaths.append(p)
        dpaths.extend(sorted((DISCOVERY / "domains").glob("*.py")))
        for path in dpaths:
            if path.name == "__init__.py":
                continue
            api = module_api(path)
            rel = path.relative_to(ROOT)
            add(f"### `{rel}`, {api['docstring']}")
            add("")
            add(f"*{api['lines']} lines*")
            add("")
            if api["constants"]:
                add(f"Constants: {', '.join('`' + c + '`' for c in api['constants'])}")
                add("")
            for name, doc in api["classes"]:
                add(f"- `class {name}`, {doc}" if doc else f"- `class {name}`")
            for sig, doc in api["functions"]:
                add(f"- `{sig}`" + (f", {doc}" if doc else ""))
            add("")

    # ---- harness -----------------------------------------------------
    if HARNESS.exists():
        add("## Falsification harness API (`harness/`), the referee")
        add("")
        add(
            "The falsification protocol with the subject factored out. Four instrument "
            "roles, rivals (share the structure, lack the property), decoys (ablation), "
            "surrogates (null control) and lesions (detector power), bundled into a "
            "`Battery`; a `Department` is a battery plus a door plus reference claims "
            "whose verdicts are known. The admission rule is **no department without a "
            "battery**: one with no rival, with neither decoy nor surrogate, or with no "
            "lesion is refused, because it could never fail. `protocol.py` is "
            "domain-agnostic under the same three seam tests as `ontology/schema.py`; "
            "the subject lives only in `harness/departments/`. "
            "`tests/test_department_conformance.py` is parametrized over the registered "
            "departments, so adding one adds its audit. Design: "
            "[`harness/README.md`](harness/README.md)."
        )
        add("")
        hpaths = [HARNESS / "protocol.py"]
        hpaths.extend(
            p for p in sorted(HARNESS.glob("*.py"))
            if p.name not in {"__init__.py", "protocol.py"}
        )
        hpaths.extend(sorted((HARNESS / "departments").glob("*.py")))
        for path in hpaths:
            if path.name == "__init__.py" or not path.exists():
                continue
            api = module_api(path)
            rel = path.relative_to(ROOT)
            add(f"### `{rel}`, {api['docstring']}")
            add("")
            add(f"*{api['lines']} lines*")
            add("")
            if api["constants"]:
                add(f"Constants: {', '.join('`' + c + '`' for c in api['constants'])}")
                add("")
            for name, doc in api["classes"]:
                add(f"- `class {name}`, {doc}" if doc else f"- `class {name}`")
            for sig, doc in api["functions"]:
                add(f"- `{sig}`" + (f", {doc}" if doc else ""))
            add("")

    # ---- dossier (probe) ---------------------------------------------
    if DOSSIER.exists():
        add("## Research dossiers API (`dossier/`), **a probe, not a department**")
        add("")
        add(
            "An experiment in representing mathematical research state, intent, "
            "definitions, provenance, evidence, failed attempts, proof obligations and "
            "verification status, so that an agent can resume rigorous work. One "
            "schema, one worked example, one CLI (`scripts/50_dossier.py`). Two ideas "
            "are under test: **intent is data** (what an object is *for*, stated before "
            "any formula, plus what it is most likely to be confused with), and "
            "**\"verified\" is four independent things** (numeric agreement, enclosure "
            "arithmetic, the published record, a proof kernel) which `status.py` "
            "refuses to collapse, `Support.__bool__` raises rather than let a caller "
            "write `if support:`. Registered in no department and given no door, "
            "because a dossier has no rivals of its own: see "
            "[`docs/19-research-dossiers.md`](docs/19-research-dossiers.md) SS6. "
            "Design: [`dossier/README.md`](dossier/README.md)."
        )
        add("")
        dpaths = [DOSSIER / "status.py", DOSSIER / "schema.py", DOSSIER / "report.py"]
        dpaths.extend(sorted((DOSSIER / "subjects").glob("*.py")))
        for path in dpaths:
            if path.name == "__init__.py" or not path.exists():
                continue
            api = module_api(path)
            rel = path.relative_to(ROOT)
            add(f"### `{rel}`, {api['docstring']}")
            add("")
            add(f"*{api['lines']} lines*")
            add("")
            if api["constants"]:
                add(f"Constants: {', '.join('`' + c + '`' for c in api['constants'])}")
                add("")
            for name, doc in api["classes"]:
                add(f"- `class {name}`, {doc}" if doc else f"- `class {name}`")
            for sig, doc in api["functions"]:
                add(f"- `{sig}`" + (f", {doc}" if doc else ""))
            add("")

    # ---- docs --------------------------------------------------------
    add("## Documents (`docs/`)")
    add("")
    for name, title in doc_index():
        add(f"- `{name}`, {title}")
    add("")

    # ---- scripts -----------------------------------------------------
    add("## Runnable demos (`scripts/`)")
    add("")
    for name, summary in script_index():
        add(f"- `scripts/{name}`" + (f", {summary}" if summary else ""))
    add("")

    # ---- tests -------------------------------------------------------
    add("## Tests (`tests/`)")
    add("")
    counts = test_counts()
    total = sum(n for _, n in counts)
    add(f"{total} test functions across {len(counts)} files "
        f"(the collected count differs where tests are parametrised):")
    add("")
    for name, n in counts:
        add(f"- `tests/{name}`, {n}")
    add("")
    add("```bash")
    add(".venv/bin/python -m pytest -q -m 'not slow'   # fast tier")
    add(".venv/bin/python -m pytest -q                 # everything")
    add("```")
    add("")

    # ---- ground truth ------------------------------------------------
    add("## Ground truth for quick assertions")
    add("")
    add("| quantity | value |")
    add("| --- | --- |")
    add("| ζ(2) | π²/6 = 1.6449340668482264… |")
    add("| ζ(0), ζ(−1) | −1/2, −1/12 |")
    add("| γ₁, γ₂, γ₃ | 14.134725141734694, 21.022039638771555, 25.010857580145689 |")
    add("| N(100) | 29 zeros with 0 < γ < 100 |")
    add("| Ξ(0) | 0.4971207781… |")
    add("| λ₁ (Li) | 1 + γ/2 − log(4π)/2 = 0.0230957089661… |")
    add("| Λ (de Bruijn–Newman) | 0 ≤ Λ < 0.2; RH ⟺ Λ = 0 |")
    add("| θ(1/x) − √x·θ(x), ξ(s) − ξ(1−s) | 0 to working precision (~1e−30 at dps 30) |")
    add("")
    add(
        "Identities are exposed as measured *defect* functions rather than assumed; "
        "mpmath's `zetazero` / `siegelz` / `grampoint` / `nzeros` and Arb are used as "
        "independent oracles against the hand-rolled machinery."
    )
    add("")
    return "\n".join(lines) + "\n"


def build_flat() -> str:
    """Concatenate every source and doc file into one pasteable blob."""
    parts = ["# CONTEXT_FLAT.md, full repository dump (generated)\n"]
    groups = [
        ("Operating context", [ROOT / "AGENTS.md", ROOT / "README.md"]),
        ("Package", sorted(PKG.glob("*.py"))),
        (
            "Discovery layer",
            [DISCOVERY / "README.md", *sorted(DISCOVERY.glob("*.py")),
             *sorted((DISCOVERY / "domains").glob("*.py"))],
        ),
        (
            "Harness",
            [HARNESS / "README.md", *sorted(HARNESS.glob("*.py")),
             *sorted((HARNESS / "departments").glob("*.py"))],
        ),
        (
            "Dossiers (probe)",
            [DOSSIER / "README.md", *sorted(DOSSIER.glob("*.py")),
             *sorted((DOSSIER / "subjects").glob("*.py"))],
        ),
        ("Scripts", sorted(SCRIPTS.glob("*.py")) + sorted(SCRIPTS.glob("*.sh"))),
        ("Docs", sorted(DOCS.glob("*.md"))),
        ("Tests", sorted(TESTS.glob("*.py"))),
    ]
    for heading, paths in groups:
        parts.append(f"\n\n{'=' * 70}\n## {heading}\n{'=' * 70}\n")
        for path in paths:
            if not path.exists():
                continue
            rel = path.relative_to(ROOT)
            parts.append(f"\n\n--- {rel} ---\n\n")
            parts.append(path.read_text(encoding="utf-8"))
    return "".join(parts)


def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument("--flat", action="store_true", help="also write CONTEXT_FLAT.md")
    ap.add_argument(
        "--check",
        action="store_true",
        help="exit non-zero if CONTEXT.md is out of date (for CI / pre-commit)",
    )
    args = ap.parse_args()

    text = build()

    if args.check:
        current = OUT.read_text(encoding="utf-8") if OUT.exists() else ""
        if current != text:
            print("CONTEXT.md is stale, run: python scripts/make_context.py")
            return 1
        print("CONTEXT.md is up to date.")
        return 0

    OUT.write_text(text, encoding="utf-8")
    print(f"wrote {OUT.relative_to(ROOT)} ({len(text.splitlines())} lines)")

    if args.flat:
        flat = build_flat()
        OUT_FLAT.write_text(flat, encoding="utf-8")
        kb = len(flat.encode("utf-8")) / 1024
        print(f"wrote {OUT_FLAT.relative_to(ROOT)} ({kb:.0f} KB)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
