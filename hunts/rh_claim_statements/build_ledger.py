"""Build claims.json from the curated ledger and the READ-ONLY archive.

Run isolated, from the repo root, with the archive and the Mathlib checkout
given as arguments (nothing is imported or executed from either tree):

    .venv/bin/python -I hunts/rh_claim_statements/build_ledger.py \
        --arch ARCH --mathlib MATHLIB --decl-index DECLS.txt --notation-scan NOTATION.txt

DECLS.txt and NOTATION.txt are the outputs of the two `rg` scans recorded in
RUNS.md (declarations in the archive whose name ends in an identifier used by a
claim; top-level notation, macro and elab declarations). Without them the
capture check is recorded as not run.

For each claim the script records: the verbatim statement (from the declaration
keyword to the first top-level `:=`), its sha256 and the file's sha256; the
namespace, `open`, `variable` and notation lines in force at that line; every
identifier of the statement, resolved to a Mathlib definition site (file and
line, looked up by a regex in the checkout), to Lean core, or to an
archive-local definition quoted in the ledger; and whether any archive
declaration could capture one of those identifiers. An identifier that is
neither bound in the statement nor resolved stops the build.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import runpy
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
OPEN, CLOSE = "([{⟨⦃", ")]}⟩⦄"


def strip_comments(text):
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and text.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth:
            if text[i] == "\n":
                out.append("\n")
            i += 1; continue
        if text.startswith("--", i):
            while i < n and text[i] != "\n":
                i += 1
            continue
        out.append(text[i]); i += 1
    return "".join(out)


def statement(lines, line):
    """From 1-based `line` to the first top-level ':=' that is not a `let` binder."""
    text = "\n".join(lines[line - 1:line - 1 + 400])
    depth, i, seg = 0, 0, 0
    while i < len(text):
        c = text[i]
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
        elif c == "\n" and depth == 0:
            seg = i + 1
        elif depth == 0 and text.startswith(":=", i):
            if text[seg:i].strip().startswith(("let ", "have ")):
                i += 2; continue
            return text[:i].rstrip()
        i += 1
    raise ValueError("statement does not close")


def context(lines, line):
    """Namespace stack, opens, variables and notation in force at `line` (text level)."""
    stack = [dict(kind="file", name="", opens=[], variables=[], notations=[], other=[])]
    imports, i = [], 0
    while i < line - 1:
        raw = lines[i]; s = raw.strip()
        if raw[:1] in (" ", "\t") or not s:
            i += 1; continue
        if s.startswith("import "):
            imports.append(s[7:].strip())
        elif s.startswith("namespace "):
            stack.append(dict(kind="namespace", name=s.split()[1], opens=[], variables=[], notations=[], other=[]))
        elif re.match(r"(noncomputable |public )*section\b", s):
            stack.append(dict(kind="section", name="", opens=[], variables=[], notations=[], other=[]))
        elif s == "end" or s.startswith("end "):
            if len(stack) > 1:
                stack.pop()
        elif s.startswith("open "):
            stack[-1]["opens"].append(f"{s}  [line {i + 1}]")
        elif s.startswith("variable"):
            blk = raw
            depth = sum(raw.count(c) for c in OPEN) - sum(raw.count(c) for c in CLOSE)
            j = i
            while depth > 0 and j + 1 < len(lines):
                j += 1; blk += "\n" + lines[j]
                depth += sum(lines[j].count(c) for c in OPEN) - sum(lines[j].count(c) for c in CLOSE)
            stack[-1]["variables"].append(f"{blk.strip()}  [line {i + 1}]")
            i = j
        elif re.match(r"(local |scoped )?(notation3?|infix[lr]?|prefix|postfix|macro|syntax|elab)\b", s):
            stack[-1]["notations"].append(f"{s}  [line {i + 1}]")
        elif s.startswith(("attribute [local", "local instance", "universe", "set_option autoImplicit")):
            stack[-1]["other"].append(f"{s}  [line {i + 1}]")
        i += 1
    pre, j = [], line - 2
    while j >= 0 and lines[j].strip().startswith(("open ", "set_option", "@[", "omit", "include")):
        pre.insert(0, lines[j].strip()); j -= 1
    return dict(imports=imports,
                namespace=".".join(e["name"] for e in stack if e["kind"] == "namespace"),
                opens=[o for e in stack for o in e["opens"]],
                variables=[v for e in stack for v in e["variables"]],
                notations=[v for e in stack for v in e["notations"]],
                local_overrides=[v for e in stack for v in e["other"] if not v.startswith("universe")],
                directly_above=pre)


# ---------------------------------------------------------------------------
# identifiers
# ---------------------------------------------------------------------------

TOKEN = re.compile(r"[^\W\d][\w'!?]*(?:\.(?:[^\W\d][\w'!?]*|\d+))*")
SIMPLE = re.compile(r"^[^\W\d][\w'!?]*$")
KEYWORDS = {"theorem", "lemma", "private", "protected", "nonrec", "fun", "let", "in", "Prop", "by", "_root_", "_"}
GLYPH_LETTERS = {"ℝ", "ℂ", "ℕ", "ℤ", "ℚ", "ᵥ", "ˣ", "¹", "𝓝"}


def _binder_names(group):
    """Names bound by a bracket group such as `(a b : T)`, `{x : T}`, `[inst : C x]` or `[C x]`."""
    inner = group[1:-1]
    depth = 0
    for k, ch in enumerate(inner):
        if ch in OPEN:
            depth += 1
        elif ch in CLOSE:
            depth -= 1
        elif ch == ":" and depth == 0 and not inner.startswith(":=", k):
            names = inner[:k].split()
            return names if names and all(SIMPLE.match(n) for n in names) else []
    return []


def _groups_from(text, start):
    """Consecutive top-level bracket groups from `start`; returns (groups, index after them)."""
    groups, i = [], start
    while True:
        while i < len(text) and text[i].isspace():
            i += 1
        if i >= len(text) or text[i] not in "({[⦃":
            return groups, i
        depth, j = 0, i
        while j < len(text):
            if text[j] in OPEN:
                depth += 1
            elif text[j] in CLOSE:
                depth -= 1
                if depth == 0:
                    break
            j += 1
        groups.append(text[i:j + 1]); i = j + 1


def bound_names(st, variables):
    names = set()
    m = re.match(r"\s*(?:private |protected |nonrec |noncomputable )*(?:theorem|lemma)\s+(\S+)", st)
    decl_name = m.group(1)
    groups, _ = _groups_from(st, m.end())
    for g in groups:
        names.update(_binder_names(g))
    for v in variables:
        body = re.sub(r"\s*\[line \d+\]$", "", v)[len("variable"):]
        gs, _ = _groups_from(body, 0)
        for g in gs:
            names.update(_binder_names(g))
    for q in re.finditer(r"(∀|∃|fun|λ|∑|∏|∫|let)\s*", st):
        gs, k = _groups_from(st, q.end())
        if gs:
            for g in gs:
                names.update(_binder_names(g))
            continue
        mm = re.match(r"((?:[^\W\d][\w']*\s+)*[^\W\d][\w']*)\s*(?:,|:|=>|∈)", st[q.end():])
        if mm:
            names.update(mm.group(1).split())
    for q in re.finditer(r"\{\s*([^\W\d][\w']*)\s*:[^{}]*?//", st):
        names.add(q.group(1))
    return names, decl_name


def identifiers(st, variables, resolve, extra_bound=()):
    bound, decl_name = bound_names(st, variables)
    bound |= set(extra_bound)
    found, unknown = {}, []
    for mt in TOKEN.finditer(st):
        tok = mt.group(0)
        if mt.start() >= 2 and st[mt.start() - 1] == "." and st[mt.start() - 2] in ")]⟩":
            continue                                      # method notation on a bracketed term, handled below
        if tok in KEYWORDS or tok in GLYPH_LETTERS or tok == decl_name or tok == decl_name.split(".")[-1]:
            continue
        if decl_name.startswith("_root_.") and tok in decl_name:
            continue
        if tok in resolve:
            found[tok] = resolve[tok]; continue
        parts = tok.split(".")
        split = next((k for k in range(len(parts) - 1, 0, -1)
                      if ".".join(parts[:k]) in resolve and "." + parts[-1] in resolve), None)
        if split is not None:                             # `Finset.univ.filter`: a resolved term, then a method
            found[".".join(parts[:split])] = resolve[".".join(parts[:split])]
            found["." + parts[-1]] = resolve["." + parts[-1]]
            continue
        head, _, tail = tok.partition(".")
        if tok in bound or (head in bound and not tail):
            continue
        if head in bound and tail:
            for comp in tail.split("."):
                if comp.isdigit():
                    continue                              # a projection .1 / .2 of a bound pair
                if "." + comp in resolve:
                    found["." + comp] = resolve["." + comp]
                else:
                    unknown.append(tok)
            continue
        unknown.append(tok)
    # method notation on a parenthesised term: `(p ^ n - 1).totient`
    for mm in re.finditer(r"\)\.([^\W\d][\w']*)", st):
        key = "." + mm.group(1)
        if key in resolve:
            found[key] = resolve[key]
        else:
            unknown.append(")" + key)
    return found, sorted(set(unknown)), sorted(bound)


def mathlib_site(root, file, regex, cache={}):
    key = (file, regex)
    if key not in cache:
        lines = (root / file).read_text(encoding="utf-8").split("\n")
        hit = next(((i + 1, l.strip()) for i, l in enumerate(lines) if re.search(regex, l)), None)
        if hit is None:
            raise SystemExit(f"no line matching {regex!r} in {file}")
        cache[key] = hit
    return cache[key]


# ---------------------------------------------------------------------------
# capture check from the rg declaration index
# ---------------------------------------------------------------------------

DECL = re.compile(r"\b(def|abbrev|structure|class|inductive|opaque|alias|irreducible_def|instance|theorem|lemma|axiom)\s+([^\s:({\[]+)")


def load_decl_index(path, arch):
    decls, files = [], {}
    for row in open(path, encoding="utf-8"):
        rel, line, text = row.rstrip("\n").split(":", 2)
        rel = rel[2:] if rel.startswith("./") else rel
        m = DECL.search(text)
        if not m:
            continue
        if rel not in files:
            files[rel] = strip_comments((arch / rel).read_text(encoding="utf-8")).split("\n")
        ns = context(files[rel], int(line))["namespace"]
        name = m.group(2)
        full = name[len("_root_."):] if name.startswith("_root_.") else (ns + "." + name if ns else name)
        decls.append((full, rel, int(line), m.group(1), "private" in text[:m.start()]))
    return decls


def active_namespaces(ctx):
    parts = ctx["namespace"].split(".") if ctx["namespace"] else []
    act = {""} | {".".join(parts[:i]) for i in range(1, len(parts) + 1)}
    for o in ctx["opens"] + [p for p in ctx["directly_above"] if p.startswith("open ")]:
        body = re.sub(r"\s*\[line \d+\]$", "", o)[5:].replace("scoped ", "")
        body = re.sub(r"\(.*?\)|hiding.*|renaming.*|\bin$", "", body)
        for nm in body.split():
            act.add(nm)
            for i in range(1, len(parts) + 1):
                act.add(".".join(parts[:i]) + "." + nm)
    return act


def captures(decls, ctx, path, tokens):
    act, out = active_namespaces(ctx), []
    for full, rel, line, kind, private in decls:
        if private and rel != path:
            continue
        for w in tokens:
            w = w.lstrip(".")
            if full == w or full.endswith("." + w):
                if full[:-len(w)].rstrip(".") in act:
                    out.append(dict(written=w, archive_declaration=full, kind=kind, where=f"{rel}:{line}"))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--arch", required=True)
    ap.add_argument("--mathlib", required=True)
    ap.add_argument("--decl-index")
    ap.add_argument("--notation-scan")
    ap.add_argument("--out", default=str(HERE / "claims.json"))
    ap.add_argument("--print-names", action="store_true",
                    help="print the alternation of identifier names for the rg declaration scan and stop")
    a = ap.parse_args()
    arch, mathlib = Path(a.arch), Path(a.mathlib)
    src = runpy.run_path(str(HERE / "ledger_src.py"))
    if a.print_names:
        names = set()
        for c in src["CLAIMS"]:
            lines = strip_comments((arch / c["path"]).read_text(encoding="utf-8")).split("\n")
            st = statement(lines, c["line"])
            found, unknown, _ = identifiers(st, context(lines, c["line"])["variables"], src["RESOLVE"], c.get("bound", ()))
            if unknown:
                raise SystemExit(f"{c['id']} {c['name']}: unresolved identifiers {unknown}\n{st}")
            names |= {t.lstrip(".").split(".")[-1] for t in found}
        print("|".join(sorted(names)))
        return
    decls = load_decl_index(a.decl_index, arch) if a.decl_index else None
    notation = None
    if a.notation_scan:
        kinds = {}
        for row in open(a.notation_scan, encoding="utf-8"):
            text = row.split(":", 2)[2].strip()
            text = re.sub(r"^(@\[[^\]]*\]\s*)*(public |meta )*", "", text)
            k = text.split()[0]
            if k == "macro" or k == "elab":
                k += " (tactic)" if re.search(r":\s*tactic\s*=>", text) else " (command)" if re.search(r":\s*command\s*=>", text) else " (other)"
            kinds[k] = kinds.get(k, 0) + 1
        term_level = sum(v for k, v in kinds.items() if k.split()[0] in ("notation", "notation3", "infix", "infixl", "infixr", "prefix", "postfix", "syntax", "macro_rules")
                         or k.endswith("(other)"))
        notation = dict(top_level_declarations_by_kind=kinds, term_level_notation_declarations=term_level,
                        reading="the archive declares no global term-level notation; `local` and `scoped` notation is "
                                "listed per claim under context.notations when it precedes the statement in its file")
    sites, claims = {}, []
    for c in src["CLAIMS"]:
        raw = (arch / c["path"]).read_text(encoding="utf-8")
        lines = strip_comments(raw).split("\n")
        st = statement(lines, c["line"])
        assert re.search(r"\b" + re.escape(c["name"].split(".")[-1]) + r"(?![\w'])", st.split("\n")[0]), (c["id"], st[:80])
        ctx = context(lines, c["line"])
        found, unknown, bound = identifiers(st, ctx["variables"], src["RESOLVE"], c.get("bound", ()))
        if unknown:
            raise SystemExit(f"{c['id']} {c['name']}: unresolved identifiers {unknown}\n{st}")
        ids = []
        for tok, (qual, origin, file, regex) in sorted(found.items()):
            e = dict(written=tok, resolves_to=qual, origin=origin)
            if origin == "Mathlib":
                ln, text = mathlib_site(mathlib, file, regex)
                e["defined_at"] = f"{file}:{ln}"
                e["definition_line"] = text
                sites[qual] = e["defined_at"]
            elif origin == "core":
                e["defined_at"] = "Lean core or Batteries (outside the Mathlib checkout); no declaration of this name in the archive"
            else:
                e["defined_at"] = "archive-local, quoted under local_definitions"
            ids.append(e)
        symbols = {s: m for s, m in src["SYMBOLS"].items() if s in st}
        cap = None
        if decls is not None:
            cap = captures(decls, ctx, c["path"], list(found))
            expected = {n.strip().split(".")[-1] for d in c.get("local_definitions", []) for n in d["name"].split(",")}
            stray = [h for h in cap if h["written"].split(".")[-1] not in expected]
            if stray:
                raise SystemExit(f"{c['id']}: an archive declaration may capture an identifier: {stray}")
        mutants = []
        for k, m in enumerate(c["mutants"], 1):
            if m["replace"] is None:
                mst = f"theorem {c['name']}_mutant : Nat.Prime ({c['literal']} + {m['params']['offset']})"
            else:
                old, new = m["replace"]
                assert st.count(old) == 1, (c["id"], old, st.count(old))
                mst = st.replace(old, new)
            mutants.append(dict(id=f"{c['id']}-m{k}", tag=m["tag"], kind=m["kind"], change=m["replace"],
                                statement=mst, params=m["params"], fast=m["fast"], why_false=m["why_false"]))
        claims.append(dict(
            id=c["id"], name=c["name"], topic=c["topic"], path=c["path"], line=c["line"],
            verbatim=st, sha256=hashlib.sha256(st.encode("utf-8")).hexdigest(),
            file_sha256=hashlib.sha256(raw.encode("utf-8")).hexdigest(),
            context=dict(namespace=ctx["namespace"], opens=ctx["opens"], variables=ctx["variables"],
                         notations=ctx["notations"], local_overrides=ctx["local_overrides"],
                         directly_above=ctx["directly_above"], imports=ctx["imports"][:8],
                         imports_total=len(ctx["imports"])),
            bound_variables=bound, identifiers=ids, notation=symbols,
            local_definitions=c.get("local_definitions", []),
            capture_check=("not run" if cap is None else
                           dict(archive_declarations_that_could_capture=cap,
                                verdict="none besides the quoted local definitions" if cap else "none")),
            math=c["math"], conventions=[src["CONV"][k] for k in c["conv"]] + c.get("extra_conv", []),
            quantifiers=c["quant"], domain=c["domain"], grade_if_it_holds=c["grade"],
            sharpness=c["sharpness"], test=c["test"], mutants=mutants))
    meta = dict(src["ARCHIVE"], claims=len(claims), mutants=sum(len(c["mutants"]) for c in claims),
                extraction="text level: comments stripped, statement = declaration keyword to the first top-level ':='",
                notation_scan=notation,
                lakefile_options="autoImplicit = false, relaxedAutoImplicit = false (so an unbound name in a statement is an error, not a new variable)",
                capture_check_method=("for every identifier written in a statement, every archive declaration whose full name ends "
                                      "in it and whose namespace is the statement's namespace, a prefix of it, or an opened one")
                if decls is not None else "not run",
                mathlib_definition_sites=dict(sorted(sites.items())))
    Path(a.out).write_text(json.dumps(dict(meta=meta, claims=claims), ensure_ascii=False, indent=1) + "\n", encoding="utf-8")
    print(f"wrote {a.out}: {len(claims)} claims, {meta['mutants']} mutants")


if __name__ == "__main__":
    main()
