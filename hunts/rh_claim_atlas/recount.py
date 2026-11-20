"""Recount the whole-tree statistics of an unpacked Lean source tree.

Text only: this walks `*.lean` files, counts lines and line-start keywords,
and builds the import graph from `import` lines. It runs no Lean and reads
nothing but file text, so every number it prints is a measured count of
text, not a statement about what a kernel would accept.

Usage (the tree is untrusted data, so isolate the interpreter):

    python -I recount.py SRC_DIR [--out FILE] [--closure Module.Name ...]
                         [--strings STRING ...]

`SRC_DIR` is the directory that holds `Main.lean`. `--strings` reports, for
each fixed string (matched without regard to case), the number of files that
contain it, the number that contain it outside import lines, and the number
of such lines, in total and by depth-2 directory. Standard library only.
"""
from __future__ import annotations

import json
import os
import re
import statistics
import sys
import time
from collections import Counter, defaultdict, deque

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|nonrec|partial)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|instance|example|inductive|class)\b",
    re.M,
)
IMPORT = re.compile(r"^import[ \t]+(.+)$", re.M)
HYP_STRUCT = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*structure\s+(\S*(?:Hypothes|Literature|Published)\S*)", re.M
)
WORDS = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "axiom_decl": re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+)*axiom\b", re.M),
    "implemented_by": re.compile(r"implemented_by"),
    "extern_attr": re.compile(r"@\[extern"),
    "unsafe_word": re.compile(r"\bunsafe\b"),
    "decide_plus_kernel": re.compile(r"decide \+kernel"),
    "run_cmd": re.compile(r"\brun_cmd\b"),
    "addDecl": re.compile(r"\baddDecl\b"),
    "set_option": re.compile(r"\bset_option\b"),
    "open_private": re.compile(r"^\s*open private\b", re.M),
    "elab_macro_syntax_line_start": re.compile(r"^(?:scoped\s+|local\s+)?(?:elab|macro|syntax)\b", re.M),
    "line_comment_at_line_start": re.compile(r"^\s*--", re.M),
    "block_comment_open": re.compile(r"/-"),
}


NAMESPACE = re.compile(r"^(namespace|end)\s+(\S+)\s*$")
PROP_DEF = re.compile(r"^(?:noncomputable\s+)?def\s+(\S+)\s*:\s*Prop\s*:=")
ONE_LINE_THEOREM = re.compile(r"^theorem \S+ : (\S+) :=")
PUBLISHED = "GlobalTheory.Published."


def walk(src: str):
    for root, dirs, files in os.walk(src):
        dirs.sort()
        for name in sorted(files):
            yield os.path.join(root, name)


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        print(__doc__)
        return 2
    src = os.path.abspath(argv[1])
    out = None
    closures: list[str] = []
    strings: list[str] = []
    rest = argv[2:]
    while rest:
        flag = rest.pop(0)
        if flag == "--out":
            out = rest.pop(0)
        elif flag == "--closure":
            while rest and not rest[0].startswith("--"):
                closures.append(rest.pop(0))
        elif flag == "--strings":
            while rest and not rest[0].startswith("--"):
                strings.append(rest.pop(0))
        else:
            print(f"unknown argument {flag!r}")
            return 2
    t0 = time.time()
    n_files = n_nonlean = total_lines = total_bytes = 0
    d1 = defaultdict(lambda: [0, 0])
    d2 = defaultdict(lambda: [0, 0])
    decls: Counter = Counter()
    decls_d1 = defaultdict(Counter)
    kw_hits: Counter = Counter()
    kw_files: Counter = Counter()
    kw_sample = defaultdict(list)
    hyp_structs = 0
    imports: dict[str, list[str]] = {}
    ext_roots: Counter = Counter()
    lines_of: dict[str, int] = {}
    longest_line: list[int] = []
    largest = (0, "")
    import_lines_internal_raw: list[list[str]] = []
    formalism: dict[str, bool] = {}
    published_defs: dict[str, str] = {}
    theorem_types: set[str] = set()
    str_files: Counter = Counter()
    str_files_body: Counter = Counter()
    str_lines_body: Counter = Counter()
    str_by_dir = defaultdict(Counter)
    for path in walk(src):
        rel = os.path.relpath(path, src)
        if not rel.endswith(".lean"):
            n_nonlean += 1
            continue
        with open(path, "rb") as fh:
            raw = fh.read()
        text = raw.decode("utf-8")
        n_files += 1
        nl = raw.count(b"\n") + (1 if raw and not raw.endswith(b"\n") else 0)
        total_lines += nl
        total_bytes += len(raw)
        parts = rel.split(os.sep)
        k1 = parts[0] if len(parts) > 1 else "(root)"
        k2 = "/".join(parts[:2]) if len(parts) > 2 else (k1 + "/(files)" if len(parts) == 2 else "(root)")
        d1[k1][0] += 1
        d1[k1][1] += nl
        d2[k2][0] += 1
        d2[k2][1] += nl
        mod = rel[: -len(".lean")].replace(os.sep, ".")
        lines_of[mod] = nl
        mods: list[str] = []
        for m in IMPORT.finditer(text):
            mods.extend(m.group(1).split())
        imports[mod] = mods
        for m in DECL.finditer(text):
            decls[m.group(1)] += 1
            decls_d1[k1][m.group(1)] += 1
        hyp_structs += len(HYP_STRUCT.findall(text))
        file_lines = text.split("\n")
        if file_lines and file_lines[-1] == "":
            file_lines.pop()
        longest_line.append(max((len(x) for x in file_lines), default=0))
        if nl > largest[0]:
            largest = (nl, rel.replace(os.sep, "/"))
        if parts[0] == "Formalism" and len(parts) > 2:
            formalism[parts[1]] = formalism.get(parts[1], False) or parts[-1].startswith("Statement")
        if "theorem " in text:
            for x in file_lines:
                if x.startswith("theorem "):
                    tm = ONE_LINE_THEOREM.match(x)
                    if tm:
                        theorem_types.add(tm.group(1).replace("_root_.", ""))
        if PUBLISHED[:-1] in text:
            stack: list[str] = []
            for x in file_lines:
                nm = NAMESPACE.match(x)
                if nm:
                    if nm.group(1) == "namespace":
                        stack.append(nm.group(2))
                    elif stack and stack[-1].split(".")[-1] == nm.group(2).split(".")[-1]:
                        stack.pop()
                    continue
                dm = PROP_DEF.match(x)
                if dm:
                    full = ".".join(stack + [dm.group(1)])
                    if full.startswith(PUBLISHED):
                        published_defs.setdefault(full[len(PUBLISHED):], rel.replace(os.sep, "/"))
        if strings:
            low = text.lower()
            for s in strings:
                if s.lower() in low:
                    str_files[s] += 1
                    hits = sum(
                        1 for x in file_lines if not x.startswith("import ") and s.lower() in x.lower()
                    )
                    if hits:
                        str_files_body[s] += 1
                        str_lines_body[s] += hits
                        str_by_dir[s][k2] += 1
        for key, rx in WORDS.items():
            c = len(rx.findall(text))
            if c:
                kw_hits[key] += c
                kw_files[key] += 1
                if len(kw_sample[key]) < 8:
                    kw_sample[key].append(rel.replace(os.sep, "/"))
    modules = set(imports)
    tops = {m.split(".")[0] for m in modules}
    edges: dict[str, set[str]] = {}
    unresolved = 0
    n_edges = 0
    fan_in: Counter = Counter()
    for mod, mods in imports.items():
        internal = set()
        for i in mods:
            if i in modules:
                internal.add(i)
            elif i.split(".")[0] in tops and i.split(".")[0] not in ("Mathlib", "Lean", "Batteries"):
                unresolved += 1
            else:
                ext_roots[i.split(".")[0]] += 1
        edges[mod] = internal
        n_edges += len(internal)
        for i in internal:
            fan_in[i] += 1
    # longest-path depth from the import leaves, by Kahn's algorithm
    rev = defaultdict(list)
    pending = {}
    for mod, internal in edges.items():
        pending[mod] = len(internal)
        for i in internal:
            rev[i].append(mod)
    depth = {m: 0 for m, c in pending.items() if c == 0}
    queue = deque(depth)
    done = 0
    while queue:
        m = queue.popleft()
        done += 1
        for parent in rev[m]:
            depth[parent] = max(depth.get(parent, 0), depth[m] + 1)
            pending[parent] -= 1
            if pending[parent] == 0:
                queue.append(parent)
    in_cycles = len(modules) - done
    hist = Counter((d // 25) * 25 for d in depth.values())
    leaves = [m for m, internal in edges.items() if not internal]
    leaves_mathlib_only = sum(
        1 for m in leaves if imports[m] and all(i.split(".")[0] == "Mathlib" for i in imports[m])
    )

    def closure(root: str) -> set[str]:
        seen = {root}
        stack = [root]
        while stack:
            for i in edges.get(stack.pop(), ()):
                if i not in seen:
                    seen.add(i)
                    stack.append(i)
        return seen

    result = {
        "tool": "hunts/rh_claim_atlas/recount.py",
        "grade": "measured count (text only, no Lean run)",
        "n_lean_files": n_files,
        "n_non_lean_files": n_nonlean,
        "total_lines": total_lines,
        "total_bytes": total_bytes,
        "dir_depth1": {k: {"files": v[0], "lines": v[1]} for k, v in sorted(d1.items())},
        "dir_depth2": {k: {"files": v[0], "lines": v[1]} for k, v in sorted(d2.items())},
        "n_internal_import_edges": n_edges,
        "n_unresolved_internal_imports": unresolved,
        "external_import_lines_by_root": dict(ext_roots),
        "n_modules_in_import_cycles": in_cycles,
        "max_dag_depth": max(depth.values()) if depth else None,
        "depth_of_Main": depth.get("Main"),
        "dag_depth_histogram_bin25": {str(k): hist[k] for k in sorted(hist)},
        "n_import_leaves": len(leaves),
        "n_import_leaves_mathlib_only": leaves_mathlib_only,
        "n_modules_fan_in_zero": sum(1 for m in modules if fan_in[m] == 0),
        "n_modules_reachable_from_Main": len(closure("Main")) if "Main" in modules else None,
        "decls_total_approx": dict(decls),
        "decls_by_depth1_approx": {k: dict(v) for k, v in sorted(decls_d1.items())},
        "n_structures_named_hypothes_literature_published": hyp_structs,
        "keyword_hits": dict(kw_hits),
        "keyword_files": dict(kw_files),
        "keyword_file_sample": dict(kw_sample),
        "import_lines_naming_archive_modules": sum(
            1 for mods in imports.values() for i in mods if i in modules
        ),
        "file_shape": {
            "median_lines": statistics.median(lines_of.values()),
            "mean_lines": round(total_lines / n_files, 1) if n_files else None,
            "max_lines": largest[0],
            "max_lines_file": largest[1],
            "files_with_a_line_over_1000_characters": sum(1 for x in longest_line if x > 1000),
            "median_longest_line_characters": statistics.median(longest_line) if longest_line else None,
        },
        "formalism_subdirectories": len(formalism),
        "formalism_subdirectories_with_statement_files": sum(1 for v in formalism.values() if v),
        "published_namespace": {
            "rule": (
                "parameterless one-line `def X : Prop :=` inside namespace GlobalTheory.Published "
                "or a sub-namespace; closed means a one-line `theorem name : T :=` exists whose T is "
                "X, Published.X or GlobalTheory.Published.X"
            ),
            "prop_defs": len(published_defs),
            "with_one_line_theorem_of_that_type": sum(
                1
                for name in published_defs
                if PUBLISHED + name in theorem_types
                or "Published." + name in theorem_types
                or name in theorem_types
            ),
        },
        "strings": {
            s: {
                "files": str_files[s],
                "files_outside_import_lines": str_files_body[s],
                "lines_outside_import_lines": str_lines_body[s],
                "files_outside_import_lines_by_depth2": dict(sorted(str_by_dir[s].items())),
            }
            for s in strings
        },
        "closures": {},
        "seconds": None,
    }
    for root in closures:
        if root not in modules:
            result["closures"][root] = None
            continue
        c = closure(root)
        by_dir = Counter("/".join(m.split(".")[:3]) for m in c)
        result["closures"][root] = {
            "modules": len(c),
            "lines": sum(lines_of[m] for m in c),
            "by_depth3_dir": dict(by_dir.most_common(12)),
        }
    result["seconds"] = round(time.time() - t0, 1)
    blob = json.dumps(result, indent=1, sort_keys=True, ensure_ascii=False)
    if out:
        with open(out, "w", encoding="utf-8") as fh:
            fh.write(blob + "\n")
    else:
        print(blob)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
