"""Recount the whole-tree statistics of an unpacked Lean source tree.

Text only: this walks `*.lean` files, counts lines and line-start keywords,
and builds the import graph from `import` lines. It runs no Lean and reads
nothing but file text, so every number it prints is a measured count of
text, not a statement about what a kernel would accept.

Usage (the tree is untrusted data, so isolate the interpreter):

    python -I recount.py SRC_DIR [--out FILE] [--closure Module.Name ...]
                         [--strings STRING ...] [--dirs DIRECTORY ...]
                         [--words NAME ...] [--decl-names NAME ...]

`SRC_DIR` is the directory that holds `Main.lean`.

* `--strings`: for each fixed string (matched without regard to case), the
  number of files that contain it, the number that contain it outside import
  lines, and the number of such lines.
* `--dirs`: for each directory (relative, any depth), its files and lines,
  the files directly inside it, the number of its sub-directories, and for
  each of the `--strings` the number of its files that contain the string,
  anywhere and outside import lines.
* `--words`: for each name, the lines outside import lines that contain it
  as a whole word (case-sensitive; the rule of `rg -w -F`), and where.
* `--decl-names`: for each name, the declarations whose last name component
  is exactly that name, and where.

Standard library only.
"""
from __future__ import annotations

import json
import os
import re
import statistics
import sys
import time
from collections import Counter, defaultdict, deque

KINDS = "theorem|lemma|def|abbrev|structure|instance|example|inductive|class"
DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|nonrec|partial)\s+)*"
    rf"({KINDS})\b",
    re.M,
)
#: the same rule with `scoped` and `local` accepted as modifiers; only the
#: `instance` count differs between the two
DECL_WIDE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|nonrec|partial|scoped|local)\s+)*"
    rf"({KINDS})\b",
    re.M,
)
IMPORT = re.compile(r"^import[ \t]+(.+)$", re.M)
HYP_STRUCT = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*structure\s+(\S*(?:Hypothes|Literature|Published)\S*)", re.M
)
INPUT_STRUCT = re.compile(r"^(?:@\[[^\]]*\]\s*)*structure\s+(\S*Input\S*)", re.M)
HYP_DEF = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+)?def\s+(\S*Hypothes\S*)", re.M)
WORDS = {
    "sorry": re.compile(r"\bsorry\b"),
    "sorry_substring_any_case": re.compile(r"sorry", re.I),
    "admit": re.compile(r"\badmit\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "axiom_decl": re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+)*axiom\b", re.M),
    "axiom_word": re.compile(r"\baxiom\b"),
    "implemented_by": re.compile(r"implemented_by"),
    "extern_attr": re.compile(r"@\[extern"),
    "unsafe_word": re.compile(r"\bunsafe\b"),
    "unsafe_substring_any_case": re.compile(r"unsafe", re.I),
    "allowUnsafeReducibility": re.compile(r"allowUnsafeReducibility"),
    "decide_plus_kernel": re.compile(r"decide \+kernel"),
    "run_cmd": re.compile(r"\brun_cmd\b"),
    "run_tac": re.compile(r"\brun_tac\b"),
    "addDecl": re.compile(r"\baddDecl\b"),
    "set_option": re.compile(r"\bset_option\b"),
    "open_private": re.compile(r"^\s*open private\b", re.M),
    "partial_def": re.compile(r"\bpartial def\b"),
    "print_axioms": re.compile(r"#print axioms"),
    "hash_check": re.compile(r"#check\b"),
    "elab_macro_syntax_line_start": re.compile(r"^(?:scoped\s+|local\s+)?(?:elab|macro|syntax)\b", re.M),
    "line_comment_at_line_start": re.compile(r"^\s*--", re.M),
    "double_dash_anywhere": re.compile(r"--"),
    "block_comment_open": re.compile(r"/-"),
}
#: tokens counted by line, and the lines that reach the goal-assigning tactic
#: `kexactB` either by name or through a macro that expands to it
LINE_TOKENS = {
    "kexactB": re.compile(r"kexactB"),
    "kc%": re.compile(r"kc%"),
    "kq%": re.compile(r"kq%"),
    "kd%": re.compile(r"kd%"),
    "tr_via": re.compile(r"\btr_via\b"),
    "tr_clause": re.compile(r"\btr_clause\b"),
    "kcopy": re.compile(r"(?<![\w#])kcopy\b"),
    "run_tac": re.compile(r"\brun_tac\b"),
}
REACH = ("kexactB", "kc%", "kq%", "kd%", "tr_via", "tr_clause")
LINE_TOKEN_ANY = re.compile(r"kexactB|k[cqd]%|tr_via|tr_clause|kcopy|run_tac")

NAMESPACE = re.compile(r"^(namespace|end)\s+(\S+)\s*$")
PROP_DEF = re.compile(r"^(?:noncomputable\s+)?def\s+(\S+)\s*:\s*Prop\s*:=")
ONE_LINE_THEOREM = re.compile(r"^theorem \S+ : (\S+) :=")
PUBLISHED = "GlobalTheory.Published."
#: a wider rule for the same count: indentation and attributes tolerated,
#: `section` tracked, any `end` closes the innermost scope, `_root_.` honoured
SCOPE_WIDE = re.compile(r"^\s*(namespace|section|end)\b[ \t]*(\S*)")
PROP_DEF_WIDE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*def\s+(\S+)\s*:\s*Prop\s*:="
)
ONE_LINE_THEOREM_WIDE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected)\s+)*theorem \S+ : (\S+) :="
)


def walk(src: str):
    for root, dirs, files in os.walk(src):
        dirs.sort()
        for name in sorted(files):
            yield os.path.join(root, name)


def decl_name_rx(names: list[str]) -> re.Pattern:
    alt = "|".join(re.escape(n) for n in names)
    return re.compile(
        r"^\s*(?:@\[[^\]]*\]\s*)*"
        r"(?:(?:private|protected|noncomputable|nonrec|partial|scoped|local)\s+)*"
        r"(?:theorem|lemma|def|abbrev|structure|instance|inductive|class|opaque|axiom)\s+"
        rf"(?:[\w.]+\.)?({alt})(?![\w.'!?])",
        re.M,
    )


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        print(__doc__)
        return 2
    src = os.path.abspath(argv[1])
    out = None
    lists: dict[str, list[str]] = {
        "--closure": [], "--strings": [], "--dirs": [], "--words": [], "--decl-names": [],
    }
    rest = argv[2:]
    while rest:
        flag = rest.pop(0)
        if flag == "--out":
            out = rest.pop(0)
        elif flag in lists:
            while rest and not rest[0].startswith("--"):
                lists[flag].append(rest.pop(0))
        else:
            print(f"unknown argument {flag!r}")
            return 2
    closures, strings = lists["--closure"], lists["--strings"]
    dirs_wanted = [d.strip("/") for d in lists["--dirs"]]
    words, decl_names = lists["--words"], lists["--decl-names"]
    word_rx = {w: re.compile(r"(?<!\w)" + re.escape(w) + r"(?!\w)") for w in words}
    named_rx = decl_name_rx(decl_names) if decl_names else None
    t0 = time.time()
    n_files = n_nonlean = total_lines = total_bytes = 0
    d1 = defaultdict(lambda: [0, 0])
    d2 = defaultdict(lambda: [0, 0])
    decls: Counter = Counter()
    decls_wide: Counter = Counter()
    decls_d1 = defaultdict(Counter)
    kw_hits: Counter = Counter()
    kw_files: Counter = Counter()
    kw_sample = defaultdict(list)
    tok_lines: Counter = Counter()
    tok_files: Counter = Counter()
    tok_sample = defaultdict(list)
    hyp_structs = input_structs = hyp_defs = 0
    imports: dict[str, list[str]] = {}
    ext_roots: Counter = Counter()
    lines_of: dict[str, int] = {}
    longest_line: list[int] = []
    over_1000_bytes = 0
    largest = (0, "")
    formalism: dict[str, bool] = {}
    formalism_direct: dict[str, bool] = {}
    published_defs: dict[str, str] = {}
    published_defs_wide: dict[str, str] = {}
    theorem_types: set[str] = set()
    theorem_types_wide: set[str] = set()
    str_files: Counter = Counter()
    str_files_body: Counter = Counter()
    str_lines_body: Counter = Counter()
    dir_stat = {
        d: {"files": 0, "lines": 0, "files_direct": 0, "subs": set(),
            "str_any": Counter(), "str_body": Counter()}
        for d in dirs_wanted
    }
    word_hits = {w: [] for w in words}
    named = {n: [] for n in decl_names}
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
        relu = "/".join(parts)
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
        for m in DECL_WIDE.finditer(text):
            decls_wide[m.group(1)] += 1
        hyp_structs += len(HYP_STRUCT.findall(text))
        input_structs += len(INPUT_STRUCT.findall(text))
        hyp_defs += len(HYP_DEF.findall(text))
        file_lines = text.split("\n")
        if file_lines and file_lines[-1] == "":
            file_lines.pop()
        longest_line.append(max((len(x) for x in file_lines), default=0))
        if max((len(x) for x in raw.split(b"\n")), default=0) > 1000:
            over_1000_bytes += 1
        if nl > largest[0]:
            largest = (nl, relu)
        if parts[0] == "Formalism" and len(parts) > 2:
            formalism[parts[1]] = formalism.get(parts[1], False) or parts[-1].startswith("Statement")
            formalism_direct[parts[1]] = formalism_direct.get(parts[1], False) or (
                len(parts) == 3 and parts[-1].startswith("Statement")
            )
        if "theorem " in text:
            for x in file_lines:
                if x.startswith("theorem "):
                    tm = ONE_LINE_THEOREM.match(x)
                    if tm:
                        theorem_types.add(tm.group(1).replace("_root_.", ""))
                tw = ONE_LINE_THEOREM_WIDE.match(x)
                if tw:
                    theorem_types_wide.add(tw.group(1).replace("_root_.", ""))
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
                        published_defs.setdefault(full[len(PUBLISHED):], relu)
        if "Published" in text:
            scopes: list[tuple[str, str]] = []
            for x in file_lines:
                sm = SCOPE_WIDE.match(x)
                if sm:
                    if sm.group(1) == "end":
                        if scopes:
                            scopes.pop()
                    else:
                        scopes.append((sm.group(1), sm.group(2)))
                    continue
                dm = PROP_DEF_WIDE.match(x)
                if dm:
                    name = dm.group(1)
                    if name.startswith("_root_."):
                        full = name[len("_root_."):]
                    else:
                        full = ".".join([n for k, n in scopes if k == "namespace" and n] + [name])
                    if full.startswith(PUBLISHED):
                        published_defs_wide.setdefault(full[len(PUBLISHED):], relu)
        in_dirs = [d for d in dirs_wanted if relu.startswith(d + "/")]
        for d in in_dirs:
            st = dir_stat[d]
            st["files"] += 1
            st["lines"] += nl
            below = relu[len(d) + 1:].split("/")
            if len(below) == 1:
                st["files_direct"] += 1
            else:
                st["subs"].add(below[0])
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
                    for d in in_dirs:
                        dir_stat[d]["str_any"][s] += 1
                        if hits:
                            dir_stat[d]["str_body"][s] += 1
        for w in words:
            if w in text:
                for n, x in enumerate(file_lines, 1):
                    if w in x and not x.startswith("import ") and word_rx[w].search(x):
                        word_hits[w].append(f"{relu}:{n}")
        if named_rx is not None:
            for m in named_rx.finditer(text):
                named[m.group(1)].append(f"{relu}:{text.count(chr(10), 0, m.start(1)) + 1}")
        for key, rx in WORDS.items():
            c = len(rx.findall(text))
            if c:
                kw_hits[key] += c
                kw_files[key] += 1
                if len(kw_sample[key]) < 8:
                    kw_sample[key].append(relu)
        if LINE_TOKEN_ANY.search(text):
            seen: set[str] = set()
            for x in file_lines:
                reach = False
                for key, rx in LINE_TOKENS.items():
                    if rx.search(x):
                        tok_lines[key] += 1
                        seen.add(key)
                        reach = reach or key in REACH
                if reach:
                    tok_lines["reach_kexactB_by_name_or_macro"] += 1
                    seen.add("reach_kexactB_by_name_or_macro")
            for key in seen:
                tok_files[key] += 1
                if len(tok_sample[key]) < 8:
                    tok_sample[key].append(relu)
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

    def mathlib_only(m: str) -> bool:
        return bool(imports[m]) and all(i.split(".")[0] == "Mathlib" for i in imports[m])

    leaves_mathlib_only = sum(1 for m in leaves if mathlib_only(m))
    top_of = lambda m: m.split(".")[0] if "." in m else "(root)"  # noqa: E731
    dag_d1 = {k: {"import_leaves": 0, "import_leaves_mathlib_only": 0, "depth_min": None, "depth_max": None}
              for k in d1}
    for m in leaves:
        dag_d1[top_of(m)]["import_leaves"] += 1
        if mathlib_only(m):
            dag_d1[top_of(m)]["import_leaves_mathlib_only"] += 1
    for m, dep in depth.items():
        row = dag_d1[top_of(m)]
        row["depth_min"] = dep if row["depth_min"] is None else min(row["depth_min"], dep)
        row["depth_max"] = dep if row["depth_max"] is None else max(row["depth_max"], dep)

    def closure(root: str) -> set[str]:
        seen = {root}
        stack = [root]
        while stack:
            for i in edges.get(stack.pop(), ()):
                if i not in seen:
                    seen.add(i)
                    stack.append(i)
        return seen

    def closed(defs: dict[str, str], types: set[str]) -> int:
        return sum(
            1 for name in defs
            if PUBLISHED + name in types or "Published." + name in types or name in types
        )

    result = {
        "tool": "hunts/rh_claim_atlas/recount.py",
        "grade": "measured count (text only, no Lean run)",
        "arguments": {k.lstrip("-"): v for k, v in lists.items()},
        "n_lean_files": n_files,
        "n_non_lean_files": n_nonlean,
        "total_lines": total_lines,
        "total_bytes": total_bytes,
        "dir_depth1": {k: {"files": v[0], "lines": v[1]} for k, v in sorted(d1.items())},
        "dir_depth1_dag": {k: dag_d1[k] for k in sorted(dag_d1)},
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
        "decls_total_scoped_and_local_included_approx": dict(decls_wide),
        "decls_by_depth1_approx": {k: dict(v) for k, v in sorted(decls_d1.items())},
        "n_structures_named_hypothes_literature_published": hyp_structs,
        "n_structures_named_input": input_structs,
        "n_defs_named_hypothes": hyp_defs,
        "keyword_hits": dict(kw_hits),
        "keyword_files": dict(kw_files),
        "keyword_file_sample": dict(kw_sample),
        "keywords_scanned": sorted(WORDS),
        "line_tokens": {
            k: {"lines": tok_lines[k], "files": tok_files[k], "first_files_in_tree_order": tok_sample[k]}
            for k in list(LINE_TOKENS) + ["reach_kexactB_by_name_or_macro"]
        },
        "import_lines_naming_archive_modules": sum(
            1 for mods in imports.values() for i in mods if i in modules
        ),
        "file_shape": {
            "median_lines": statistics.median(lines_of.values()),
            "mean_lines": round(total_lines / n_files, 1) if n_files else None,
            "max_lines": largest[0],
            "max_lines_file": largest[1],
            "files_with_a_line_over_1000_characters": sum(1 for x in longest_line if x > 1000),
            "files_with_a_line_over_1000_bytes": over_1000_bytes,
            "median_longest_line_characters": statistics.median(longest_line) if longest_line else None,
        },
        "formalism_subdirectories": len(formalism),
        "formalism_subdirectories_with_statement_files": sum(1 for v in formalism.values() if v),
        "formalism_subdirectories_with_statement_files_directly_inside": sum(
            1 for v in formalism_direct.values() if v
        ),
        "published_namespace": {
            "rule": (
                "parameterless one-line `def X : Prop :=` inside namespace GlobalTheory.Published "
                "or a sub-namespace; closed means a one-line `theorem name : T :=` exists whose T is "
                "X, Published.X or GlobalTheory.Published.X"
            ),
            "prop_defs": len(published_defs),
            "with_one_line_theorem_of_that_type": closed(published_defs, theorem_types),
        },
        "published_namespace_wide_rule": {
            "rule": (
                "the same count with indentation and attributes tolerated, `section` tracked, any "
                "`end` closing the innermost scope and `_root_.` names honoured"
            ),
            "prop_defs": len(published_defs_wide),
            "with_one_line_theorem_of_that_type": closed(published_defs_wide, theorem_types_wide),
            "narrow_rule_names_missing_here": len(set(published_defs) - set(published_defs_wide)),
        },
        "strings": {
            s: {
                "files": str_files[s],
                "files_outside_import_lines": str_files_body[s],
                "lines_outside_import_lines": str_lines_body[s],
            }
            for s in strings
        },
        "directories": {
            d: {
                "files": st["files"],
                "lines": st["lines"],
                "files_directly_inside": st["files_direct"],
                "subdirectories": len(st["subs"]),
                "files_containing": {s: st["str_any"][s] for s in strings if st["str_any"][s]},
                "files_containing_outside_import_lines": {
                    s: st["str_body"][s] for s in strings if st["str_body"][s]
                },
            }
            for d, st in dir_stat.items()
        },
        "whole_words": {
            w: {"lines_outside_import_lines": len(v), "at": v[:16]} for w, v in word_hits.items()
        },
        "declarations_named": {n: {"count": len(v), "at": v[:8]} for n, v in named.items()},
        "closures": {},
        "seconds": None,
    }
    for root in closures:
        if root not in modules:
            result["closures"][root] = None
            continue
        c = closure(root)
        by_dir = Counter("/".join(m.split(".")[:3]) for m in c)
        # ties broken by name: `most_common` follows set order, which changes from run to run
        largest_dirs = sorted(by_dir.items(), key=lambda kv: (-kv[1], kv[0]))[:12]
        result["closures"][root] = {
            "modules": len(c),
            "lines": sum(lines_of[m] for m in c),
            "by_depth3_dir": dict(largest_dirs),
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
