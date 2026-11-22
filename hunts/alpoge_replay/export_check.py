#!/usr/bin/env python3
"""A route that shares no checker with the others: export, then nanoda.

The first two passes are Lean's own kernel and the third is lean4lean, which
is derived from it. Here `lean4export` writes a declaration and everything it
depends on, down to the axioms, as text (the Lean 4 NDJSON export format),
and `nanoda`, a type checker for Lean 4 written in Rust, checks that file.
Neither program is built or run anywhere but on a runner, next to the
archive.

  summary   read an export file: versions, declarations by kind, axioms, and
            whether it holds every constant of a module (`ModuleConsts.lean`
            lists them)
  config    write nanoda's configuration for an export file
  selftest  export and check a toy package: an honest theorem must pass; a
            theorem that skipped the kernel and one resting on `sorry` must
            not
  run       export named declarations of a module, summarise, check

What a pass means: every declaration in the export file was accepted by
nanoda, and the file declares no axiom but the permitted ones. The file is
the declarations asked for and their dependencies; `summary` says whether
that is all of a module.
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import replay_check as rc  # noqa: E402

#: the axioms of Lean's logic; anything else in an export fails the check
STANDARD_AXIOMS = ("propext", "Classical.choice", "Quot.sound")

#: a theorem that is no theorem: `lake build` accepts it with a warning, and
#: its export declares the axiom `sorryAx`
LAZY = "theorem lazy : (1 : Nat) = 2 := sorry\n"

#: (module, declaration, must nanoda accept it)
TOY_CASES = (
    ("Lib.Honest", "honest", True),
    ("Lib.UsesCheat", "worse", False),     # rests on `bad`, whose proof has the wrong type
    ("Lib.Lazy", "lazy", False),           # rests on an axiom that is not permitted
)

DECL_KINDS = ("axiom", "def", "opaque", "thm", "quot")


def dotted(name: tuple) -> str:
    return ".".join(str(c) for c in name)


def read_export(path: str) -> dict:
    """Names, kinds and axioms of an export file (format 3.x), without checking anything."""
    names: dict[int, tuple] = {0: ()}
    kinds: dict[str, int] = {}
    declared: dict[tuple, str] = {}
    axioms: list[str] = []
    flagged: list[str] = []          # unsafe or partial declarations: the exporter leaves them out by default
    meta: dict = {}
    lines = 0

    def declare(obj: dict, kind: str) -> None:
        name = names[obj["name"]]
        declared[name] = kind
        kinds[kind] = kinds.get(kind, 0) + 1
        if obj.get("isUnsafe") or obj.get("safety") in ("unsafe", "partial"):
            flagged.append(dotted(name))

    with open(path, encoding="utf-8") as fh:
        for line in fh:
            if not line.strip():
                continue
            lines += 1
            obj = json.loads(line)
            if "meta" in obj:
                meta = obj["meta"]
            elif "in" in obj:
                if "str" in obj:
                    names[obj["in"]] = names[obj["str"]["pre"]] + (obj["str"]["str"],)
                else:
                    names[obj["in"]] = names[obj["num"]["pre"]] + (obj["num"]["i"],)
            elif "inductive" in obj:
                for part, kind in (("types", "inductive"), ("ctors", "constructor"), ("recs", "recursor")):
                    for item in obj["inductive"].get(part, []):
                        declare(item, kind)
            else:
                for kind in DECL_KINDS:
                    if kind in obj:
                        declare(obj[kind], kind)
                        if kind == "axiom":
                            axioms.append(dotted(names[obj[kind]["name"]]))
                        break
    return {"meta": meta, "lines": lines, "bytes": os.path.getsize(path), "kinds": dict(sorted(kinds.items())),
            "n_declared": len(declared), "axioms": sorted(axioms), "unsafe_or_partial": flagged,
            "declared": declared}


def summarise(path: str, consts_path: str | None = None, permitted=STANDARD_AXIOMS) -> dict:
    """What an export holds, and what of a module it does not."""
    ex = read_export(path)
    out = {k: v for k, v in ex.items() if k != "declared"}
    out["axioms_not_permitted"] = [a for a in ex["axioms"] if a not in permitted]
    if consts_path:
        given, missing, left_out = 0, [], []
        with open(consts_path, encoding="utf-8") as fh:
            for line in fh:
                if not line.strip():
                    continue
                c = json.loads(line)
                given += 1
                name = tuple(c["name"])
                if c.get("unsafe") or c.get("partial"):
                    left_out.append(dotted(name))        # no checker of proofs is given these
                elif name not in ex["declared"]:
                    missing.append(dotted(name))
        out["module"] = {"constants": given, "unsafe_or_partial": left_out, "missing_from_export": missing}
    return out


def nanoda_config(export_path: str, threads: int = 4, permitted=STANDARD_AXIOMS) -> dict:
    return {
        "export_file_path": os.path.abspath(export_path),
        "use_stdin": False,
        "num_threads": threads,
        # the archive compiles with a 400 MB thread stack: its terms are deep
        "stack_size_bytes": 1 << 30,
        "permitted_axioms": list(permitted),
        "unpermitted_axiom_hard_error": True,
        "nat_extension": True,
        "string_extension": True,
        "print_success_message": True,
    }


def export(l4e: str, pkg: str, module: str, decls: list[str], out_path: str) -> tuple[int, float, str]:
    """`lake env lean4export <module> -- <decls>` in a Lake package, into `out_path`."""
    start = time.time()
    with open(out_path, "wb") as fh:
        p = subprocess.run(["lake", "env", os.path.abspath(l4e), module, "--", *decls], cwd=pkg,
                           stdout=fh, stderr=subprocess.PIPE, preexec_fn=rc._big_stack)
    return p.returncode, time.time() - start, p.stderr.decode("utf-8", "replace")[-800:]


def check(nanoda: str, export_path: str, work: str, threads: int = 4, timeout_s: float | None = None) -> dict:
    """Run nanoda on an export. `accepted` is its exit code being 0."""
    cfg = os.path.join(work, os.path.basename(export_path) + ".nanoda.json")
    with open(cfg, "w", encoding="utf-8") as fh:
        json.dump(nanoda_config(export_path, threads), fh, indent=1)
    cmd = [os.path.abspath(nanoda), cfg]
    timed = os.path.exists("/usr/bin/time")
    if timed:
        cmd = ["/usr/bin/time", "-v", *cmd]
    start = time.time()
    try:
        p = subprocess.run(cmd, capture_output=True, timeout=timeout_s)
        code, out, err = p.returncode, p.stdout.decode("utf-8", "replace"), p.stderr.decode("utf-8", "replace")
    except subprocess.TimeoutExpired as e:
        code = None
        out = (e.stdout or b"").decode("utf-8", "replace")
        err = (e.stderr or b"").decode("utf-8", "replace")
    res = {"exit_code": code, "accepted": code == 0, "seconds": round(time.time() - start, 1),
           "stdout_tail": out[-1500:], "stderr_tail": err[-2500:]}
    for line in err.splitlines():
        if "Maximum resident set size" in line:
            res["max_rss_mb"] = int(line.rsplit(":", 1)[1]) // 1024
    return res


def selftest(l4e: str, nanoda: str, toolchain: str, work: str) -> dict:
    """Export and check the toy: passed only if nanoda accepts the honest
    theorem and neither of the two that are not theorems."""
    pkg = os.path.join(work, "toy")
    rc.write_toy(pkg, toolchain)
    with open(os.path.join(pkg, "src", "Lib", "Lazy.lean"), "w", encoding="utf-8") as fh:
        fh.write(LAZY)
    modules = sorted({m for m, _, _ in TOY_CASES})
    build = subprocess.run(["lake", "build", *modules], cwd=pkg, capture_output=True, text=True)
    out: dict = {"build_rc": build.returncode, "cases": {}, "passed": False}
    if build.returncode != 0:
        out["build_tail"] = (build.stdout + build.stderr)[-800:]
        return out
    ok = True
    for module, decl, want in TOY_CASES:
        path = os.path.join(work, f"toy-{decl}.ndjson")
        code, _, err = export(l4e, pkg, module, [decl], path)
        case: dict = {"export_rc": code, "want_accepted": want}
        if code != 0:
            case["export_stderr"] = err
            ok = False
        else:
            s = summarise(path)
            case.update({"declared": s["n_declared"], "axioms": s["axioms"], "format": s["meta"].get("format")})
            got = check(nanoda, path, work, threads=2, timeout_s=600)
            case.update({"accepted": got["accepted"], "exit_code": got["exit_code"],
                         "output": (got["stdout_tail"] + got["stderr_tail"])[-600:]})
            ok = ok and got["accepted"] == want
        out["cases"][decl] = case
    out["passed"] = ok
    return out


def cmd_summary(a) -> None:
    print(json.dumps(summarise(a.export, a.consts), ensure_ascii=False))


def cmd_config(a) -> None:
    with open(a.out, "w", encoding="utf-8") as fh:
        json.dump(nanoda_config(a.export, a.threads), fh, indent=1)


def cmd_selftest(a) -> None:
    out = selftest(a.lean4export, a.nanoda, a.toolchain, a.work)
    print("export selftest: " + json.dumps(out, ensure_ascii=False))
    if not out["passed"]:
        print("the checker did not accept the honest theorem and reject the two others; it may check nothing")
        sys.exit(1)


def cmd_run(a) -> None:
    os.makedirs(a.work, exist_ok=True)
    path = os.path.join(a.work, "export.ndjson")
    code, secs, err = export(a.lean4export, a.lean_dir, a.module, a.decl, path)
    out: dict = {"module": a.module, "declarations": a.decl, "export_rc": code, "export_seconds": round(secs, 1)}
    if code != 0:
        out["export_stderr"] = err
        print(json.dumps(out, ensure_ascii=False))
        sys.exit(1)
    out["export"] = summarise(path, a.consts)
    out["nanoda"] = check(a.nanoda, path, a.work, a.threads, a.minutes * 60)
    covered = not a.consts or not out["export"]["module"]["missing_from_export"]
    out["passed"] = bool(out["nanoda"]["accepted"] and not out["export"]["axioms_not_permitted"])
    out["covers_the_module"] = covered
    print(json.dumps(out, ensure_ascii=False))
    sys.exit(0 if out["passed"] else 1)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("summary")
    s.add_argument("export"); s.add_argument("--consts", help="the output of ModuleConsts.lean for one module")
    s.set_defaults(fn=cmd_summary)
    s = sub.add_parser("config")
    s.add_argument("export"); s.add_argument("out"); s.add_argument("--threads", type=int, default=4)
    s.set_defaults(fn=cmd_config)
    s = sub.add_parser("selftest")
    s.add_argument("--lean4export", required=True); s.add_argument("--nanoda", required=True)
    s.add_argument("--toolchain", required=True); s.add_argument("--work", required=True)
    s.set_defaults(fn=cmd_selftest)
    s = sub.add_parser("run")
    s.add_argument("--lean4export", required=True); s.add_argument("--nanoda", required=True)
    s.add_argument("--lean-dir", required=True); s.add_argument("--module", required=True)
    s.add_argument("--decl", nargs="+", required=True, help="declarations to export with what they depend on")
    s.add_argument("--consts", help="the output of ModuleConsts.lean for the module")
    s.add_argument("--threads", type=int, default=4); s.add_argument("--minutes", type=float, default=120)
    s.add_argument("--work", required=True)
    s.set_defaults(fn=cmd_run)
    a = ap.parse_args()
    a.fn(a)


if __name__ == "__main__":
    main()
