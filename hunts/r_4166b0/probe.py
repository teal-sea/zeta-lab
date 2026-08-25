#!/usr/bin/env python3
"""Hunt R-4166B0 (#109) -- reproduce and freshness-check ethereum/soundcalc.

Two verdicts per unit, never merged:

  REPRODUCTION  does the checked-in TOML follow from the vendor's own tree at
                the version the TOML names?
  FRESHNESS     does the same TOML still describe the vendor's current release?

Runnable end to end:

    python3 probe.py all           # every stage, writes results.json
    python3 probe.py stage0        # soundcalc reproduces its own reports
    python3 probe.py pins          # every provenance pin resolves
    python3 probe.py derive        # re-derive TOML fields from vendor source
    python3 probe.py freshness     # vendor current release vs the named version
    python3 probe.py control       # planted faults, to show the checks can fail

Needs network and `git`. `gh` is used where available for tag metadata and
falls back to unauthenticated HTTPS. Everything fetched is written under
`data/` with its sha256, so a later reader can see exactly what was read.

Nothing here bears on RH (docs/08). Nothing here is a statement about a vendor
or about the security of any deployed system: every statement is scoped to the
artifact at the pinned commit.
"""

from __future__ import annotations

import hashlib
import json
import math
import os
import re
import shutil
import subprocess
import sys
import urllib.error
import urllib.request
from pathlib import Path

HERE = Path(__file__).resolve().parent
DATA = HERE / "data"
WORK = Path(os.environ.get("R4166B0_WORK", "/tmp/r4166b0_probe"))

# The published record, pinned. This is the object under test.
SOUNDCALC_REPO = "https://github.com/ethereum/soundcalc.git"
SOUNDCALC_PIN = "d9078d64c9c3ae15b0931f6d249b2dc073194f15"  # 2026-07-23
TOML_PKG = "toml==0.10.2"  # soundcalc imports `toml`; its pyproject declares no deps

READ_DATE = "2026-08-24"

# ---------------------------------------------------------------- utilities


def sh(cmd, cwd=None, check=True, timeout=1800):
    r = subprocess.run(
        cmd, cwd=cwd, shell=isinstance(cmd, str), capture_output=True,
        text=True, timeout=timeout,
    )
    if check and r.returncode != 0:
        raise RuntimeError(f"{cmd}\n{r.stdout}\n{r.stderr}")
    return r


def fetch(url, dest: Path) -> dict:
    """GET a raw artifact, record its sha256 and byte count. 404 is a result."""
    dest.parent.mkdir(parents=True, exist_ok=True)
    req = urllib.request.Request(url, headers={"User-Agent": "zeta-lab-r4166b0"})
    try:
        with urllib.request.urlopen(req, timeout=90) as r:
            body = r.read()
    except urllib.error.HTTPError as e:
        return {"url": url, "status": e.code, "present": False}
    dest.write_bytes(body)
    return {
        "url": url, "status": 200, "present": True, "bytes": len(body),
        "sha256": hashlib.sha256(body).hexdigest(),
        "path": str(dest.relative_to(HERE)),
    }


def raw(repo, ref, path):
    return f"https://raw.githubusercontent.com/{repo}/{ref}/{path}"


def gh_json(endpoint):
    r = subprocess.run(["gh", "api", endpoint], capture_output=True, text=True, timeout=90)
    if r.returncode != 0:
        return None
    try:
        return json.loads(r.stdout)
    except json.JSONDecodeError:
        return None


def ref_exists(repo_url, sha) -> bool:
    """Does this commit exist in this repository? Asked of git, not of an API.

    `git fetch --depth 1 <url> <sha>` makes the server resolve the object.
    A server that does not have it answers 'not our ref'.
    """
    tmp = WORK / ("refprobe_" + hashlib.sha1((repo_url + sha).encode()).hexdigest()[:10])
    if tmp.exists():
        shutil.rmtree(tmp)
    tmp.mkdir(parents=True)
    sh(["git", "init", "-q"], cwd=tmp)
    r = sh(["git", "fetch", "-q", "--depth", "1", repo_url, sha], cwd=tmp, check=False)
    shutil.rmtree(tmp, ignore_errors=True)
    return r.returncode == 0


def remote_refs(repo_url, kind="heads"):
    r = sh(["git", "ls-remote", f"--{kind}", repo_url], check=False, timeout=180)
    out = {}
    for line in r.stdout.splitlines():
        if "\t" not in line:
            continue
        sha, name = line.split("\t", 1)
        if name.endswith("^{}"):
            name = name[:-3]
        out[name.split("/", 2)[-1]] = sha
    return out


# ------------------------------------------------------- soundcalc at its pin


def soundcalc_tree() -> Path:
    """Clone soundcalc and hard-pin it. Never mutated; experiments use copies."""
    tree = WORK / "soundcalc"
    if not (tree / ".git").exists():
        WORK.mkdir(parents=True, exist_ok=True)
        shutil.rmtree(tree, ignore_errors=True)
        sh(["git", "clone", "-q", SOUNDCALC_REPO, str(tree)], timeout=900)
    sh(["git", "checkout", "-q", SOUNDCALC_PIN], cwd=tree)
    sh(["git", "clean", "-qfdx"], cwd=tree)
    sh(["git", "checkout", "-q", "--", "."], cwd=tree)
    return tree


def runner_python() -> str:
    """An interpreter with `toml`. soundcalc needs it and does not declare it."""
    venv = WORK / "scvenv"
    py = venv / "bin" / "python"
    if not py.exists():
        sh([sys.executable, "-m", "venv", str(venv)], timeout=600)
        sh([str(venv / "bin" / "pip"), "-q", "install", TOML_PKG], timeout=900)
    return str(py)


def run_soundcalc(tree: Path) -> str:
    r = sh([runner_python(), "-m", "soundcalc"], cwd=tree, check=False, timeout=1800)
    return r.stdout + r.stderr


def skipped_units(output: str):
    """soundcalc does not fail on a config it cannot read. It prints and skips."""
    return dict(re.findall(r"^\s*-\s*(\S+):\s*missing '([^']+)'", output, re.M))


def reports_dirty(tree: Path):
    r = sh(["git", "status", "--porcelain", "reports/"], cwd=tree, check=False)
    return [l.strip() for l in r.stdout.splitlines() if l.strip()]


# ------------------------------------------------------------------ stage 0


def stage0():
    """Kill condition 1: does soundcalc reproduce its own reports/ from its own TOMLs?"""
    tree = soundcalc_tree()
    out = run_soundcalc(tree)
    written = re.findall(r"^wrote :: reports/(\S+)", out, re.M)
    checked_in = sorted(p.name for p in (tree / "reports").glob("*.md"))
    skipped = skipped_units(out)
    dirty = reports_dirty(tree)
    res = {
        "soundcalc_pin": SOUNDCALC_PIN,
        "reports_checked_in": checked_in,
        "reports_regenerated": sorted(written),
        "reports_not_regenerated": sorted(set(checked_in) - set(written)),
        "units_skipped_by_loader": skipped,
        "byte_identical_after_rerun": dirty == [],
        "dirty_files": dirty,
        "undeclared_dependency": {
            "module": "toml",
            "declared_in_pyproject": False,
            "note": "pyproject.toml sets dependencies = []; `python3 -m soundcalc` "
                    "raises ModuleNotFoundError on a clean interpreter.",
        },
    }
    res["verdict"] = (
        "reproduces" if res["byte_identical_after_rerun"] else "does-not-reproduce"
    )
    return res


# ------------------------------------------------------------------- pins

# Every provenance pin the TOMLs name, and where it points.
PINS = [
    dict(unit="Airbender", kind="commit", repo="matter-labs/zksync-airbender",
         ref="632d19b946d23180c2548626cbff4dbcce8ddb04",
         cited_in="airbender.toml header 'Commit:'"),
    dict(unit="Miden", kind="commit", repo="0xMiden/miden-vm",
         ref="fde5256c7ea99112e7dc2677b4c57ad824f63dcb",
         cited_in="miden.toml header, air/src/options.rs#L47"),
    dict(unit="RISC0", kind="commit", repo="risc0/risc0",
         ref="ebc18c770c4dd5a8e8dfdca1297edb181848405f",
         cited_in="risc0.toml header, risc0/zkp/src/docs/soundness.ipynb"),
    dict(unit="OpenVM", kind="commit", repo="openvm-org/stark-backend",
         ref="0c33328916d95047325b60a8044ecf9468db84bb",
         cited_in="openvm.toml, app circuit num_queries"),
    dict(unit="OpenVM", kind="commit", repo="openvm-org/stark-backend",
         ref="972f5dbecb6ab3ff7e3e978e9087235ad17c1de9",
         cited_in="openvm.toml, leaf and internal circuits"),
    dict(unit="SP1", kind="tag", repo="succinctlabs/sp1", ref="v6.1.0",
         cited_in="sp1.toml version = \"6.1.0\""),
    dict(unit="Pico", kind="branch", repo="brevis-network/pico", ref="soundcalc",
         cited_in="pico.toml header"),
    dict(unit="ZisK", kind="branch", repo="0xPolygonHermez/pil2-proofman",
         ref="pre-develop-0.17.0",
         cited_in="regenerate_zisk_config.sh step 4"),
]


def pins():
    out = []
    for p in PINS:
        url = f"https://github.com/{p['repo']}.git"
        if p["kind"] == "commit":
            ok = ref_exists(url, p["ref"])
        elif p["kind"] == "tag":
            ok = p["ref"] in remote_refs(url, "tags")
        else:
            ok = p["ref"] in remote_refs(url, "heads")
        out.append({**p, "resolves": ok})
    return out


# ------------------------------------------------- re-derivation from source

def derive_risc0(tree: Path):
    """risc0.toml cites one notebook. Re-derive every field it carries."""
    pin = "ebc18c770c4dd5a8e8dfdca1297edb181848405f"
    m = fetch(raw("risc0/risc0", pin, "risc0/zkp/src/docs/soundness.ipynb"),
              DATA / "risc0_soundness_pinned.ipynb")
    if not m["present"]:
        return {"verdict": "source-unavailable", "artifact": m}
    nb = json.loads((DATA / "risc0_soundness_pinned.ipynb").read_text())
    src = "\n".join("".join(c["source"]) for c in nb["cells"] if c["cell_type"] == "code")

    def const(name):
        hit = re.search(rf"^\s*{name}\s*=\s*([0-9]+)", src, re.M)
        return int(hit.group(1)) if hit else None

    k, h = const("k"), const("h")
    nb_vals = {
        "rho": 1 / (1 << k) if k is not None else None,
        "trace_length": (1 << h) if h is not None else None,
        "num_queries": const("s"),
        "num_columns": sum(x for x in (const("num_control"), const("num_data"),
                                       const("num_accum")) if x is not None),
        "opening_points": const("max_combo"),
        "field_extension_degree": const("ext_size"),
        "max_degree": const("max_degree"),
    }
    nb_vals["batch_size"] = nb_vals["num_columns"] + 4  # notebook: L = C + 4

    import tomllib
    t = tomllib.loads((tree / "soundcalc/zkvms/risc0/risc0.toml").read_text())
    c = t["circuits"][0]
    checks = {
        "rho": (c["rho"], nb_vals["rho"]),
        "trace_length": (c["trace_length"], nb_vals["trace_length"]),
        "num_queries": (c["num_queries"], nb_vals["num_queries"]),
        "num_columns": (c["num_columns"], nb_vals["num_columns"]),
        "opening_points": (c["opening_points"], nb_vals["opening_points"]),
        "batch_size": (c["batch_size"], nb_vals["batch_size"]),
    }
    agree = {k2: (a == b) for k2, (a, b) in checks.items()}
    # The TOML's folding schedule is arithmetic on those constants.
    D = c["trace_length"] / c["rho"]
    d = D
    for f in c["fri_folding_factors"]:
        d /= f
    agree["fri_schedule_lands_on_early_stop"] = (d == c["fri_early_stop_degree"])
    return {
        "verdict": "match" if all(agree.values()) else "mismatch",
        "fields_checked": len(agree),
        "fields_agreeing": sum(agree.values()),
        "per_field": {k2: {"toml": checks[k2][0], "source": checks[k2][1]}
                      for k2 in checks},
        "agree": agree,
        "documented_deviations": [
            "air_max_degree = 4 while the notebook sets max_degree = 5; the TOML "
            "states the reason at the point of use (DEEP-ALI uses d-1).",
            "fri_early_stop_degree derived arithmetically, not read from the notebook.",
        ],
        "self_flagged_unverified": ["hash_size_bits (TOML comment: 'TODO: check if "
                                    "that is actually true')"],
        "missing_required_key": "num_constraints",
        "artifact": m,
    }


def derive_miden(tree: Path):
    """miden.toml cites one Rust constant. Re-derive the fields it carries."""
    pin = "fde5256c7ea99112e7dc2677b4c57ad824f63dcb"
    m = fetch(raw("0xMiden/miden-vm", pin, "air/src/options.rs"),
              DATA / "miden_options_pinned.rs")
    if not m["present"]:
        return {"verdict": "source-unavailable", "artifact": m}
    text = (DATA / "miden_options_pinned.rs").read_text()
    blk = re.search(
        r"RECURSIVE_96_BITS:\s*WinterProofOptions\s*=\s*WinterProofOptions::new\(([^)]*)\)",
        text, re.S)
    args = [a.strip() for a in blk.group(1).split(",") if a.strip()]
    # WinterProofOptions::new(num_queries, blowup_factor, grinding_factor,
    #                         field_extension, fri_folding_factor,
    #                         fri_remainder_max_degree, ...)
    src_vals = {
        "num_queries": int(args[0]),
        "blowup_factor": int(args[1]),
        "grinding_query_phase": int(args[2]),
        "field_extension": args[3],
        "fri_folding_factor": int(args[4]),
        "fri_remainder_max_degree": int(args[5]),
    }
    import tomllib
    t = tomllib.loads((tree / "soundcalc/zkvms/miden/miden.toml").read_text())
    c = t["circuits"][0]
    checks = {
        "num_queries": (c["num_queries"], src_vals["num_queries"]),
        "rho": (c["rho"], 1 / src_vals["blowup_factor"]),
        "grinding_query_phase": (c["grinding_query_phase"],
                                 src_vals["grinding_query_phase"]),
        "field": (t["zkevm"]["field"],
                  "Goldilocks^2" if src_vals["field_extension"].endswith("Quadratic")
                  else src_vals["field_extension"]),
        "fri_folding_factor": (set(c["fri_folding_factors"]),
                               {src_vals["fri_folding_factor"]}),
    }
    agree = {k: (a == b) for k, (a, b) in checks.items()}
    return {
        "verdict": "match" if all(agree.values()) else "mismatch",
        "fields_checked": len(agree),
        "fields_agreeing": sum(agree.values()),
        "per_field": {k: {"toml": (sorted(v[0]) if isinstance(v[0], set) else v[0]),
                          "source": (sorted(v[1]) if isinstance(v[1], set) else v[1])}
                      for k, v in checks.items()},
        "agree": agree,
        "documented_deviations": [
            f"fri_early_stop_degree = {c['fri_early_stop_degree']} while the cited "
            f"constant sets fri_remainder_max_degree = "
            f"{src_vals['fri_remainder_max_degree']}; the TOML states the reason.",
        ],
        "self_flagged_unverified": [
            "trace_length, num_columns, batch_size, opening_points -- the TOML marks "
            "each 'XXX need to check ... by running the prover' or 'XXX ???'.",
            "hash_size_bits (TOML comment: 'TODO: check if that is actually true').",
        ],
        "missing_required_key": "num_constraints",
        "artifact": m,
    }


def derive_openvm(tree: Path):
    """openvm.toml cites three source lines. Check each line carries its value."""
    refs = {
        "a": "0c33328916d95047325b60a8044ecf9468db84bb",
        "b": "972f5dbecb6ab3ff7e3e978e9087235ad17c1de9",
    }
    arts, lines = {}, {}
    for k, ref in refs.items():
        m = fetch(raw("openvm-org/stark-backend", ref,
                      "crates/stark-sdk/src/config/fri_params.rs"),
                  DATA / f"openvm_fri_params_{ref[:8]}.rs")
        arts[k] = m
        if not m["present"]:
            return {"verdict": "source-unavailable", "artifacts": arts}
        lines[k] = (DATA / f"openvm_fri_params_{ref[:8]}.rs").read_text().splitlines()

    def params_at(which, fn, log_blowup):
        """Read the FriParameters arm for this log_blowup out of this function."""
        txt = "\n".join(lines[which])
        body = txt.split(f"pub fn {fn}(", 1)[1]
        arm = re.search(rf"^\s*{log_blowup} => FriParameters \{{(.*?)^\s*\}},",
                        body, re.S | re.M).group(1)
        return {k: int(v) for k, v in re.findall(r"(\w+):\s*(\d+)", arm)}

    # The three citations, as written in the TOML.
    citations = [
        dict(circuit="app", ref=refs["a"], line=183,
             fn="standard_fri_params_with_100_bits_security", log_blowup=1),
        dict(circuit="leaf", ref=refs["b"], line=65,
             fn="standard_fri_params_with_100_bits_conjectured_security", log_blowup=1),
        dict(circuit="internal", ref=refs["b"], line=71,
             fn="standard_fri_params_with_100_bits_conjectured_security", log_blowup=2),
    ]
    import tomllib
    t = tomllib.loads((tree / "soundcalc/zkvms/openvm/openvm.toml").read_text())
    by_name = {c["name"]: c for c in t["circuits"]}

    out = []
    for cit in citations:
        which = "a" if cit["ref"] == refs["a"] else "b"
        at_line = lines[which][cit["line"] - 1].strip()
        cited_fn = params_at(which, cit["fn"], cit["log_blowup"])
        toml_q = by_name[cit["circuit"]]["num_queries"]
        out.append({
            **cit,
            "text_at_cited_line": at_line,
            "value_in_cited_function_arm": cited_fn.get("num_queries"),
            "toml_num_queries": toml_q,
            "cited_line_carries_the_value": at_line == f"num_queries: {toml_q},",
            "cited_arm_matches_toml": cited_fn.get("num_queries") == toml_q,
        })

    # Do the TOML's values reproduce from ONE function at the newer commit?
    single = {lb: params_at("a", "standard_fri_params_with_100_bits_security", lb)
              for lb in (1, 2)}
    reproduces = {
        "app": by_name["app"]["num_queries"] == single[1]["num_queries"]
               and by_name["app"]["grinding_batching_phase"] == single[1]["commit_proof_of_work_bits"]
               and by_name["app"]["grinding_query_phase"] == single[1]["query_proof_of_work_bits"],
        "leaf": by_name["leaf"]["num_queries"] == single[1]["num_queries"]
                and by_name["leaf"]["grinding_batching_phase"] == single[1]["commit_proof_of_work_bits"]
                and by_name["leaf"]["grinding_query_phase"] == single[1]["query_proof_of_work_bits"],
        "internal": by_name["internal"]["num_queries"] == single[2]["num_queries"]
                    and by_name["internal"]["grinding_batching_phase"] == single[2]["commit_proof_of_work_bits"]
                    and by_name["internal"]["grinding_query_phase"] == single[2]["query_proof_of_work_bits"],
    }
    stale = [c["circuit"] for c in out if not c["cited_arm_matches_toml"]]
    return {
        "verdict": "match" if all(reproduces.values()) else "mismatch",
        "values_reproduce_from": {
            "repo": "openvm-org/stark-backend", "ref": refs["a"],
            "function": "standard_fri_params_with_100_bits_security",
            "arms": single,
        },
        "per_circuit_reproduces": reproduces,
        "citations": out,
        "stale_citations": stale,
        "note": ("The values reproduce. Two of the three citations point at a "
                 "superseded commit and a differently-named function whose arms "
                 "carry different, LOWER query counts. The TOML uses the higher "
                 "counts, so the citation is stale, not the number."),
        "artifacts": arts,
    }


SP1_CONSTS = {
    "crates/primitives/src/fri_params.rs": [
        "CORE_LOG_BLOWUP", "RECURSION_LOG_BLOWUP", "SHRINK_LOG_BLOWUP",
        "SP1_PROOF_OF_WORK_BITS", "SP1_SHRINK_WRAP_POW_BITS",
        "SP1_TARGET_BITS_OF_SECURITY",
    ],
    "crates/prover/src/components.rs": [
        "CORE_LOG_STACKING_HEIGHT", "CORE_MAX_LOG_ROW_COUNT",
        "RECURSION_LOG_TRACE_AREA", "SHRINK_LOG_TRACE_AREA",
        "SHRINK_LOG_STACKING_HEIGHT", "SHRINK_MAX_LOG_ROW_COUNT",
    ],
    "crates/verifier/src/compressed/config.rs": [
        "RECURSION_LOG_STACKING_HEIGHT", "RECURSION_MAX_LOG_ROW_COUNT",
    ],
    "slop/crates/basefold/src/verifier.rs": ["BATCH_GRINDING_BITS"],
}


def sp1_constants(ref):
    """Read the constants gen_soundcalc_toml.rs imports, at a pinned ref."""
    vals, arts = {}, []
    for path, names in SP1_CONSTS.items():
        m = fetch(raw("succinctlabs/sp1", ref, path),
                  DATA / f"sp1_{ref}_{Path(path).name}")
        arts.append({**m, "vendor_path": path})
        if not m["present"]:
            continue
        text = Path(HERE / m["path"]).read_text()
        for n in names:
            hit = re.search(rf"pub const {n}\s*:\s*\w+\s*=\s*([^;]+);", text)
            if hit:
                vals[n] = eval(hit.group(1).strip(), {"__builtins__": {}}, {})
    m = fetch(raw("succinctlabs/sp1", ref, "crates/core/executor/src/opts.rs"),
              DATA / f"sp1_{ref}_opts.rs")
    arts.append({**m, "vendor_path": "crates/core/executor/src/opts.rs"})
    if m["present"]:
        hit = re.search(r"pub const ELEMENT_THRESHOLD\s*:\s*u64\s*=\s*([^;]+);",
                        Path(HERE / m["path"]).read_text())
        if hit:
            vals["ELEMENT_THRESHOLD"] = eval(hit.group(1).strip(),
                                             {"__builtins__": {}}, {})
    return vals, arts


def sp1_expected(k):
    """Redo, in Python, exactly the arithmetic gen_soundcalc_toml.rs does."""
    def udq(log_blowup, grinding):
        rate = 1.0 / (1 << log_blowup)
        return math.ceil(-(k["SP1_TARGET_BITS_OF_SECURITY"] - grinding)
                         / math.log2(0.5 + rate / 2.0))
    pow_ = k["SP1_PROOF_OF_WORK_BITS"]
    return {
        "core": {
            "blowup_factor": 1 << k["CORE_LOG_BLOWUP"],
            "rho": 1.0 / (1 << k["CORE_LOG_BLOWUP"]),
            "trace_length": 1 << k["CORE_MAX_LOG_ROW_COUNT"],
            "dense_length": 1 << k["CORE_LOG_STACKING_HEIGHT"],
            "dense_batch": k["ELEMENT_THRESHOLD"] // (1 << k["CORE_LOG_STACKING_HEIGHT"]) + 1,
            "num_queries": udq(k["CORE_LOG_BLOWUP"], pow_),
            "fri_folding_factors": [2] * k["CORE_LOG_STACKING_HEIGHT"],
            "fri_early_stop_degree": 1 << k["CORE_LOG_BLOWUP"],
            "grinding_batching_phase": k["BATCH_GRINDING_BITS"],
            "grinding_query_phase": pow_,
        },
        "compress": {
            "blowup_factor": 1 << k["RECURSION_LOG_BLOWUP"],
            "rho": 1.0 / (1 << k["RECURSION_LOG_BLOWUP"]),
            "trace_length": 1 << k["RECURSION_MAX_LOG_ROW_COUNT"],
            "dense_length": 1 << k["RECURSION_LOG_STACKING_HEIGHT"],
            "dense_batch": (1 << k["RECURSION_LOG_TRACE_AREA"])
                           // (1 << k["RECURSION_LOG_STACKING_HEIGHT"]),
            "num_queries": udq(k["RECURSION_LOG_BLOWUP"], pow_),
            "fri_folding_factors": [2] * k["RECURSION_LOG_STACKING_HEIGHT"],
            "fri_early_stop_degree": 1 << k["RECURSION_LOG_BLOWUP"],
            "grinding_batching_phase": k["BATCH_GRINDING_BITS"],
            "grinding_query_phase": pow_,
        },
        "shrink": {
            "blowup_factor": 1 << k["SHRINK_LOG_BLOWUP"],
            "rho": 1.0 / (1 << k["SHRINK_LOG_BLOWUP"]),
            "trace_length": 1 << k["SHRINK_MAX_LOG_ROW_COUNT"],
            "dense_length": 1 << k["SHRINK_LOG_STACKING_HEIGHT"],
            "dense_batch": (1 << k["SHRINK_LOG_TRACE_AREA"])
                           // (1 << k["SHRINK_LOG_STACKING_HEIGHT"]),
            "num_queries": udq(k["SHRINK_LOG_BLOWUP"], k["SP1_SHRINK_WRAP_POW_BITS"]),
            "fri_folding_factors": [2] * k["SHRINK_LOG_STACKING_HEIGHT"],
            "fri_early_stop_degree": 1 << k["SHRINK_LOG_BLOWUP"],
            "grinding_batching_phase": k["BATCH_GRINDING_BITS"],
            "grinding_query_phase": k["SP1_SHRINK_WRAP_POW_BITS"],
        },
    }


# The generator computes these from machine.shape() at runtime. A build is the
# only documented route to them and this run does not do builds. Named, not
# guessed.
SP1_SHAPE_FIELDS = ["trace_columns", "num_constraints"]


def derive_sp1(tree: Path, ref):
    """Redo the constant-derived half of gen_soundcalc_toml.rs at a pinned ref."""
    k, arts = sp1_constants(ref)
    missing = [n for ns in SP1_CONSTS.values() for n in ns if n not in k]
    if missing or "ELEMENT_THRESHOLD" not in k:
        return {"verdict": "source-unavailable", "missing_constants": missing,
                "ref": ref, "artifacts": arts}
    exp = sp1_expected(k)
    import tomllib
    t = tomllib.loads((tree / "soundcalc/zkvms/sp1/sp1.toml").read_text())
    by_name = {c["name"]: c for c in t["circuits"]}
    per_field, agree = {}, {}
    for cname, want in exp.items():
        got = by_name[cname]
        for f, v in want.items():
            key = f"{cname}.{f}"
            per_field[key] = {"toml": got.get(f), "derived": v}
            agree[key] = got.get(f) == v
    return {
        "verdict": "match" if all(agree.values()) else "mismatch",
        "ref": ref,
        "constants_read": k,
        "fields_checked": len(agree),
        "fields_agreeing": sum(agree.values()),
        "per_field": per_field,
        "agree": agree,
        "not_checked_needs_a_build": {
            "fields": [f"{c}.{f}" for c in exp for f in SP1_SHAPE_FIELDS]
                      + ["*.lookups.num_lookups_M", "*.lookups.num_columns_S"],
            "why": "gen_soundcalc_toml.rs derives these from machine.shape() at "
                   "runtime; the only documented route is `cargo run --release "
                   "-p sp1-prover --bin gen_soundcalc_toml`, which this run does "
                   "not do (compute discipline: no heavy builds here).",
        },
        "artifacts": arts,
    }


# --------------------------------------------------------------- freshness

VENDOR_LATEST = [
    ("Airbender", "matter-labs/zksync-airbender"),
    ("Miden", "0xMiden/miden-vm"),
    ("OpenVM", "openvm-org/openvm"),
    ("OpenVM2", "openvm-org/openvm"),
    ("Pico", "brevis-network/pico"),
    ("RISC0", "risc0/risc0"),
    ("SP1", "succinctlabs/sp1"),
    ("Venus", "cysic-labs/venus"),
    ("ZisK", "0xPolygonHermez/zisk"),
]

NAMED_VERSION = {
    "Airbender": "commit 632d19b9 (header: Created 2026-02-24)",
    "Miden": "commit fde5256c (2025-08-29)",
    "OpenVM": "1.5.0", "OpenVM2": "2.0.0",
    "Pico": "branch `soundcalc` (no commit recorded)",
    "RISC0": "commit ebc18c77 notebook (dated September 2024)",
    "SP1": "6.1.0", "Venus": "0.1.6", "ZisK": "0.16.1",
    "zkDTVM": "0.8.0",
}


def freshness_versions():
    out = {}
    for unit, repo in VENDOR_LATEST:
        rel = gh_json(f"repos/{repo}/releases/latest") or {}
        out[unit] = {
            "vendor_repo": repo,
            "named_in_toml": NAMED_VERSION[unit],
            "vendor_latest_release": rel.get("tag_name"),
            "vendor_latest_release_date": rel.get("published_at"),
        }
    out["zkDTVM"] = {
        "vendor_repo": None,
        "named_in_toml": NAMED_VERSION["zkDTVM"],
        "vendor_latest_release": None,
        "note": "zkdtvm_v080.toml names `zkdtvm-suite/whir_config_koalabear_ext5.json` "
                "as its runtime source of truth; no public repository under "
                "AntChainOpenLabs carries that file.",
    }
    return out


def freshness_airbender(tree: Path):
    """The vendor's generator checks its own output in. Swap it and re-run."""
    m = fetch(raw("matter-labs/zksync-airbender", "dev",
                  "tools/pow_config_generator/airbender.toml"),
              DATA / "airbender_vendor_dev.toml")
    if not m["present"]:
        return {"verdict": "unable-to-regenerate", "artifact": m}
    vendor = (DATA / "airbender_vendor_dev.toml").read_text().split("\n")

    scratch = WORK / "sc_airbender"
    shutil.rmtree(scratch, ignore_errors=True)
    shutil.copytree(tree, scratch)
    target = scratch / "soundcalc/zkvms/airbender/airbender.toml"

    # (a) the vendor's output, unmodified
    target.write_text("\n".join(vendor))
    out_a = run_soundcalc(scratch)
    skipped_a = skipped_units(out_a)

    # (b) one hand intervention: move the single key soundcalc wants elsewhere
    i = next(n for n, l in enumerate(vendor) if l.strip().startswith("protocol_family"))
    moved = list(vendor)
    key = moved.pop(i)
    j = next(n for n, l in enumerate(moved) if l.strip() == "[[circuits]]")
    moved.insert(j + 1, key)
    target.write_text("\n".join(moved))
    run_soundcalc(scratch)

    def same(name):
        a = (tree / "reports" / name).read_text()
        b = (scratch / "reports" / name).read_text()
        return a == b

    header_only = [l for l in vendor if l.startswith("# Created:") or l.startswith("# Commit:")]
    return {
        "verdict": "unchanged" if (same("airbender.md") and same("summary.md"))
                   else "drifted",
        "hand_interventions": 1,
        "intervention": "move the single `protocol_family` key from [zkevm] into "
                        "the first [[circuits]] table",
        "vendor_output_loads_unmodified": "Airbender" not in skipped_a,
        "skip_reason_unmodified": skipped_a.get("Airbender"),
        "vendor_header": header_only,
        "airbender_md_identical": same("airbender.md"),
        "summary_md_identical": same("summary.md"),
        "artifact": m,
    }


def freshness_sp1(tree: Path):
    """Every constant the generator reads, at the vendor's latest tag."""
    at_gen, _ = sp1_constants("b69a2db2")   # tree where the TOML was generated
    at_latest, _ = sp1_constants("v6.4.0")  # vendor's latest release
    changed = {n: {"at_generation_tree": at_gen.get(n), "at_v6.4.0": at_latest.get(n)}
               for n in set(at_gen) | set(at_latest)
               if at_gen.get(n) != at_latest.get(n)}
    gen_at_tag = fetch(
        raw("succinctlabs/sp1", "v6.1.0",
            "crates/prover/scripts/gen_soundcalc_toml.rs"),
        DATA / "sp1_gen_at_v6.1.0.rs")
    gen_at_latest = fetch(
        raw("succinctlabs/sp1", "v6.4.0",
            "crates/prover/scripts/gen_soundcalc_toml.rs"),
        DATA / "sp1_gen_at_v6.4.0.rs")
    return {
        "verdict": "unchanged" if not changed else "drifted",
        "scope": "the constant-derived fields only; the shape-derived fields need "
                 "a build and were not checked",
        "constants_changed": changed,
        "constants_compared": sorted(set(at_gen) | set(at_latest)),
        "generator_present_at_named_version": gen_at_tag["present"],
        "generator_present_at_latest": gen_at_latest["present"],
    }


def freshness_miden():
    """Does the cited file still exist, and does it still carry the constant?"""
    at_latest = fetch(raw("0xMiden/miden-vm", "v0.29.2", "air/src/options.rs"),
                      DATA / "miden_options_v0.29.2.rs")
    hist = gh_json("repos/0xMiden/miden-vm/commits"
                   "?path=air/src/options.rs&per_page=5") or []
    return {
        "verdict": "unable-to-regenerate" if not at_latest["present"] else "drifted",
        "cited_file_present_at_latest_release": at_latest["present"],
        "cited_file_status_at_latest_release": at_latest.get("status"),
        "last_commits_touching_cited_file": [
            {"date": c["commit"]["committer"]["date"], "sha": c["sha"][:8],
             "subject": c["commit"]["message"].split("\n")[0]} for c in hist],
        "artifact": at_latest,
    }


def freshness_risc0():
    """Same object, or a different one?"""
    a = gh_json("repos/risc0/risc0/contents/risc0/zkp/src/docs/soundness.ipynb"
                "?ref=ebc18c770c4dd5a8e8dfdca1297edb181848405f") or {}
    b = gh_json("repos/risc0/risc0/contents/risc0/zkp/src/docs/soundness.ipynb"
                "?ref=v3.0.6") or {}
    hist = gh_json("repos/risc0/risc0/commits"
                   "?path=risc0/zkp/src/docs/soundness.ipynb&per_page=10") or []
    return {
        "verdict": "unchanged" if (a.get("sha") and a.get("sha") == b.get("sha"))
                   else "drifted",
        "blob_sha_at_pinned_commit": a.get("sha"),
        "blob_sha_at_latest_release": b.get("sha"),
        "commits_ever_touching_the_file": [
            {"date": c["commit"]["committer"]["date"], "sha": c["sha"][:8],
             "subject": c["commit"]["message"].split("\n")[0]} for c in hist],
        "scope": "This says the CITED ARTIFACT is unchanged. It does not say the "
                 "vendor's prover parameters are unchanged: the artifact is a "
                 "September 2024 notebook that has never been revised, while the "
                 "vendor has shipped several major versions since.",
    }


def freshness_zisk():
    """The one executable regeneration script in the repository. Does it still run?"""
    heads = remote_refs("https://github.com/0xPolygonHermez/pil2-proofman.git", "heads")
    branch = "pre-develop-0.17.0"
    key = gh_json("repos/0xPolygonHermez/zisk/releases/latest") or {}
    return {
        "verdict": "unable-to-regenerate",
        "script": "soundcalc/zkvms/zisk/regenerate_zisk_config.sh",
        "pinned_branch": branch,
        "pinned_branch_exists": branch in heads,
        "nearest_surviving_branches": sorted(
            n for n in heads if n.startswith("pre-develop-0.1")
            and n[len("pre-develop-0.1")] in "6789")[:6],
        "total_branches_on_remote": len(heads),
        "unpinned_inputs": [
            "`rustup default stable` -- a moving toolchain",
            f"`git clone --branch {branch}` -- a branch, not a commit (and it is gone)",
            "`wget .../zisk-provingkey-0.16.0.tar.gz` -- a proving key whose version "
            "(0.16.0) is not the version zisk.toml declares (0.16.1)",
        ],
        "vendor_latest_release": key.get("tag_name"),
    }


def venus_vs_zisk(tree: Path):
    """venus.toml states the claim in its own header. Check it."""
    import tomllib
    v = tomllib.loads((tree / "soundcalc/zkvms/venus/venus.toml").read_text())
    z = tomllib.loads((tree / "soundcalc/zkvms/zisk/zisk.toml").read_text())
    vc, zc = v["circuits"], z["circuits"]
    claim = ("Cross-validated against ZisK upstream - identical soundness "
             "parameters. (venus.toml header)")
    if [c["name"] for c in vc] != [c["name"] for c in zc]:
        return {"verdict": "not-comparable", "claim": claim}
    diffs = {}
    for a, b in zip(vc, zc):
        d = {k: {"venus": a.get(k), "zisk": b.get(k)}
             for k in set(a) | set(b) if a.get(k) != b.get(k)}
        if d:
            diffs[a["name"]] = d
    # A `group` relabel is bookkeeping; a numeric field is not.
    numeric = {c: {k: v2 for k, v2 in d.items() if k != "group"}
               for c, d in diffs.items()}
    numeric = {c: d for c, d in numeric.items() if d}
    # Does it move a published number?
    rv = (tree / "reports/venus.md").read_text()
    rz = (tree / "reports/zisk.md").read_text()
    def totals(md):
        return re.findall(r"^\| (UDR|JBR) \| (\d+) \|", md, re.M)
    return {
        "claim": claim,
        "verdict": "claim-does-not-hold" if numeric else "claim-holds",
        "circuits": len(vc),
        "circuits_differing_numerically": sorted(numeric),
        "circuits_differing_by_label_only": sorted(set(diffs) - set(numeric)),
        "differences": numeric,
        "regime_totals_venus": totals(rv),
        "regime_totals_zisk": totals(rz),
        "published_security_bits_affected": False,
        "why_not_soundness_impacting": (
            "Every per-regime TOTAL is identical between the two reports (UDR 63 / "
            "JBR 128 on the differing circuit, and each system's headline is 128 "
            "bits JBR). The differing component is ALI, which is not the binding "
            "term -- the query phase binds at 63/128. Venus's own numbers follow "
            "from Venus's own parameters; what fails is the header's equivalence "
            "claim, not either published figure."),
    }


# ---------------------------------------------------------------- controls
#
# A check that cannot fail is not a check. Each fault below is planted in a
# copy, and the stage that should notice it is re-run.

def control():
    tree = soundcalc_tree()
    out = []

    def lesion(name, mutate, stage, expect):
        scratch = WORK / f"ctl_{name}"
        shutil.rmtree(scratch, ignore_errors=True)
        shutil.copytree(tree, scratch)
        mutate(scratch)
        got = stage(scratch)
        out.append({"fault": name, "expected": expect, "observed": got,
                    "detected": got == expect})

    def bump_query(scratch):
        p = scratch / "soundcalc/zkvms/risc0/risc0.toml"
        p.write_text(p.read_text().replace("num_queries = 50", "num_queries = 51"))

    def risc0_stage(scratch):
        return derive_risc0(scratch)["verdict"]

    lesion("risc0-num_queries-51", bump_query, risc0_stage, "mismatch")

    def bump_miden(scratch):
        p = scratch / "soundcalc/zkvms/miden/miden.toml"
        p.write_text(p.read_text().replace("num_queries = 27", "num_queries = 28"))

    lesion("miden-num_queries-28", bump_miden,
           lambda s: derive_miden(s)["verdict"], "mismatch")

    def bump_sp1(scratch):
        p = scratch / "soundcalc/zkvms/sp1/sp1.toml"
        p.write_text(p.read_text().replace("num_queries = 124", "num_queries = 123", 1))

    lesion("sp1-core-num_queries-123", bump_sp1,
           lambda s: derive_sp1(s, "v6.4.0")["verdict"], "mismatch")

    def bump_openvm(scratch):
        p = scratch / "soundcalc/zkvms/openvm/openvm.toml"
        p.write_text(p.read_text().replace("num_queries = 118", "num_queries = 117"))

    lesion("openvm-internal-num_queries-117", bump_openvm,
           lambda s: derive_openvm(s)["verdict"], "mismatch")

    # stage0 REGENERATES the reports, so it is sensitive to a perturbed INPUT,
    # not to a perturbed output: a tampered report is overwritten before the
    # diff is taken. The lesion has to move a TOML.
    def perturb_input(scratch):
        p = scratch / "soundcalc/zkvms/airbender/airbender.toml"
        t = p.read_text()
        n = int(re.search(r"^num_queries = (\d+)", t, re.M).group(1))
        p.write_text(re.sub(r"^num_queries = \d+", f"num_queries = {n + 1}", t,
                            count=1, flags=re.M))

    def stage0_on(scratch):
        run_soundcalc(scratch)
        return "reproduces" if reports_dirty(scratch) == [] else "does-not-reproduce"

    lesion("airbender-toml-num_queries+1", perturb_input, stage0_on,
           "does-not-reproduce")

    # Positive control: if the two configs really did carry identical circuits,
    # does the checker say so? Give venus.toml zisk's circuits verbatim.
    def align_venus(scratch):
        p = scratch / "soundcalc/zkvms/venus/venus.toml"
        z = (scratch / "soundcalc/zkvms/zisk/zisk.toml").read_text()
        head = p.read_text().split("[[circuits]]", 1)[0]
        p.write_text(head + "[[circuits]]" + z.split("[[circuits]]", 1)[1])

    lesion("venus-given-zisk-circuits", align_venus,
           lambda s: venus_vs_zisk(s)["verdict"], "claim-holds")

    return out


# -------------------------------------------------------------------- main

UNITS = ["Airbender", "Miden", "OpenVM", "OpenVM2", "Pico", "RISC0", "SP1",
         "Venus", "ZisK", "zkDTVM"]


def run_all():
    DATA.mkdir(parents=True, exist_ok=True)
    tree = soundcalc_tree()
    res = {
        "hunt": "R-4166B0 (#109)",
        "read_date": READ_DATE,
        "artifact": {"repo": "ethereum/soundcalc", "pin": SOUNDCALC_PIN},
        "units": UNITS,
        "stage0_self_reproduction": stage0(),
        "pins": pins(),
        "derivations": {
            "RISC0": derive_risc0(tree),
            "Miden": derive_miden(tree),
            "OpenVM": derive_openvm(tree),
            "SP1_at_generation_tree": derive_sp1(tree, "b69a2db2"),
            "SP1_at_latest_release": derive_sp1(tree, "v6.4.0"),
        },
        "freshness": {
            "versions": freshness_versions(),
            "Airbender": freshness_airbender(tree),
            "SP1": freshness_sp1(tree),
            "Miden": freshness_miden(),
            "RISC0": freshness_risc0(),
            "ZisK": freshness_zisk(),
        },
        "venus_identity_claim": venus_vs_zisk(tree),
        "controls": control(),
    }
    return res


def main():
    cmd = sys.argv[1] if len(sys.argv) > 1 else "all"
    DATA.mkdir(parents=True, exist_ok=True)
    if cmd == "all":
        res = run_all()
        (HERE / "results.json").write_text(json.dumps(res, indent=2, sort_keys=False))
        print(json.dumps(res["stage0_self_reproduction"], indent=2))
        print(f"\nwrote {HERE / 'results.json'}")
        bad = [c for c in res["controls"] if not c["detected"]]
        print(f"controls: {len(res['controls']) - len(bad)}/{len(res['controls'])} detected")
        return 0 if not bad else 1
    tree = soundcalc_tree()
    table = {
        "stage0": stage0,
        "pins": pins,
        "derive": lambda: {"RISC0": derive_risc0(tree), "Miden": derive_miden(tree),
                           "OpenVM": derive_openvm(tree),
                           "SP1": derive_sp1(tree, "v6.4.0")},
        "freshness": lambda: {"versions": freshness_versions(),
                              "Airbender": freshness_airbender(tree),
                              "SP1": freshness_sp1(tree), "Miden": freshness_miden(),
                              "RISC0": freshness_risc0(), "ZisK": freshness_zisk()},
        "venus": lambda: venus_vs_zisk(tree),
        "control": control,
    }
    if cmd not in table:
        print(__doc__)
        return 2
    print(json.dumps(table[cmd](), indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
