#!/usr/bin/env python3
"""Hunt R-0DFB8D / #108 -- recount SWE-bench Verified leaderboard entries from
their own archived per-instance logs.

Two verdicts per unit, never merged:

  RECOUNT (class A)          count of resolved==true across the archived
                             per-instance report.json files, against the
                             entry's published results/results.json.
  SELF-CONSISTENCY (class B) does each per-instance `resolved` follow from the
                             tests_status recorded in the same file?

Nothing here judges a patch, a team, an agent or a model. It reads one archive
against itself.

Sources, all read-only and pinned:
  * repository  SWE-bench/experiments at EXPERIMENTS_COMMIT (raw.githubusercontent)
  * logs        s3://swe-bench-submissions, anonymous HTTPS GET
  * split       princeton-nlp/SWE-bench_Verified, parquet at DATASET_SHA

Stages:
  survey   fetch metadata.yaml + results/results.json for all 134 entries
  split    fetch the 500 Verified instance ids
  fetch    fetch per-instance report.json for the selected units
  analyse  recount, reconcile, re-derive; write results.json + fetch manifest

Usage:
  python probe.py all            # everything, ~15 min cold, cached afterwards
  python probe.py survey|split|fetch|analyse
"""

from __future__ import annotations

import concurrent.futures as cf
import hashlib
import io
import json
import os
import sys
import urllib.request
import urllib.error
import urllib.parse
from pathlib import Path

HERE = Path(__file__).resolve().parent
DATA = HERE / "data"
CACHE = DATA / "cache"

# --- pins ------------------------------------------------------------------
EXPERIMENTS_COMMIT = "1faa91cade0562ba62b66c1c99e71f7b72d96f13"  # read 2026-08-24
DATASET_SHA = "c104f840cc67f8b6eec6f759ebc8b2693d585d4a"  # princeton-nlp/SWE-bench_Verified
BUCKET = "https://swe-bench-submissions.s3.amazonaws.com"
RAW = f"https://raw.githubusercontent.com/SWE-bench/experiments/{EXPERIMENTS_COMMIT}"
API = "https://api.github.com/repos/SWE-bench/experiments"
SPLIT_PARQUET = (
    "https://huggingface.co/api/datasets/princeton-nlp/SWE-bench_Verified"
    f"/parquet/default/test/0.parquet"
)

# The six phase-one units: three maintainer-checked, three not, spread by date.
# Chosen by survey.py output, recorded here so the run is reproducible.
UNITS_FILE = DATA / "units.json"

WORKERS = 16
TIMEOUT = 60


# --- plumbing --------------------------------------------------------------
def _get(url: str, *, cache_key: str | None = None, allow_404: bool = False):
    """GET a URL, returning (status, body_bytes, headers). Cached on disk."""
    if cache_key:
        blob = CACHE / cache_key
        meta = CACHE / (cache_key + ".meta.json")
        if blob.exists() and meta.exists():
            m = json.loads(meta.read_text())
            return m["status"], blob.read_bytes(), m["headers"]
    req = urllib.request.Request(url, headers={"User-Agent": "zeta-lab-hunt-r0dfb8d"})
    tok = os.environ.get("GITHUB_TOKEN")
    if tok and url.startswith(API):
        req.add_header("Authorization", f"Bearer {tok}")
    try:
        with urllib.request.urlopen(req, timeout=TIMEOUT) as r:
            status, body, headers = r.status, r.read(), dict(r.headers)
    except urllib.error.HTTPError as e:
        if allow_404 and e.code in (403, 404):
            status, body, headers = e.code, e.read(), dict(e.headers)
        else:
            raise
    if cache_key:
        blob = CACHE / cache_key
        blob.parent.mkdir(parents=True, exist_ok=True)
        blob.write_bytes(body)
        keep = {k: headers[k] for k in ("ETag", "Content-Length", "Last-Modified") if k in headers}
        (CACHE / (cache_key + ".meta.json")).write_text(
            json.dumps({"status": status, "url": url, "headers": keep})
        )
    return status, body, headers


def s3(key: str) -> str:
    """Bucket URL for an object key. Entry names contain '+' (Skywork-SWE-32B+TTS_Bo8),
    which a bare URL treats as a space: an unencoded probe reports a 404 that is the
    probe's fault and not the archive's. Found the hard way, 2026-08-24."""
    return f"{BUCKET}/" + urllib.parse.quote(key, safe="/")


def _pmap(fn, items):
    with cf.ThreadPoolExecutor(max_workers=WORKERS) as ex:
        return list(ex.map(fn, items))


# --- stage: survey ---------------------------------------------------------
def entry_names() -> list[str]:
    _, body, _ = _get(f"{API}/git/trees/{EXPERIMENTS_COMMIT}?recursive=1", cache_key="tree.json")
    tree = json.loads(body)["tree"]
    names = sorted(
        {p.split("/")[2] for p in (t["path"] for t in tree) if p.startswith("evaluation/verified/")}
    )
    return names


def survey():
    import yaml

    names = entry_names()
    print(f"[survey] {len(names)} verified entries at {EXPERIMENTS_COMMIT[:12]}")

    def one(name):
        rec = {"entry": name}
        st, body, _ = _get(
            f"{RAW}/evaluation/verified/{name}/results/results.json",
            cache_key=f"repo/{name}/results.json",
            allow_404=True,
        )
        rec["results_status"] = st
        if st == 200:
            r = json.loads(body)
            rec["published"] = {
                k: (len(v) if isinstance(v, list) else v)
                for k, v in r.items()
            }
            rec["published_lists"] = {k: v for k, v in r.items() if isinstance(v, list)}
        meta = None
        for fn in ("metadata.yaml", "metadata.yml"):
            st2, body2, _ = _get(
                f"{RAW}/evaluation/verified/{name}/{fn}",
                cache_key=f"repo/{name}/{fn}",
                allow_404=True,
            )
            if st2 == 200:
                meta = yaml.safe_load(body2)
                rec["metadata_file"] = fn
                break
        rec["metadata_present"] = meta is not None
        if isinstance(meta, dict):
            tags = meta.get("tags") or {}
            rec["checked"] = tags.get("checked", None) if isinstance(tags, dict) else None
            rec["checked_key_present"] = isinstance(tags, dict) and "checked" in tags
            rec["metadata_keys"] = sorted(meta.keys())
            rec["metadata_text"] = body2.decode("utf-8", "replace")
        else:
            rec["checked"] = None
            rec["checked_key_present"] = False
            rec["metadata_keys"] = []
            rec["metadata_text"] = ""
        st3, body3, _ = _get(
            f"{RAW}/evaluation/verified/{name}/README.md",
            cache_key=f"repo/{name}/README.md",
            allow_404=True,
        )
        rec["readme_text"] = body3.decode("utf-8", "replace") if st3 == 200 else ""
        return rec

    rows = _pmap(one, names)
    DATA.mkdir(parents=True, exist_ok=True)
    (DATA / "survey.json").write_text(json.dumps(rows, indent=1))
    n_true = sum(1 for r in rows if r["checked"] is True)
    n_false = sum(1 for r in rows if r["checked"] is False)
    n_absent = sum(1 for r in rows if not r["checked_key_present"])
    print(f"[survey] tags.checked  true={n_true} false={n_false} absent={n_absent}")
    return rows


# --- stage: split ----------------------------------------------------------
def split():
    import pyarrow.parquet as pq

    _, body, _ = _get(SPLIT_PARQUET, cache_key="split/verified_test_0.parquet")
    tbl = pq.read_table(io.BytesIO(body), columns=["instance_id", "FAIL_TO_PASS", "PASS_TO_PASS"])
    ids = [str(x) for x in tbl.column("instance_id").to_pylist()]
    f2p = [json.loads(x) for x in tbl.column("FAIL_TO_PASS").to_pylist()]
    p2p = [json.loads(x) for x in tbl.column("PASS_TO_PASS").to_pylist()]
    out = {
        "dataset": "princeton-nlp/SWE-bench_Verified",
        "sha": DATASET_SHA,
        "n": len(ids),
        "sha256_of_sorted_ids": hashlib.sha256("\n".join(sorted(ids)).encode()).hexdigest(),
        "instance_ids": ids,
        "expected_tests": {i: {"FAIL_TO_PASS": a, "PASS_TO_PASS": b} for i, a, b in zip(ids, f2p, p2p)},
    }
    DATA.mkdir(parents=True, exist_ok=True)
    (DATA / "split.json").write_text(json.dumps(out, indent=1))
    print(f"[split] {len(ids)} instance ids, sha256 {out['sha256_of_sorted_ids'][:16]}")
    return out


# --- stage: fetch ----------------------------------------------------------
def units(include_supplementary: bool = True) -> list[str]:
    d = json.loads(UNITS_FILE.read_text())
    return d["units"] + (d.get("supplementary", []) if include_supplementary else [])


def fetch():
    sp = json.loads((DATA / "split.json").read_text())
    ids = sp["instance_ids"]
    manifest = {}
    for u in units():
        def one(iid, u=u):
            key = f"logs/{u}/{iid}/report.json"
            st, body, hdrs = _get(s3(f"verified/{u}/logs/{iid}/report.json"),
                                  cache_key=key, allow_404=True)
            return iid, st, len(body), hdrs.get("ETag", "").strip('"')

        rows = _pmap(one, ids)
        got = sum(1 for _, st, _, _ in rows if st == 200)
        manifest[u] = {
            "bucket": BUCKET,
            "prefix": f"verified/{u}/logs/",
            "n_requested": len(ids),
            "n_200": got,
            "files": {iid: {"status": st, "bytes": nb, "etag": et} for iid, st, nb, et in rows},
        }
        print(f"[fetch] {u}: {got}/{len(ids)} report.json retrieved")
    (DATA / "fetch_manifest.json").write_text(json.dumps(manifest, indent=1))
    return manifest


# --- stage: analyse --------------------------------------------------------
def _load_report(u: str, iid: str):
    p = CACHE / f"logs/{u}/{iid}/report.json"
    if not p.exists():
        return None
    meta = json.loads((CACHE / f"logs/{u}/{iid}/report.json.meta.json").read_text())
    if meta["status"] != 200:
        return None
    try:
        return json.loads(p.read_bytes())
    except Exception:
        return "unparseable"


def _statuses(rep_body, iid):
    """Return the inner record for an instance, tolerating key shape."""
    if not isinstance(rep_body, dict):
        return None
    if iid in rep_body:
        return rep_body[iid]
    # some entries key by something else; if exactly one key, take it
    if len(rep_body) == 1:
        return next(iter(rep_body.values()))
    return None


def analyse_unit(u, s, sp, man, mutate=None):
    """One unit's two verdicts. `mutate(iid, report) -> report | None` lets the
    control stage plant a fault; None means 'this file is now absent'."""
    expected = sp["expected_tests"]
    pub = s.get("published", {})
    pub_lists = s.get("published_lists", {})

    present, missing, unparseable = [], [], []
    resolved_ids, unresolved_ids = [], []
    inconsistent = []
    extra_ids = []
    f2p_missing_from_report = []

    for iid in sp["instance_ids"]:
        rep = _load_report(u, iid)
        if mutate is not None and rep not in (None, "unparseable"):
            rep = mutate(iid, rep)
        if rep is None:
            missing.append(iid)
            continue
        if rep == "unparseable":
            unparseable.append(iid)
            continue
        present.append(iid)
        keys = list(rep.keys()) if isinstance(rep, dict) else []
        if iid not in keys:
            extra_ids.append({"instance": iid, "keys_in_file": keys})
        rec = _statuses(rep, iid)
        if not isinstance(rec, dict):
            unparseable.append(iid)
            continue
        claimed = bool(rec.get("resolved"))
        (resolved_ids if claimed else unresolved_ids).append(iid)

        ts = rec.get("tests_status") or {}
        f2p = ts.get("FAIL_TO_PASS") or {}
        p2p = ts.get("PASS_TO_PASS") or {}
        f2p_s, f2p_f = set(f2p.get("success") or []), set(f2p.get("failure") or [])
        p2p_s, p2p_f = set(p2p.get("success") or []), set(p2p.get("failure") or [])
        # class B: does `resolved` follow from the file's own tests_status,
        # against the split's declared required tests?
        want_f2p = set(expected[iid]["FAIL_TO_PASS"])
        want_p2p = set(expected[iid]["PASS_TO_PASS"])
        derived = (
            not f2p_f
            and not p2p_f
            and want_f2p.issubset(f2p_s)
            and want_p2p.issubset(p2p_s)
        )
        if derived != claimed:
            inconsistent.append(
                {
                    "instance": iid,
                    "claimed_resolved": claimed,
                    "derived_resolved": derived,
                    "f2p_failures": sorted(f2p_f)[:10],
                    "p2p_failures": sorted(p2p_f)[:10],
                    "f2p_required_not_in_success": sorted(want_f2p - f2p_s)[:10],
                    "p2p_required_not_in_success": sorted(want_p2p - p2p_s)[:10],
                    "n_f2p_required_not_in_success": len(want_f2p - f2p_s),
                    "n_p2p_required_not_in_success": len(want_p2p - p2p_s),
                }
            )
        if want_f2p - (f2p_s | f2p_f):
            f2p_missing_from_report.append(iid)

    pub_resolved = pub.get("resolved")
    recount = len(resolved_ids)
    n_expected_absent = (pub.get("no_generation") or 0) + (pub.get("no_logs") or 0)
    accounted = len(missing) - n_expected_absent

    if len(present) == 0:
        verdict_a = "logs-unavailable"
    elif pub_resolved is None:
        verdict_a = "no-published-count"
    elif recount == pub_resolved:
        verdict_a = "match"
    else:
        verdict_a = "mismatch"

    if len(present) == 0:
        verdict_b = "not-run"
    else:
        verdict_b = "consistent" if not inconsistent else "inconsistent"

    pub_id_list = None
    for k in ("resolved", "resolved_ids"):
        if isinstance(pub_lists.get(k), list):
            pub_id_list = pub_lists[k]
    id_set_delta = None
    if pub_id_list is not None:
        id_set_delta = {
            "published_only": sorted(set(pub_id_list) - set(resolved_ids))[:20],
            "recount_only": sorted(set(resolved_ids) - set(pub_id_list))[:20],
            "n_published_only": len(set(pub_id_list) - set(resolved_ids)),
            "n_recount_only": len(set(resolved_ids) - set(pub_id_list)),
        }

    meta_text = (s.get("metadata_text", "") + "\n" + s.get("readme_text", "")).lower()
    harness_hint = [
        w for w in ("swebench", "sweb.eval", "harness", "docker") if w in meta_text
    ]

    return {
        "entry": u,
        "checked_flag": s["checked"],
        "checked_key_present": s["checked_key_present"],
        "published": pub,
        "recount": {
            "verdict": verdict_a,
            "resolved_recounted": recount,
            "resolved_published": pub_resolved,
            "delta": None if pub_resolved is None else recount - pub_resolved,
            "n_reports_retrieved": len(present),
            "n_reports_missing": len(missing),
            "n_unparseable": len(unparseable),
            "missing_accounted_by_no_generation_and_no_logs": accounted <= 0,
            "unaccounted_missing": accounted,
            "report_keyed_differently": extra_ids[:20],
            "published_id_set_delta": id_set_delta,
            "missing_ids": missing[:40],
        },
        "self_consistency": {
            "verdict": verdict_b,
            "n_checked": len(present),
            "n_inconsistent": len(inconsistent),
            "inconsistent": inconsistent[:50],
            "n_instances_where_required_f2p_absent_from_report": len(f2p_missing_from_report),
            "required_f2p_absent_sample": f2p_missing_from_report[:10],
        },
        "recorded_without_judgement": {
            "harness_version_stated": None,
            "harness_keyword_hits_in_metadata_or_readme": harness_hint,
            "trajs_listable": False,
            "trajs_note": (
                "anonymous ListBucket is denied on this bucket, so the presence of trajs/ "
                "can only be probed key by key, never listed"
            ),
            "n_report_files_200": man["n_200"],
        },
    }


def analyse():
    survey_rows = {r["entry"]: r for r in json.loads((DATA / "survey.json").read_text())}
    sp = json.loads((DATA / "split.json").read_text())
    manifest = json.loads((DATA / "fetch_manifest.json").read_text())

    out = {
        "hunt": "r_0dfb8d",
        "pins": {
            "experiments_commit": EXPERIMENTS_COMMIT,
            "dataset_sha": DATASET_SHA,
            "bucket": BUCKET,
            "split_ids_sha256": sp["sha256_of_sorted_ids"],
        },
        "archive_survey": {
            "n_entries": len(survey_rows),
            "checked_true": sum(1 for r in survey_rows.values() if r["checked"] is True),
            "checked_false": sum(1 for r in survey_rows.values() if r["checked"] is False),
            "checked_absent": sum(1 for r in survey_rows.values() if not r["checked_key_present"]),
            "latest_checked_true": max(
                (n for n, r in survey_rows.items() if r["checked"] is True), default=None
            ),
        },
        "units": [],
    }

    d = json.loads(UNITS_FILE.read_text())
    supp = set(d.get("supplementary", []))
    preds_rows = {}
    if (DATA / "preds.json").exists():
        preds_rows = json.loads((DATA / "preds.json").read_text())
    by_repo_rows = {}
    if (DATA / "by_repo.json").exists():
        by_repo_rows = json.loads((DATA / "by_repo.json").read_text())
    for u in units():
        row = analyse_unit(u, survey_rows[u], sp, manifest[u])
        row["preregistered"] = u not in supp
        row["absence_accounting"] = preds_rows.get(u)
        if by_repo_rows.get(u, {}).get("status") == 200:
            row["cross_check_resolved_by_repo"] = {
                k: v for k, v in by_repo_rows[u].items() if k != "rows"
            }
        out["units"].append(row)

    if (DATA / "control.json").exists():
        out["control"] = json.loads((DATA / "control.json").read_text())
    if (DATA / "availability.json").exists():
        a = json.loads((DATA / "availability.json").read_text())
        out["archive_availability"] = {k: v for k, v in a.items() if k != "rows"}
    out["archive_survey"]["checked_flag_is_a_non_boolean_string"] = sorted(
        n for n, r in survey_rows.items() if isinstance(r["checked"], str)
    )
    out["archive_survey"]["n_entries_stating_a_harness_version"] = 0
    out["archive_survey"]["harness_version_probe"] = (
        "no metadata.yaml/metadata.yml/README.md among the 134 matches "
        "/swebench[=< ]*\\d|harness version|sweb\\.eval|swebench_?version|harness[: ]+\\d/i"
    )

    (HERE / "results.json").write_text(json.dumps(out, indent=1))
    for u in out["units"]:
        print(
            f"[analyse] {u['entry']:<52} A={u['recount']['verdict']:<18}"
            f" recount={u['recount']['resolved_recounted']} published={u['recount']['resolved_published']}"
            f" | B={u['self_consistency']['verdict']} ({u['self_consistency']['n_inconsistent']})"
        )
    return out


# --- stage: by_repo --------------------------------------------------------
# results/resolved_by_repo.json is a second published artifact carrying the
# same claim at finer grain. One aggregate agreement can come from two errors
# cancelling; twelve per-repo agreements cannot, as easily.
def by_repo():
    sp = json.loads((DATA / "split.json").read_text())
    manifest = json.loads((DATA / "fetch_manifest.json").read_text())
    repo_of = {i: i.rsplit("-", 1)[0].replace("__", "/") for i in sp["instance_ids"]}
    out = {}
    for u in units():
        st, body, _ = _get(
            f"{RAW}/evaluation/verified/{u}/results/resolved_by_repo.json",
            cache_key=f"repo/{u}/resolved_by_repo.json",
            allow_404=True,
        )
        if st != 200:
            out[u] = {"status": st}
            continue
        pub = json.loads(body)
        counts, totals = {}, {}
        files = manifest[u]["files"]
        for iid in sp["instance_ids"]:
            r = repo_of[iid]
            totals[r] = totals.get(r, 0) + 1
            if files.get(iid, {}).get("status") != 200:
                continue
            rep = _load_report(u, iid)
            rec = _statuses(rep, iid) if isinstance(rep, dict) else None
            if isinstance(rec, dict) and rec.get("resolved"):
                counts[r] = counts.get(r, 0) + 1
        rows = {}
        for r in sorted(set(pub) | set(totals)):
            p = (pub.get(r) or {}).get("resolved")
            c = counts.get(r, 0)
            rows[r] = {
                "published_resolved": p,
                "recounted_resolved": c,
                "agree": p == c,
                "published_total": (pub.get(r) or {}).get("total"),
                "split_total": totals.get(r),
                "totals_agree": (pub.get(r) or {}).get("total") == totals.get(r),
            }
        out[u] = {
            "status": 200,
            "n_repos": len(rows),
            "n_repos_agreeing": sum(1 for v in rows.values() if v["agree"]),
            "n_repos_totals_agreeing": sum(1 for v in rows.values() if v["totals_agree"]),
            "rows": rows,
        }
        print(
            f"[by_repo] {u}: {out[u]['n_repos_agreeing']}/{out[u]['n_repos']} repos agree on resolved,"
            f" {out[u]['n_repos_totals_agreeing']}/{out[u]['n_repos']} on totals"
        )
    (DATA / "by_repo.json").write_text(json.dumps(out, indent=1))
    return out


# --- stage: preds ----------------------------------------------------------
# The published record accounts for absent logs with two fields, no_generation
# and no_logs. all_preds.jsonl is archived beside the logs, so which of the two
# a missing report belongs to is checkable rather than assumable.
def preds():
    sp = json.loads((DATA / "split.json").read_text())
    survey_rows = {r["entry"]: r for r in json.loads((DATA / "survey.json").read_text())}
    manifest = json.loads((DATA / "fetch_manifest.json").read_text())
    out = {}
    for u in units():
        st, body, _ = _get(s3(f"verified/{u}/all_preds.jsonl"),
                           cache_key=f"preds/{u}.jsonl", allow_404=True)
        if st != 200:
            out[u] = {"all_preds_status": st}
            print(f"[preds] {u}: all_preds.jsonl -> {st}")
            continue
        have, empty = set(), set()
        for line in body.decode("utf-8", "replace").splitlines():
            line = line.strip()
            if not line:
                continue
            r = json.loads(line)
            iid = r["instance_id"]
            have.add(iid)
            if not (r.get("model_patch") or "").strip():
                empty.add(iid)
        files = manifest[u]["files"]
        missing = [i for i in sp["instance_ids"] if files.get(i, {}).get("status") != 200]
        no_pred = [i for i in missing if i not in have]
        pred_but_no_log = [i for i in missing if i in have and i not in empty]
        empty_pred = [i for i in missing if i in empty]
        pub = survey_rows[u].get("published", {})
        out[u] = {
            "all_preds_status": 200,
            "n_predictions": len(have),
            "n_empty_patches": len(empty),
            "n_missing_reports": len(missing),
            "missing_with_no_prediction": no_pred,
            "missing_with_empty_prediction": empty_pred,
            "missing_with_nonempty_prediction": pred_but_no_log,
            "published_no_generation": pub.get("no_generation"),
            "published_no_logs": pub.get("no_logs"),
            "no_generation_reconciles": (len(no_pred) + len(empty_pred)) == (pub.get("no_generation") or 0),
            "no_logs_reconciles": len(pred_but_no_log) == (pub.get("no_logs") or 0),
        }
        print(
            f"[preds] {u}: preds={len(have)} missing_reports={len(missing)}"
            f" no_pred={len(no_pred)} empty_pred={len(empty_pred)} pred_but_no_log={len(pred_but_no_log)}"
            f" | published no_generation={pub.get('no_generation')} no_logs={pub.get('no_logs')}"
        )
    (DATA / "preds.json").write_text(json.dumps(out, indent=1))
    return out


# --- stage: control --------------------------------------------------------
# A check that cannot fail is not a check. Every fault below is planted in a
# copy of one unit's archived reports, in memory, and the stage asserts that
# the verdict it is supposed to move actually moves.
CONTROL_UNIT = "20250902_atlassian-rovo-dev"  # 500/500 reports, A=match, B=consistent


def _first(pred, sp, u):
    for iid in sp["instance_ids"]:
        rep = _load_report(u, iid)
        rec = _statuses(rep, iid) if isinstance(rep, dict) else None
        if isinstance(rec, dict) and pred(rec):
            return iid
    return None


def control():
    survey_rows = {r["entry"]: r for r in json.loads((DATA / "survey.json").read_text())}
    sp = json.loads((DATA / "split.json").read_text())
    manifest = json.loads((DATA / "fetch_manifest.json").read_text())
    u = CONTROL_UNIT
    s, man = survey_rows[u], manifest[u]

    unresolved = _first(lambda r: not r.get("resolved"), sp, u)
    resolved = _first(lambda r: r.get("resolved"), sp, u)

    def flip_to_resolved(iid, rep):
        if iid == unresolved:
            rep = json.loads(json.dumps(rep))
            _statuses(rep, iid)["resolved"] = True
        return rep

    def plant_failed_test(iid, rep):
        if iid == resolved:
            rep = json.loads(json.dumps(rep))
            rec = _statuses(rep, iid)
            rec["tests_status"]["PASS_TO_PASS"]["failure"].append("planted::test_fault")
        return rep

    def drop_required_f2p(iid, rep):
        if iid == resolved:
            rep = json.loads(json.dumps(rep))
            rec = _statuses(rep, iid)
            rec["tests_status"]["FAIL_TO_PASS"]["success"] = []
        return rep

    def delete_file(iid, rep):
        return None if iid == resolved else rep

    base = analyse_unit(u, s, sp, man)
    faults = {
        "baseline": (None, "unchanged"),
        "resolved-flipped-false-to-true": (flip_to_resolved, "A mismatch (+1) and B inconsistent"),
        "p2p-failure-planted-under-resolved-true": (plant_failed_test, "B inconsistent, A unchanged"),
        "required-f2p-successes-dropped": (drop_required_f2p, "B inconsistent, A unchanged"),
        "one-report-file-removed": (delete_file, "A recount -1 -> mismatch"),
    }
    rows = {}
    for name, (fn, expectation) in faults.items():
        r = base if fn is None else analyse_unit(u, s, sp, man, mutate=fn)
        rows[name] = {
            "expectation": expectation,
            "A_verdict": r["recount"]["verdict"],
            "A_recount": r["recount"]["resolved_recounted"],
            "A_delta_vs_published": r["recount"]["delta"],
            "B_verdict": r["self_consistency"]["verdict"],
            "B_n_inconsistent": r["self_consistency"]["n_inconsistent"],
            "n_missing": r["recount"]["n_reports_missing"],
        }
    ok = (
        rows["baseline"]["A_verdict"] == "match"
        and rows["baseline"]["B_verdict"] == "consistent"
        and rows["resolved-flipped-false-to-true"]["A_verdict"] == "mismatch"
        and rows["resolved-flipped-false-to-true"]["B_n_inconsistent"] == 1
        and rows["p2p-failure-planted-under-resolved-true"]["B_n_inconsistent"] == 1
        and rows["p2p-failure-planted-under-resolved-true"]["A_verdict"] == "match"
        and rows["required-f2p-successes-dropped"]["B_n_inconsistent"] == 1
        and rows["one-report-file-removed"]["A_verdict"] == "mismatch"
    )
    out = {
        "control_unit": u,
        "instance_flipped": unresolved,
        "instance_lesioned": resolved,
        "all_faults_detected": ok,
        "faults": rows,
    }
    (DATA / "control.json").write_text(json.dumps(out, indent=1))
    for k, v in rows.items():
        print(f"[control] {k:<45} A={v['A_verdict']:<10} B={v['B_verdict']}({v['B_n_inconsistent']})")
    print(f"[control] all planted faults detected: {ok}")
    return out


# --- stage: availability ---------------------------------------------------
# One probe key per entry across the whole archive: is the per-instance
# evidence retrievable at the documented location at all?
def availability():
    sp = json.loads((DATA / "split.json").read_text())
    probe_ids = [sp["instance_ids"][0], sp["instance_ids"][250], sp["instance_ids"][-1]]
    names = entry_names()

    def one(name):
        hits = []
        for iid in probe_ids:
            st, _, _ = _get(
                s3(f"verified/{name}/logs/{iid}/report.json"),
                cache_key=f"avail/{name}/{iid}.json",
                allow_404=True,
            )
            hits.append(st)
        st_pred, _, _ = _get(
            s3(f"verified/{name}/all_preds.jsonl"),
            cache_key=f"avail/{name}/all_preds.head",
            allow_404=True,
        )
        return {
            "entry": name,
            "probe_statuses": hits,
            "any_report_200": any(h == 200 for h in hits),
            "all_preds_200": st_pred == 200,
        }

    rows = _pmap(one, names)
    n_any = sum(1 for r in rows if r["any_report_200"])
    out = {
        "probe_instance_ids": probe_ids,
        "n_entries": len(rows),
        "n_with_at_least_one_probe_report_200": n_any,
        "n_with_no_probe_report": len(rows) - n_any,
        "entries_with_no_probe_report": [r["entry"] for r in rows if not r["any_report_200"]],
        "rows": rows,
    }
    (DATA / "availability.json").write_text(json.dumps(out, indent=1))
    print(f"[availability] {n_any}/{len(rows)} entries answer at least one of 3 probe keys")
    return out


STAGES = {
    "survey": survey,
    "split": split,
    "fetch": fetch,
    "analyse": analyse,
    "by_repo": by_repo,
    "preds": preds,
    "control": control,
    "availability": availability,
}

if __name__ == "__main__":
    what = sys.argv[1] if len(sys.argv) > 1 else "all"
    CACHE.mkdir(parents=True, exist_ok=True)
    if what == "all":
        survey()
        split()
        fetch()
        preds()
        by_repo()
        analyse()
        control()
        availability()
    else:
        STAGES[what]()
