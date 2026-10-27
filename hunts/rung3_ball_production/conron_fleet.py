#!/usr/bin/env python3
"""Hunt #145, door 1, Stage B: `con-ron --verified` over the assembled closure, site by site.

`con-ron` (a second kernel, not Lean's) declines any axiom but `propext`, `Classical.choice`
and `Quot.sound`, so the closure is cut at the 215 site theorems by abstraction, not by
axioms: the top shard holds `Rung3Glue.*`, the assembly's constants abstracted over the site
theorems (`lean/ExportShard.lean`), and each site shard holds every constant of one site with
its closure. `shard_manifest.py` hashes every declaration of every shard, and `coverage`
joins them: shared constants equal across shards, each `Rung3Glue.T.S` equal to the type of
`S` in its site shard, and the closure of the 18 final declarations, computed in the real
assembled environment, inside the union of what `con-ron` accepted.

Compute: this box exports (`phase0`, `export`, oleans on /dev/shm, the compressed shards in
a spool on disk); InstaBox VMs (primary) and Novita sandboxes (second provider) check one
shard each and are deleted when it ends. Keys are read from Infisical at call time and held
in memory only; no key goes to a VM, a file or an argv.

    conron_fleet.py build | phase0 | export | run | deadman | sweep [--delete] | status | coverage

Every long subcommand is meant to run detached (`setsid nohup`), driven by the state files
in RUN: `exports.json` (written by `phase0` and `export` only), `fleet.json` (by `run`
only), `vms.jsonl` (the VM registry, append-only) and `STOP` (stops `run`, triggers
`deadman`).
"""
from __future__ import annotations

import argparse
import concurrent.futures as cf
import hashlib
import json
import os
import shutil
import signal
import subprocess
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path

HERE = Path(__file__).resolve().parent
WT = HERE.parents[1]
LEANDIR = WT / "lean"
HOME = Path.home()
RUN = Path(os.environ.get("R3FLEET_RUN", HOME / ".cache/zeta-lab/rung3-conron-fleet-20261027"))
SPOOL, RECEIPTS, LOGS, PHASE0 = RUN / "spool", RUN / "receipts", RUN / "logs", RUN / "phase0"
MANIFESTS = RUN / "manifests"
SHM = Path("/dev/shm/r3fleet")
TC = HOME / ".elan/toolchains/leanprover--lean4---v4.35.0-rc2"
CONRON = TC / "bin" / "con-ron"
CONRON_SHA = "4e5616d94374cae37324dad2594f6230c2bb2297240249fc78ff508f3bc5acef"
EXPORTER = RUN / "build" / "exportshard"
OVERLAY = HOME / ".cache/zeta-lab/rung3-ball-production-assembly/overlay"
RH100 = HOME / ".cache/zeta-lab/rh100-out"
REPLAY = HOME / ".cache/zeta-lab/rung3-ball-production-full/receipts-replay-20261027"
REPO, RUN_ID = "teal-sea/zeta-lab", 40353536947
PACKAGES = ["Cli", "batteries", "Qq", "aesop", "proofwidgets", "importGraph", "LeanSearchClient",
            "plausible", "mathlib"]
PY = str(RUN / "nv-venv" / "bin" / "python")      # has orjson; shard_manifest.py runs under it
INFISICAL_PROJECT = "36d20a40-4684-48bb-9351-010ec83b0cd9"
LABEL = {"project": "zeta-rung3-conron"}
NAME_PREFIX = "zr3c-"
IB_TEMPLATE = "universal@2026-10-25.23"
NV_TEMPLATE = "6u3xl5rrw6n31q0ac7hb"               # zr3c-conron-2x4: base + zstd, 2 vCPU, 4096 MiB
FAULT_SITE, FAULT_BYTE = "B_right_06", 62304
FAULT_SHA_BEFORE = "82f661051bd932f2473f36f36947f7f49752dcb9e401a029228fbe9d07b1ac12"
FAULT_SHA_AFTER = "695e7e49b715451fd24d49e6ffb1ffdf5e95f6e9e411d63f82fd228cd6d7f0a1"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

# prices (USD), list: InstaBox per vCPU-hour and GiB-hour; Novita per vCPU-second and GiB-second
IB_VCPU_H, IB_GIB_H = 0.004, 0.00225
NV_VCPU_S, NV_GIB_S = 0.0000098, 0.0000032
HARD_CAP_USD = 40.0
STOP_LAUNCH_USD = 36.0          # no new VM once spent + projected reaches this
DISK_FLOOR_GB = 10.0
SPOOL_CAP_BYTES = 7 * 10**9
MEM_START_GIB, MEM_KILL_GIB = 30.0, 20.0


def utc() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def log(*a) -> None:
    print(utc(), *a, flush=True)


def load_json(p: Path, default):
    try:
        return json.loads(p.read_text())
    except FileNotFoundError:
        return default


def save_json(p: Path, obj) -> None:
    tmp = p.with_suffix(p.suffix + f".tmp{os.getpid()}")
    tmp.write_text(json.dumps(obj, indent=1, sort_keys=True) + "\n")
    os.replace(tmp, p)


def sha256(p: Path) -> str:
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 22), b""):
            h.update(chunk)
    return h.hexdigest()


def mem_available_gib() -> float:
    for line in Path("/proc/meminfo").read_text().splitlines():
        if line.startswith("MemAvailable:"):
            return int(line.split()[1]) / 2**20
    raise RuntimeError("no MemAvailable")


def disk_free_gb(p: Path = HOME) -> float:
    return shutil.disk_usage(p).free / 1e9


def spool_bytes() -> int:
    return sum(f.stat().st_size for f in SPOOL.glob("*.ndjson.zst*")) if SPOOL.exists() else 0


def load_exports() -> dict:
    """Every exported shard: `phase0.json` (the top shard) and `exports.json` (the sites)."""
    out = dict(load_json(RUN / "phase0.json", {}).get("shards", {}))
    out.update(load_json(RUN / "exports.json", {}).get("shards", {}))
    return out


def export_key(shard: str) -> str:
    """`site:X#novita` is the shard `site:X` pinned to Novita (a second run of the same file)."""
    return shard.split("#", 1)[0]


# --------------------------------------------------------------------------- keys

_keys: dict[str, tuple[float, str]] = {}
_keys_lock = threading.Lock()


def secret(name: str) -> str:
    """Read from Infisical, held in memory for five minutes; never logged or written."""
    with _keys_lock:
        t, v = _keys.get(name, (0.0, ""))
        if time.time() - t < 300 and v:
            return v
        r = subprocess.run(["infisical", "secrets", "get", name, "--projectId", INFISICAL_PROJECT,
                            "--env", "prod", "--plain", "--silent"],
                           capture_output=True, text=True, timeout=60)
        v = r.stdout.strip()
        if r.returncode != 0 or not v:
            raise RuntimeError(f"could not read the {name} key from Infisical (rc {r.returncode})")
        _keys[name] = (time.time(), v)
        return v


# --------------------------------------------------------------------------- registry

REG = RUN / "vms.jsonl"
_reg_lock = threading.Lock()


def registry_add(rec: dict) -> None:
    with _reg_lock, open(REG, "a") as f:
        f.write(json.dumps({**rec, "utc": utc()}) + "\n")
        f.flush()
        os.fsync(f.fileno())


def registry() -> dict[tuple[str, str], dict]:
    """(provider, id) -> the creation record, for every VM not recorded as deleted."""
    out: dict[tuple[str, str], dict] = {}
    if not REG.exists():
        return out
    for line in REG.read_text().splitlines():
        if not line.strip():
            continue
        r = json.loads(line)
        k = (r["provider"], r["id"])
        if r.get("event") == "deleted":
            out.pop(k, None)
        elif r.get("event", "created") == "created":
            out[k] = r
    return out


# --------------------------------------------------------------------------- InstaBox

class ApiError(Exception):
    def __init__(self, status: int, body: str):
        super().__init__(f"HTTP {status}: {body[:300]}")
        self.status, self.body = status, body


class InstaBox:
    BASE = "https://api.instabox.sh"

    def _req(self, method: str, path: str, body=None, headers=None, data=None, timeout=120,
             raw_out: Path | None = None, tries: int = 6):
        url = path if path.startswith("http") else self.BASE + path
        last = None
        for attempt in range(tries):
            h = {"X-API-Key": secret("instabox"), "Accept": "application/json"}
            h.update(headers or {})
            payload = data
            if body is not None:
                payload = json.dumps(body).encode()
                h["Content-Type"] = "application/json"
            if hasattr(payload, "seek"):
                payload.seek(0)
            req = urllib.request.Request(url, data=payload, method=method, headers=h)
            try:
                with urllib.request.urlopen(req, timeout=timeout) as r:
                    if raw_out is not None:
                        with open(raw_out, "wb") as f:
                            shutil.copyfileobj(r, f, 1 << 22)
                        return {"status": r.status}
                    txt = r.read().decode()
                    return json.loads(txt) if txt.strip() else {}
            except urllib.error.HTTPError as e:
                txt = e.read().decode(errors="replace")
                last = ApiError(e.code, txt)
                retryable = e.code in (408, 425, 429, 500, 502, 503, 504)
                try:
                    j = json.loads(txt)
                    retryable = retryable or bool(j.get("error", {}).get("retryable"))
                    wait = j.get("error", {}).get("retryAfterSeconds")
                except Exception:
                    wait = None
                if not retryable:
                    raise last
                time.sleep(min(60, wait or 5 * (attempt + 1)))
            except (urllib.error.URLError, TimeoutError, ConnectionError, OSError) as e:
                last = e
                time.sleep(5 * (attempt + 1))
        raise last if last else RuntimeError("request failed")

    def create(self, name: str, vcpus: int, mem: int, meta: dict, idem: str) -> dict:
        return self._req("POST", "/v1/machines", body={
            "name": name, "templateId": IB_TEMPLATE, "vcpus": vcpus, "memMiB": mem,
            "metadata": meta, "autoSuspendAfterSeconds": 0},
            headers={"Idempotency-Key": idem})

    def op(self, op_id: str, wait: str = "25s") -> dict:
        return self._req("GET", f"/v1/operations/{op_id}?wait={wait}", timeout=60)

    def machine(self, mid: str) -> dict | None:
        try:
            return self._req("GET", f"/v1/machines/{mid}")
        except ApiError as e:
            if e.status == 404:
                return None
            raise

    def exec(self, mid: str, cmd: str, timeout: int = 60) -> dict:
        return self._req("POST", f"/v1/machines/{mid}/exec",
                         body={"cmd": cmd, "timeoutSeconds": timeout}, timeout=timeout + 60)

    def upload(self, mid: str, remote: str, local: Path, mode: str = "0644") -> dict:
        q = urllib.parse.urlencode({"path": remote, "parents": "true", "mode": mode})
        size = local.stat().st_size
        with open(local, "rb") as f:
            return self._req("PUT", f"/v1/machines/{mid}/files?{q}", data=f,
                             headers={"Content-Type": "application/octet-stream",
                                      "Content-Length": str(size)}, timeout=1800, tries=3)

    def download(self, mid: str, remote: str, local: Path) -> None:
        q = urllib.parse.urlencode({"path": remote})
        self._req("GET", f"/v1/machines/{mid}/files/content?{q}", raw_out=local, timeout=600)

    def delete(self, mid: str) -> dict | None:
        try:
            return self._req("DELETE", f"/v1/machines/{mid}",
                             headers={"Idempotency-Key": f"zr3c-del-{mid}", "X-Confirm-Delete": mid})
        except ApiError as e:
            if e.status == 404:
                return None
            raise

    def list_mine(self) -> list[dict]:
        out, cursor = [], None
        while True:
            q = "metadata=" + urllib.parse.quote(f"project:{LABEL['project']}") + "&limit=100"
            if cursor:
                q += "&cursor=" + urllib.parse.quote(cursor)
            d = self._req("GET", f"/v1/machines?{q}")
            out += [m for m in d.get("machines", [])
                    if m.get("metadata", {}).get("project") == LABEL["project"]
                    and m.get("name", "").startswith(NAME_PREFIX)]
            cursor = d.get("nextCursor")
            if not cursor:
                return out

    def usage(self, mid: str) -> dict:
        return self._req("GET", f"/v1/machines/{mid}/usage")


# --------------------------------------------------------------------------- Novita

class Novita:
    def _sdk(self):
        from novita_sandbox.core import Sandbox
        return Sandbox

    def create(self, meta: dict, timeout_s: int):
        S = self._sdk()
        return S.create(template=NV_TEMPLATE, timeout=timeout_s, metadata=meta,
                        api_key=secret("novita"))

    def connect(self, sid: str):
        return self._sdk().connect(sid, api_key=secret("novita"))

    def run(self, sid: str, cmd: str, timeout: int = 60):
        sbx = self.connect(sid)
        return sbx.commands.run(cmd, timeout=timeout, user="root")

    def upload(self, sid: str, remote: str, local: Path) -> None:
        sbx = self.connect(sid)
        with open(local, "rb") as f:
            sbx.files.write(remote, f, user="root", request_timeout=1800)

    def read(self, sid: str, remote: str) -> bytes:
        sbx = self.connect(sid)
        return sbx.files.read(remote, format="bytes", user="root", request_timeout=600)

    def kill(self, sid: str) -> bool:
        return self._sdk().kill(sid, api_key=secret("novita"))

    def list_mine(self) -> list:
        S = self._sdk()
        try:
            from novita_sandbox.core.sandbox.sandbox_api import SandboxQuery
            pager = S.list(query=SandboxQuery(metadata=dict(LABEL)), api_key=secret("novita"))
        except Exception:
            pager = S.list(api_key=secret("novita"))
        items = []
        while pager.has_next:
            items += [s for s in pager.next_items() if (getattr(s, "metadata", None) or {}).get("project")
                      == LABEL["project"]]
        return items

    def quota(self):
        return self._sdk().get_quota(api_key=secret("novita"))


# --------------------------------------------------------------------------- sites, costs

def production():
    import importlib.util
    spec = importlib.util.spec_from_file_location("rung3_production_for_fleet", HERE / "production.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def finals(P) -> list[str]:
    return [f"ZetaLean.DH.Rung3Assembly.Plan2.{n}" for n in P.FINAL + P.STRIP]


def primes_excluding_5(t: int) -> list[int]:
    out, n = [], 2
    while len(out) < t:
        if all(n % p for p in range(2, int(n ** 0.5) + 1)) and n != 5:
            out.append(n)
        n += 1
    return out


def tower_cpu_s(p: int) -> float:
    """con-ron CPU-s for one whole-tower decision, interpolated in log p through the
    measured 16 s (p = 2), 265 s (p = 89, B_right_06), 400 s (p = 401) and 648 s (p = 1801)."""
    import math
    pts = [(2, 16.0), (89, 265.0), (401, 400.0), (1801, 648.0)]
    x = math.log(p)
    for (p0, t0), (p1, t1) in zip(pts, pts[1:]):
        if p <= p1:
            a = (x - math.log(p0)) / (math.log(p1) - math.log(p0))
            return t0 + a * (t1 - t0)
    (p0, t0), (p1, t1) = pts[-2], pts[-1]
    return t1 + (x - math.log(p1)) * (t1 - t0) / (math.log(p1) - math.log(p0))


def census_rows() -> dict[str, dict]:
    rows = [json.loads(l) for l in (REPLAY / "export-sample" / "census-215.jsonl").read_text().splitlines()]
    return {r["id"]: r for r in rows}


def projected_cpu_s(shard: str, rows: dict, scale: float) -> float:
    """con-ron CPU for one shard, before the pilot's scale: the base (about 400 CPU-s at the
    B_right_06 sample) plus the towers."""
    if shard == "top":
        return 3000.0 * scale
    sid = shard.split(":", 1)[1]
    return (400.0 + sum(tower_cpu_s(p) for p in primes_excluding_5(rows[sid]["towers"]))) * scale


# --------------------------------------------------------------------------- build

def cmd_build(_a) -> None:
    b = RUN / "build"
    b.mkdir(parents=True, exist_ok=True)
    src = HERE / "lean" / "ExportShard.lean"
    shutil.copy(src, b / "ExportShard.lean")
    env = {**os.environ, "PATH": f"{TC / 'bin'}:{os.environ['PATH']}", "LEAN_PATH": str(TC / "lib/lean")}
    subprocess.run(["lean", "-c", "ExportShard.c", "ExportShard.lean"], cwd=b, env=env, check=True)
    subprocess.run(["leanc", "-O3", "-o", "exportshard", "ExportShard.c"], cwd=b, env=env, check=True)
    rec = {"utc": utc(), "ExportShard.lean": sha256(src), "exportshard": sha256(b / "exportshard"),
           "toolchain": str(TC), "con-ron": sha256(CONRON)}
    assert rec["con-ron"] == CONRON_SHA, rec
    save_json(b / "build.json", rec)
    print(json.dumps(rec, indent=1))


# --------------------------------------------------------------------------- exports

def lean_path(*front: Path) -> str:
    ps = [OVERLAY, *front] + [LEANDIR / ".lake/packages" / p / ".lake/build/lib/lean" for p in PACKAGES]
    ps += [LEANDIR / ".lake/build/lib/lean", TC / "lib/lean"]
    return ":".join(str(p) for p in ps)


def timed(cmd: list[str], tag: str, stdout_path: Path | None, env_lp: str) -> dict:
    """One process under `nice -n 10`, `ulimit -s unlimited` and `/usr/bin/time -v`; killed
    if MemAvailable falls below MEM_KILL_GIB."""
    tfile = LOGS / f"{tag}.time"
    efile = LOGS / f"{tag}.err"
    env = {**os.environ, "PATH": f"{TC / 'bin'}:{os.environ['PATH']}", "LEAN_PATH": env_lp}
    sh = "ulimit -s unlimited; exec nice -n 10 /usr/bin/time -v -o " + _q(str(tfile)) + " " + \
         " ".join(_q(c) for c in cmd)
    t0, low = time.time(), mem_available_gib()
    out = open(stdout_path, "wb") if stdout_path else subprocess.DEVNULL
    with open(efile, "wb") as err:
        p = subprocess.Popen(["bash", "-c", sh], stdout=out, stderr=err, env=env,
                             start_new_session=True)
        killed = False
        while p.poll() is None:
            time.sleep(2)
            m = mem_available_gib()
            low = min(low, m)
            if m < MEM_KILL_GIB and not killed:
                os.killpg(p.pid, signal.SIGTERM)
                killed = True
        rc = p.wait()
    if stdout_path:
        out.close()
    txt = tfile.read_text() if tfile.exists() else ""
    import re
    rss = re.search(r"Maximum resident set size \(kbytes\): (\d+)", txt)
    cpu = sum(float(x) for x in re.findall(r"(?:User|System) time \(seconds\): ([\d.]+)", txt))
    rec = {"tag": tag, "rc": rc, "killed_by_guard": killed, "wall_s": round(time.time() - t0, 1),
           "cpu_s": round(cpu, 1), "max_rss_kib": int(rss.group(1)) if rss else None,
           "mem_available_low_gib": round(low, 1), "pid": p.pid}
    log("ran", json.dumps(rec))
    return rec


def _q(s: str) -> str:
    import shlex
    return shlex.quote(s)


def wait_for(cond, what: str, every: int = 20) -> None:
    told = False
    while not cond():
        if (RUN / "STOP").exists():
            raise SystemExit("STOP file present")
        if not told:
            log("waiting:", what)
            told = True
        time.sleep(every)


def finish_export(slug: str, nd: Path, summary_extra: dict) -> dict:
    """manifest, hash and compress one export from /dev/shm into the spool."""
    MANIFESTS.mkdir(parents=True, exist_ok=True)
    man = MANIFESTS / f"{slug}.manifest.tsv"
    r = subprocess.run([PY, "-I", str(HERE / "shard_manifest.py"), str(nd), str(man)],
                       capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError(f"manifest of {slug} failed: {r.stderr[-500:]}")
    summary = json.loads(r.stdout)
    bad = sorted(set(summary["axioms"]) - STANDARD_AXIOMS)
    if bad:
        raise RuntimeError(f"{slug}: non-standard axioms {bad}")
    nd_sha = sha256(nd)
    zst = SPOOL / f"{slug}.ndjson.zst"
    tmp = zst.with_suffix(".zst.tmp")
    subprocess.run(["zstd", "-q", "-f", "-9", "-T4", str(nd), "-o", str(tmp)], check=True)
    os.replace(tmp, zst)
    rec = {"status": "spooled", "slug": slug, "file": str(zst), "manifest": str(man),
           "sha256_ndjson": nd_sha, "sha256_zst": sha256(zst), "bytes_ndjson": nd.stat().st_size,
           "bytes_zst": zst.stat().st_size, "summary": summary, "utc": utc(), **summary_extra}
    subprocess.run(["zstd", "-q", "-f", "--rm", "-9", str(man)], check=True)
    rec["manifest"] = str(man) + ".zst"
    nd.unlink()
    return rec


def collect_zip(job: int, dest: Path, digests: dict) -> None:
    dest.mkdir(parents=True, exist_ok=True)
    listing = subprocess.run(["gh", "api", "--paginate", f"repos/{REPO}/actions/runs/{RUN_ID}/artifacts",
                              "--jq", ".artifacts[] | tojson"], check=True, capture_output=True, text=True)
    arts = [json.loads(l) for l in listing.stdout.splitlines() if l]
    a = [x for x in arts if x["name"] == f"rung3-production-job{job}-attempt1"]
    assert len(a) == 1 and not a[0]["expired"], (job, a)
    a = a[0]
    z = dest / "job.zip"
    with open(z, "wb") as f:
        subprocess.run(["gh", "api", f"repos/{REPO}/actions/artifacts/{a['id']}/zip"], check=True, stdout=f)
    h = sha256(z)
    assert a["digest"] == f"sha256:{h}", (job, a["digest"], h)
    assert digests[job] == h, (job, "differs from the first collect's digest")
    subprocess.run(["unzip", "-q", "-o", str(z), "-d", str(dest / "x")], check=True)
    z.unlink()


def first_digests() -> dict[int, str]:
    d = load_json(REPLAY / "collected.json", None)
    return {r["job"]: r["sha256"] for r in d["artifacts"]}


def cmd_phase0(_a) -> None:
    """Everything that needs all 215 sites at once, on /dev/shm, then cleared."""
    P = production()
    for d in (SPOOL, LOGS, PHASE0):
        d.mkdir(parents=True, exist_ok=True)
    ex = load_json(RUN / "phase0.json", {"shards": {}, "phase0": {}})
    full = SHM / "full"
    wait_for(lambda: mem_available_gib() > 45 and disk_free_gb() > DISK_FLOOR_GB + 2, "memory/disk for phase0")
    ph = ex.setdefault("phase0", {})
    if not ph.get("collected"):
        shutil.rmtree(full, ignore_errors=True)
        req = REPLAY / "RUN_REQUEST.full.json"
        r = subprocess.run([sys.executable, str(HERE / "production.py"), "collect", "--request", str(req),
                            "--run", str(RUN_ID), "--dest", str(full)], capture_output=True, text=True)
        (LOGS / "phase0-collect.log").write_text(r.stdout + r.stderr)
        assert r.returncode == 0, r.stderr[-1000:]
        got = json.loads((full / "collected.json").read_text())
        want = first_digests()
        assert {a["job"]: a["sha256"] for a in got["artifacts"]} == want
        # the 215 root oleans against the first receipts
        roots = {}
        for line in (REPLAY / "site-root-oleans.sha256").read_text().splitlines():
            h, p = line.split(None, 1)
            roots[Path(p).name] = h
        for name, h in roots.items():
            assert sha256(full / "out" / name) == h, name
        ph["collected"] = {"utc": utc(), "artifacts": got["artifacts"], "root_oleans_checked": len(roots)}
        save_json(RUN / "phase0.json", ex)
    if not ph.get("assembled"):
        env = {**os.environ, "PATH": f"{HOME / '.elan/bin'}:{os.environ['PATH']}"}
        r = subprocess.run(["bash", "-c", "ulimit -s unlimited; exec \"$@\"", "assemble",
                            sys.executable, str(HERE / "production.py"), "assemble", "--dest", str(full),
                            "--overlay", str(OVERLAY), "--rh100", str(RH100)],
                           capture_output=True, text=True, env=env)
        (LOGS / "phase0-assemble.log").write_text(r.stdout + r.stderr)
        assert r.returncode == 0, r.stderr[-2000:]
        want = {}
        for line in (REPLAY / "assembly-oleans.sha256").read_text().splitlines():
            h, p = line.split(None, 1)
            want[p.lstrip("./")] = h
        got = {p: sha256(full / "asm" / p) for p in want}
        assert got == want, {p: (got[p], want[p]) for p in want if got[p] != want[p]}
        keep = RUN / "asm"
        shutil.rmtree(keep, ignore_errors=True)
        shutil.copytree(full / "asm", keep)
        shutil.copy(full / "assemble.json", PHASE0 / "assemble.json")
        ph["assembled"] = {"utc": utc(), "assembly_oleans_equal_to_receipts": sorted(want)}
        save_json(RUN / "phase0.json", ex)
    lp = lean_path(full / "asm", full / "out", RH100)
    (PHASE0 / "lean-path.txt").write_text(lp + "\n")
    fin = finals(P)
    if not ph.get("census"):
        rec = timed([str(EXPORTER), "census", "Rung3Assembly.Final", str(PHASE0 / "census.tsv")],
                    "phase0-census", None, lp)
        assert rec["rc"] == 0, rec
        subprocess.run(["zstd", "-q", "-f", "--rm", "-9", str(PHASE0 / "census.tsv")], check=True)
        ph["census"] = rec
        save_json(RUN / "phase0.json", ex)
    if not ph.get("closure"):
        rec = timed([str(EXPORTER), "closure", "Rung3Assembly.Final", str(PHASE0 / "closure18.txt"), *fin],
                    "phase0-closure", None, lp)
        assert rec["rc"] == 0, rec
        subprocess.run(["zstd", "-q", "-f", "--rm", "-9", str(PHASE0 / "closure18.txt")], check=True)
        ph["closure"] = rec
        save_json(RUN / "phase0.json", ex)
    if ex["shards"].get("top", {}).get("status") is None:
        tmpd = SHM / "tmp"
        tmpd.mkdir(parents=True, exist_ok=True)
        nd = tmpd / "top.ndjson"
        rec = timed([str(EXPORTER), "top", "Rung3Assembly.Final", str(PHASE0 / "top-info.json"), *fin],
                    "phase0-top", nd, lp)
        assert rec["rc"] == 0, rec
        ex["shards"]["top"] = finish_export("top", nd, {"export": rec})
        save_json(RUN / "phase0.json", ex)
    shutil.rmtree(full, ignore_errors=True)
    ph["cleared_shm"] = utc()
    save_json(RUN / "phase0.json", ex)
    log("phase0 done")


def plant_fault(src_out: Path, dest: Path) -> dict:
    """A scratch tree for the fault shard: links to the site's oleans, and a copy of
    `CB_right_06/Primes.olean` with the radius of `Prime_B_right_06_2.Sq_10` one unit low."""
    shutil.rmtree(dest, ignore_errors=True)
    (dest / f"C{FAULT_SITE}").mkdir(parents=True)
    os.symlink(src_out / f"C{FAULT_SITE}.olean", dest / f"C{FAULT_SITE}.olean")
    for f in (src_out / f"C{FAULT_SITE}").iterdir():
        if f.name != "Primes.olean":
            os.symlink(f, dest / f"C{FAULT_SITE}" / f.name)
    prim = dest / f"C{FAULT_SITE}" / "Primes.olean"
    shutil.copy(src_out / f"C{FAULT_SITE}" / "Primes.olean", prim)
    assert sha256(prim) == FAULT_SHA_BEFORE
    old = (2 * 36391283805789411 + 1).to_bytes(8, "little")
    new = (2 * 36391283805789410 + 1).to_bytes(8, "little")
    data = bytearray(prim.read_bytes())
    assert data.count(old) == 1, data.count(old)
    i = data.index(old)
    diff = [k for k in range(8) if old[k] != new[k]]
    assert i + diff[0] == FAULT_BYTE and len(diff) == 1, (i, diff)
    data[i:i + 8] = new
    prim.write_bytes(bytes(data))
    assert sha256(prim) == FAULT_SHA_AFTER
    return {"byte": FAULT_BYTE, "sha256_before": FAULT_SHA_BEFORE, "sha256_after": FAULT_SHA_AFTER}


def manifest_diff(clean: Path, fault: Path) -> dict:
    """The declarations whose Merkle hash differs between two manifests of the same names."""
    def rows(p):
        return {l.split("\t")[0]: l.split("\t")[2] for l in read_zst_lines(p)}
    a, b = rows(clean), rows(fault)
    return {"changed": sorted(n for n in a if n in b and a[n] != b[n]),
            "only_clean": sorted(set(a) - set(b)), "only_fault": sorted(set(b) - set(a)),
            "declarations": len(a)}


def manifest_path(key: str) -> Path:
    return MANIFESTS / f"{key.replace(':', '-')}.manifest.tsv.zst"


def manifest_has_kernel_hashes(key: str) -> bool:
    p = manifest_path(key)
    if not p.exists():
        return False
    r = subprocess.run(f"zstd -dc {_q(str(p))} | head -n 1", shell=True, capture_output=True, text=True)
    return len(r.stdout.rstrip("\n").split("\t")) == 8


def remanifest_one(key: str, nd: Path, want_sha: str) -> dict:
    got = sha256(nd)
    if got != want_sha:
        raise RuntimeError(f"{key}: the export hashes {got}, not the recorded {want_sha}")
    tmp = MANIFESTS / f"{key.replace(':', '-')}.manifest.tsv.new"
    r = subprocess.run([PY, "-I", str(HERE / "shard_manifest.py"), str(nd), str(tmp)],
                       capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError(f"manifest of {key} failed: {r.stderr[-500:]}")
    subprocess.run(["zstd", "-q", "-f", "--rm", "-9", str(tmp), "-o", str(tmp) + ".zst"], check=True)
    os.replace(str(tmp) + ".zst", manifest_path(key))
    return json.loads(r.stdout)


def cmd_remanifest(a) -> None:
    """Rewrites every manifest written before the kernel hashes existed: from the spooled
    export when it is still there, else by exporting the site again from its zip; either
    way the export must hash as the one `con-ron` checked."""
    P = production()
    st = load_json(RUN / "remanifest.json", {"done": {}})
    jobs = P.assign(20)
    job_of = {f"site:{sid}": j for j, ids in enumerate(jobs) for sid in ids}
    job_of["fault:" + FAULT_SITE] = job_of["site:" + FAULT_SITE]
    tmpd = SHM / "remani"
    tmpd.mkdir(parents=True, exist_ok=True)
    while True:
        ex = load_exports()
        todo = [k for k, e in ex.items() if e.get("status") and not manifest_has_kernel_hashes(k)]
        if not todo:
            break
        from_spool = [k for k in todo if Path(ex[k]["file"]).exists()]
        lock = threading.Lock()

        def spool_one(k: str) -> None:
            nd = tmpd / f"{k.replace(':', '-')}.ndjson"
            with open(nd, "wb") as f:
                subprocess.run(["zstd", "-dc", "-q", ex[k]["file"]], stdout=f, check=True)
            summ = remanifest_one(k, nd, ex[k]["sha256_ndjson"])
            nd.unlink()
            with lock:
                st["done"][k] = {"from": "spool", "utc": utc(), "summary": summ}
                save_json(RUN / "remanifest.json", st)
            log("remanifest from spool", k)
        with cf.ThreadPoolExecutor(max_workers=a.workers) as pool:
            for f in [pool.submit(spool_one, k) for k in from_spool]:
                f.result()
        rest = [k for k in todo if k not in from_spool]
        by_job: dict[int, list[str]] = {}
        for k in rest:
            by_job.setdefault(job_of[k], []).append(k)
        for job, keys in sorted(by_job.items()):
            zdir = SHM / f"remani-zip{job}"
            wait_for(lambda: mem_available_gib() > MEM_START_GIB, f"memory for zip {job}")
            shutil.rmtree(zdir, ignore_errors=True)
            collect_zip(job, zdir, first_digests())
            out = zdir / "x" / "out"
            for k in keys:
                if Path(load_exports()[k]["file"]).exists() or manifest_has_kernel_hashes(k):
                    continue
                sid = k.split(":", 1)[1]
                nd = tmpd / f"{k.replace(':', '-')}.ndjson"
                elp = lean_path(out)
                if k.startswith("fault:"):
                    plant_fault(out, SHM / "remani-fault")
                    elp = lean_path(SHM / "remani-fault", out)
                rec = timed([str(EXPORTER), "site", sid], f"reexport-{k.replace(':', '-')}", nd, elp)
                if rec["rc"] != 0:
                    raise RuntimeError(f"re-export of {k} failed: {rec}")
                st["done"][k] = {"from": "re-export", "utc": utc(), "export": rec,
                                 "summary": remanifest_one(k, nd, ex[k]["sha256_ndjson"])}
                nd.unlink()
                save_json(RUN / "remanifest.json", st)
                log("remanifest by re-export", k)
            shutil.rmtree(zdir, ignore_errors=True)
            shutil.rmtree(SHM / "remani-fault", ignore_errors=True)
        if not a.wait:
            break
        time.sleep(60)
    log("remanifest done")


def one_line_diff(a: Path, b: Path) -> list:
    out = []
    with open(a, "rb") as fa, open(b, "rb") as fb:
        for n, (x, y) in enumerate(zip(fa, fb), 1):
            if x != y:
                out.append([n, x.decode()[:200], y.decode()[:200]])
                if len(out) > 5:
                    break
    return out


def cmd_export(a) -> None:
    """Per-zip streaming: one artifact on /dev/shm at a time; each site's shard into the spool."""
    P = production()
    rows = census_rows()
    for d in (SPOOL, LOGS):
        d.mkdir(parents=True, exist_ok=True)
    jobs = P.assign(20)
    order = [0, 11] + [j for j in range(20) if j not in (0, 11)]
    if a.jobs:
        order = [int(x) for x in a.jobs.split(",")]
    digests = first_digests()
    lock, stagger = threading.Lock(), threading.Lock()

    def save(ex):
        with lock:
            save_json(RUN / "exports.json", ex)

    for job in order:
        ex = load_json(RUN / "exports.json", {"zips": {}, "shards": {}, "phase0": {}})
        sites = sorted(jobs[job], key=lambda s: -projected_cpu_s(f"site:{s}", rows, 1.0))
        want = [f"site:{s}" for s in sites] + (["fault:" + FAULT_SITE] if job == 11 else [])
        if all(ex["shards"].get(w, {}).get("status") for w in want):
            continue
        wait_for(lambda: disk_free_gb() > DISK_FLOOR_GB + 1.5, f"disk for job {job}")
        zdir = SHM / f"zip{job}"
        if not (zdir / "x" / "out").is_dir() or not ex["zips"].get(str(job), {}).get("unzipped"):
            shutil.rmtree(zdir, ignore_errors=True)
            t0 = time.time()
            collect_zip(job, zdir, digests)
            ex["zips"][str(job)] = {"unzipped": utc(), "sha256": digests[job], "wall_s": round(time.time() - t0, 1)}
            save(ex)
        out = zdir / "x" / "out"
        lp = lean_path(out)
        tmpd = SHM / "tmp"
        tmpd.mkdir(parents=True, exist_ok=True)

        def one(shard: str) -> None:
            slug = shard.replace(":", "-")
            sid = shard.split(":", 1)[1]
            est = 3 * 10**8 if shard != "site:centre" else 2 * 10**9
            wait_for(lambda: spool_bytes() + est < SPOOL_CAP_BYTES and
                     disk_free_gb() - est / 1e9 > DISK_FLOOR_GB + 1, f"spool room for {shard}")
            nd = tmpd / f"{slug}.ndjson"
            extra = {}
            if shard.startswith("fault:"):
                fdir = SHM / "fault"
                extra["plant"] = plant_fault(out, fdir)
                elp = lean_path(fdir, out)
            else:
                elp = lp
            for attempt in range(3):
                with stagger:
                    wait_for(lambda: mem_available_gib() > MEM_START_GIB, f"memory for {shard}")
                    time.sleep(3)      # stagger the imports
                rec = timed([str(EXPORTER), "site", sid], f"export-{slug}", nd, elp)
                if rec["rc"] == 0:
                    break
                log("export failed, retrying", shard, json.dumps(rec))
                time.sleep(60)
            if rec["rc"] != 0:
                raise RuntimeError(f"export of {shard} failed: {rec}")
            extra["export"] = rec
            extra["site_constants_line"] = (LOGS / f"export-{slug}.err").read_text()[-2000:]
            if shard.startswith("fault:"):
                clean = tmpd / f"site-{sid}.clean.ndjson"
                if not clean.exists():      # a resumed run: export the clean site again, unspooled
                    rc2 = timed([str(EXPORTER), "site", sid], f"export-{slug}-clean-again", clean, lp)
                    assert rc2["rc"] == 0, rc2
                # the first differing line is the planted literal; later lines shift because
                # the unchanged literal, used elsewhere in the site, is then written anew
                d = one_line_diff(clean, nd)
                assert "36391283805789410" in d[0][2] and "36391283805789411" in d[0][1], d[:1]
                extra["first_difference"] = d[0]
            if shard == f"site:{FAULT_SITE}":
                shutil.copy(nd, tmpd / f"site-{sid}.clean.ndjson")
            r = finish_export(slug, nd, extra)
            if shard.startswith("fault:"):
                r["manifest_diff"] = manifest_diff(MANIFESTS / f"site-{sid}.manifest.tsv.zst",
                                                   Path(r["manifest"]))
                names = r["manifest_diff"]["changed"]
                assert f"ZetaLean.DH.Cert.Prime_{sid}_2.Sq_10" in names and \
                    not r["manifest_diff"]["only_clean"] and not r["manifest_diff"]["only_fault"], r["manifest_diff"]
            with lock:
                ex["shards"][shard] = r
            save(ex)
            log("spooled", shard, r["bytes_ndjson"], r["bytes_zst"])

        todo = [s for s in want if not ex["shards"].get(s, {}).get("status")]
        clean_first = [s for s in todo if not s.startswith("fault:")]
        with cf.ThreadPoolExecutor(max_workers=a.workers) as pool:
            for f in [pool.submit(one, s) for s in clean_first]:
                f.result()
        for s in todo:
            if s.startswith("fault:"):
                one(s)
        shutil.rmtree(zdir, ignore_errors=True)
        shutil.rmtree(SHM / "fault", ignore_errors=True)
        for f in tmpd.glob("*.clean.ndjson"):
            f.unlink()
        ex["zips"][str(job)]["done"] = utc()
        save(ex)
    log("export done")


# --------------------------------------------------------------------------- the fleet

def conron_count(ex: dict) -> int:
    """What `con-ron` reports as accepted: one per declaration record of the stream (an
    inductive block counts once), less the four `quot` records it installs as built-ins.
    Measured on the pilot's `site:B_right_06`: 62,009 records, 4 of them `quot`, accepted
    62,005."""
    rec = ex["summary"].get("records")
    if rec is None:          # a manifest written before the record count: count the stream
        out = subprocess.run(f"zstd -dc {_q(ex['file'])} | grep -oE '^\\{{\"(axiom|def|thm|opaque|quot|inductive)\"' "
                             "| sort | uniq -c", shell=True, capture_output=True, text=True, check=True).stdout
        rec = {l.split()[1].strip('{"'): int(l.split()[0]) for l in out.splitlines() if l.strip()}
        ex["summary"]["records"] = rec
    return sum(v for k, v in rec.items() if k != "quot")


PROVISION_TIMEOUT_S = 1800
DONE_STATES = ("done", "review", "failed", "failed_provision")


def slug_of(shard: str) -> str:
    return shard.replace(":", "-").replace("#", "@")


class Fleet:
    def __init__(self, args):
        self.args = args
        self.ib, self.nv = InstaBox(), Novita()
        self.state = load_json(RUN / "fleet.json", {"shards": {}})
        self.lock = threading.Lock()
        self.pool = cf.ThreadPoolExecutor(max_workers=args.workers)
        self.busy: dict[str, cf.Future] = {}
        self.rows = census_rows()
        self.term = False      # SIGTERM drains: finish what is in flight, launch nothing
        signal.signal(signal.SIGTERM, lambda *_: setattr(self, "term", True))
        # a restart loses the threads: a VM caught mid-provisioning is deleted and redone
        for name, s in self.state["shards"].items():
            act = s.pop("action", None)
            if s["state"] == "provisioning" or act == "provision":
                vm = (s.get("vms") or [{}])[-1]
                s["state"] = "destroy_then_retry" if vm.get("id") and not vm.get("deleted_epoch") else "ready"
                if not vm.get("id") and s.get("vms"):
                    s["vms"].pop()
            if s["state"] == "review" and (RECEIPTS / slug_of(name) / "receipt.json").exists():
                v = self.verify(name)
                if v["ok"]:
                    s.setdefault("verdicts", []).append(v)
                    s["verdict"] = v
                    s["state"] = "done"
                    s["history"].append({"utc": utc(), "what": "re-verified from its receipt", "ok": True})
            if act == "destroy" and s.get("after_destroy"):
                s["state"] = {"done": "destroy_then_done", "ready": "destroy_then_retry",
                              "review": "destroy_then_review", "failed": "destroy_then_fail"}.get(
                    s["after_destroy"], "destroy_then_retry")

    # -- state
    def save(self) -> None:
        with self.lock:
            save_json(RUN / "fleet.json", self.state)

    def sh(self, shard: str) -> dict:
        return self.state["shards"].setdefault(shard, {"state": "waiting", "attempt": 0, "history": []})

    def note(self, shard: str, what: str, **kw) -> None:
        s = self.sh(shard)
        s["history"].append({"utc": utc(), "what": what, **kw})
        log(shard, what, json.dumps(kw)[:400] if kw else "")

    # -- cost
    @staticmethod
    def rate_per_s(spec: dict) -> float:
        if spec.get("provider") == "novita":
            return spec["vcpus"] * NV_VCPU_S + spec["mem_gib"] * NV_GIB_S
        return (spec.get("vcpus", 8) * IB_VCPU_H + spec.get("mem_gib", 16) * IB_GIB_H) / 3600

    def spent_usd(self) -> dict:
        out = {"instabox": 0.0, "novita": 0.0}
        now = time.time()
        for s in self.state["shards"].values():
            for vm in s.get("vms", []):
                t1 = vm.get("deleted_epoch") or now
                out[vm["provider"]] += max(0.0, t1 - vm["created_epoch"]) * self.rate_per_s(vm)
        return out

    def projected_usd(self) -> float:
        scale = self.state.get("scale", 1.0)
        total = sum(self.spent_usd().values())
        for name, s in self.state["shards"].items():
            if s["state"] in DONE_STATES:
                continue
            cpu = projected_cpu_s(export_key(name), self.rows, scale)
            spec = s.get("spec") or ({"provider": "novita", "vcpus": 2, "mem_gib": 4} if name.endswith("#novita")
                                     else {"provider": "instabox", "vcpus": 8, "mem_gib": 16})
            wall = cpu / spec["vcpus"] / 0.8 + 600
            if s["state"] == "running" and s.get("started_epoch"):
                wall = max(0.0, wall - (time.time() - s["started_epoch"]))
            total += wall * self.rate_per_s(spec)
        return total

    # -- choose a provider
    def choose(self, shard: str) -> dict | None:
        a = self.args
        live = [s for s in self.state["shards"].values()
                if s.get("vms") and not s["vms"][-1].get("deleted_epoch") and s["state"] not in DONE_STATES]
        nv_live = sum(1 for s in live if s["vms"][-1]["provider"] == "novita")
        ib_live = len(live) - nv_live
        if shard.endswith("#novita"):
            return {"provider": "novita", "vcpus": 2, "mem_gib": 4} if nv_live < a.novita_max else None
        if (a.novita and nv_live < a.novita_max and shard in self.state.get("novita_shards", [])
                and self.sh(shard).get("novita_attempts", 0) < 1):
            return {"provider": "novita", "vcpus": 2, "mem_gib": 4}
        if ib_live < a.instabox_max:
            return {"provider": "instabox", "vcpus": 8, "mem_gib": 16}
        return None

    # -- actions, in worker threads; the only state they write is vm["id"], under the lock
    def act_provision(self, shard: str, spec: dict, attempt: int, vm: dict) -> dict:
        ex = load_exports()[export_key(shard)]
        slug = slug_of(shard)
        name = f"{NAME_PREFIX}{slug.lower().replace('_', '-').replace('@', '-')}-a{attempt}"[:63]
        job = {"shard": export_key(shard), "sha256_conron": CONRON_SHA, "sha256_zst": ex["sha256_zst"],
               "sha256_ndjson": ex["sha256_ndjson"], "jobs": spec["vcpus"]}
        jfile = RUN / "work" / f"{slug}.job.json"
        jfile.parent.mkdir(parents=True, exist_ok=True)
        jfile.write_text(json.dumps(job, indent=1) + "\n")
        zst = Path(ex["file"])
        res = {"name": name}
        t0 = time.time()
        if spec["provider"] == "instabox":
            op = self.ib.create(name, spec["vcpus"], spec["mem_gib"] * 1024,
                                {**LABEL, "shard": slug[:60], "run": "20261027"},
                                idem=f"zr3c-create-{slug}-a{attempt}")
            mid = op["machineId"]
            with self.lock:
                vm["id"] = mid
            registry_add({"provider": "instabox", "id": mid, "name": name, "shard": shard,
                          "event": "created", "vcpus": spec["vcpus"], "mem_gib": spec["mem_gib"]})
            while True:
                o = self.ib.op(op["id"])
                if o["state"] == "succeeded":
                    break
                if o["state"] == "failed":
                    raise RuntimeError(f"create failed: {o.get('error')}")
                if time.time() - t0 > PROVISION_TIMEOUT_S:
                    raise RuntimeError("create timed out")
            res["booted_s"] = round(time.time() - t0, 1)
            wd = "/data/home/zr3c"
            self.ib.exec(mid, f"mkdir -p {wd}")
            for local, remote, mode in ((CONRON, f"{wd}/con-ron", "0755"),
                                        (HERE / "conron_shard.py", f"{wd}/conron_shard.py", "0644"),
                                        (jfile, f"{wd}/job.json", "0644"),
                                        (zst, f"{wd}/shard.ndjson.zst", "0644")):
                r = self.ib.upload(mid, remote, local, mode)
                if r.get("sha256") != sha256(local):
                    raise RuntimeError(f"upload of {local.name}: the API hashed {r.get('sha256')}")
            res["uploaded_s"] = round(time.time() - t0, 1)
            chk = self.ib.exec(mid, "command -v zstd || ((sudo apt-get update -q && sudo DEBIAN_FRONTEND="
                                    "noninteractive apt-get install -y -q zstd) >/dev/null 2>&1; command -v zstd)",
                               timeout=300)
            if chk.get("exitCode") != 0:
                raise RuntimeError(f"no zstd on the VM: {chk}")
            start = (f"cd {wd} && (ulimit -s unlimited 2>/dev/null || ulimit -s $(ulimit -H -s)); "
                     f"setsid nohup python3 conron_shard.py {wd} > runner.log 2>&1 < /dev/null & "
                     f"sleep 5; cat {wd}/status.json")
            r = self.ib.exec(mid, start, timeout=120)
        else:
            sbx = self.nv.create({**LABEL, "shard": slug[:60], "run": "20261027"}, timeout_s=3600)
            sid = sbx.sandbox_id
            with self.lock:
                vm["id"] = sid
            registry_add({"provider": "novita", "id": sid, "name": name, "shard": shard,
                          "event": "created", "vcpus": spec["vcpus"], "mem_gib": spec["mem_gib"]})
            res["booted_s"] = round(time.time() - t0, 1)
            wd = "/root/zr3c"
            sbx.commands.run(f"mkdir -p {wd}", user="root")
            for local, remote in ((CONRON, f"{wd}/con-ron"), (HERE / "conron_shard.py", f"{wd}/conron_shard.py"),
                                  (jfile, f"{wd}/job.json"), (zst, f"{wd}/shard.ndjson.zst")):
                with open(local, "rb") as f:
                    sbx.files.write(remote, f, user="root", request_timeout=1800)
            r = sbx.commands.run(f"chmod 755 {wd}/con-ron && cd {wd} && sha256sum con-ron conron_shard.py "
                                 f"shard.ndjson.zst", user="root", timeout=120)
            got = {l.split()[1]: l.split()[0] for l in r.stdout.splitlines() if l.strip()}
            if got.get("con-ron") != CONRON_SHA or got.get("shard.ndjson.zst") != ex["sha256_zst"] \
                    or got.get("conron_shard.py") != sha256(HERE / "conron_shard.py"):
                raise RuntimeError(f"upload hashes differ: {got}")
            res["uploaded_s"] = round(time.time() - t0, 1)
            sbx.commands.run(f"cd {wd} && (ulimit -s unlimited 2>/dev/null || true); setsid nohup python3 "
                             f"conron_shard.py {wd} > runner.log 2>&1 < /dev/null &", user="root", background=True)
            time.sleep(5)
            r = {"stdout": sbx.commands.run(f"cat {wd}/status.json", user="root", timeout=60).stdout}
        if '"phase"' not in r.get("stdout", ""):
            raise RuntimeError(f"the runner did not start: {str(r)[:300]}")
        res["wd"] = wd
        res["started_epoch"] = time.time()
        return res

    def remote_cat(self, vm: dict, path: str) -> str:
        if vm["provider"] == "instabox":
            r = self.ib.exec(vm["id"], f"cat {path} 2>/dev/null; true", timeout=60)
            return r.get("stdout", "")
        return self.nv.run(vm["id"], f"cat {path} 2>/dev/null; true", timeout=60).stdout

    def act_poll(self, shard: str, vm: dict) -> dict:
        wd = vm["wd"]
        st = self.remote_cat(vm, f"{wd}/status.json")
        tail = self.remote_cat(vm, f"{wd}/conron.err | tail -n 2")
        out = {"status": json.loads(st) if st.strip().startswith("{") else None, "tail": tail[-400:]}
        if out["status"] and out["status"].get("phase") == "done":
            d = RECEIPTS / slug_of(shard)
            d.mkdir(parents=True, exist_ok=True)
            for f in ("receipt.json", "conron.out", "runner.log"):
                (d / f).write_text(self.remote_cat(vm, f"{wd}/{f}"))
            if vm["provider"] == "instabox":
                self.ib.exec(vm["id"], f"cd {wd} && gzip -kf conron.err", timeout=300)
                self.ib.download(vm["id"], f"{wd}/conron.err.gz", d / "conron.err.gz")
            else:
                self.nv.run(vm["id"], f"cd {wd} && gzip -kf conron.err", timeout=300)
                (d / "conron.err.gz").write_bytes(bytes(self.nv.read(vm["id"], f"{wd}/conron.err.gz")))
            json.loads((d / "receipt.json").read_text())       # must parse, or the poll is retried
            out["collected"] = True
        return out

    def act_destroy(self, vm: dict) -> dict:
        if vm["provider"] == "instabox":
            op = self.ib.delete(vm["id"])
            t0 = time.time()
            while op and time.time() - t0 < 600:
                o = self.ib.op(op["id"])
                if o["state"] in ("succeeded", "failed"):
                    break
            m = self.ib.machine(vm["id"])
            if m is not None and m.get("state") != "deleting":
                raise RuntimeError(f"still there after delete: {m.get('state')}")
        else:
            self.nv.kill(vm["id"])
        registry_add({"provider": vm["provider"], "id": vm["id"], "event": "deleted"})
        return {"deleted_epoch": time.time()}

    # -- receipt verification (main thread)
    def verify(self, shard: str) -> dict:
        rec = json.loads((RECEIPTS / slug_of(shard) / "receipt.json").read_text())
        ex = load_exports()[export_key(shard)]
        expect_decls = conron_count(ex)
        ins = rec.get("sha256_inputs", {})
        v = {"phase": rec.get("phase"), "exit_code": rec.get("exit_code"),
             "verdict_lines": [l for l in rec.get("verdict_lines", [])
                               if l.startswith(("con-ron: accepted", "con-ron: rejected", "con-ron: declined"))],
             "accepted_declarations": rec.get("accepted_declarations"),
             "expected_declarations": expect_decls,
             "hashes_ok": ins.get("con-ron") == CONRON_SHA and ins.get("shard.ndjson.zst") == ex["sha256_zst"]
             and rec.get("sha256_export") == ex["sha256_ndjson"],
             "wall_s": rec.get("wall_s"), "cpu_s": round((rec.get("user_s") or 0) + (rec.get("sys_s") or 0), 1),
             "maxrss_kib": rec.get("maxrss_kib"), "peak_sampled_rss_kib": rec.get("peak_sampled_rss_kib"),
             "host": rec.get("host")}
        if export_key(shard).startswith("fault:"):
            v["ok"] = (v["hashes_ok"] and v["phase"] == "checked" and v["exit_code"] == 1
                       and any("rejected" in l and "Prime_B_right_06_2.ev_whole" in l for l in v["verdict_lines"]))
        else:
            v["ok"] = (v["hashes_ok"] and v["phase"] == "checked" and v["exit_code"] == 0
                       and v["accepted_declarations"] == expect_decls
                       and any(l.startswith("con-ron: accepted") and "(--verified)" in l for l in v["verdict_lines"]))
        # no verdict at all (a crash, a kill, a broken upload) is retried; a verdict is not
        v["infrastructure"] = not v["ok"] and not v["verdict_lines"]
        return v

    # -- the loop
    def step(self) -> bool:
        stop = (RUN / "STOP").exists()
        drain = (RUN / "DRAIN").exists() or self.term
        ex = load_exports()
        wanted = self.state.setdefault("wanted", [])
        for name in wanted:
            self.sh(name)
        for shard, fut in list(self.busy.items()):
            if not fut.done():
                continue
            del self.busy[shard]
            s = self.sh(shard)
            kind = s.pop("action")
            vm = s["vms"][-1] if s.get("vms") else {}
            try:
                res = fut.result()
            except Exception as e:
                self.note(shard, f"{kind} error", error=str(e)[:500])
                s["errors"] = s.get("errors", 0) + 1
                if kind == "provision":
                    if vm.get("id"):
                        s["state"] = "destroy_then_retry" if s["errors"] < 4 else "destroy_then_fail"
                    else:
                        s["vms"].pop()
                        s["state"] = "ready" if s["errors"] < 4 else "failed_provision"
                        s["not_before"] = time.time() + 60
                elif kind == "poll":
                    s["poll_errors"] = s.get("poll_errors", 0) + 1
                    s["next_poll"] = time.time() + 120
                    if vm.get("provider") == "novita" and time.time() - vm.get("created_epoch", 0) > 3400:
                        self.note(shard, "novita session limit: back to InstaBox")
                        s["novita_attempts"] = s.get("novita_attempts", 0) + 1
                        s["state"] = "destroy_then_retry"
                    elif s["poll_errors"] >= 15:
                        s["state"] = "destroy_then_retry"
                elif kind == "destroy":
                    s["next_destroy"] = time.time() + 120
                continue
            if kind == "provision":
                vm.update(res)
                s["state"] = "running"
                s["started_epoch"] = res["started_epoch"]
                s["next_poll"] = time.time() + 120
                self.note(shard, "started", vm=vm["id"], booted_s=res.get("booted_s"),
                          uploaded_s=res.get("uploaded_s"))
            elif kind == "poll":
                s["last_status"] = res.get("status")
                s["last_tail"] = res.get("tail")
                s["last_poll_utc"] = utc()
                s["poll_errors"] = 0
                if res.get("collected"):
                    v = self.verify(shard)
                    s.setdefault("verdicts", []).append(v)
                    s["verdict"] = v
                    self.note(shard, "collected", ok=v["ok"], lines=v["verdict_lines"])
                    if v["ok"]:
                        s["state"] = "destroy_then_done"
                    elif v["infrastructure"] and len(s["verdicts"]) < 3:
                        s["state"] = "destroy_then_retry"
                    else:
                        s["state"] = "destroy_then_review"
                else:
                    s["next_poll"] = time.time() + self.args.poll_s
                    if vm["provider"] == "novita" and time.time() - vm["created_epoch"] > 3400:
                        self.note(shard, "novita session limit: back to InstaBox")
                        s["novita_attempts"] = s.get("novita_attempts", 0) + 1
                        s["state"] = "destroy_then_retry"
            elif kind == "destroy":
                vm.update(res)
                nxt = s.pop("after_destroy", "ready")
                s["state"] = nxt
                self.note(shard, "vm deleted", vm=vm.get("id"), next=nxt)
        for shard in wanted:
            s = self.sh(shard)
            if shard in self.busy or drain:
                continue
            st = s["state"]
            if st == "waiting" and ex.get(export_key(shard), {}).get("status"):
                s["state"] = st = "ready"
            if st.startswith("destroy_then_"):
                if time.time() < s.get("next_destroy", 0):
                    continue
                nxt = {"destroy_then_done": "done", "destroy_then_retry": "ready",
                       "destroy_then_review": "review", "destroy_then_fail": "failed"}[st]
                vm = s["vms"][-1] if s.get("vms") else {}
                if vm.get("id") and not vm.get("deleted_epoch"):
                    s["after_destroy"] = nxt
                    s["action"] = "destroy"
                    self.busy[shard] = self.pool.submit(self.act_destroy, dict(vm))
                else:
                    s["state"] = nxt
                continue
            if st == "running" and time.time() >= s.get("next_poll", 0):
                s["action"] = "poll"
                self.busy[shard] = self.pool.submit(self.act_poll, shard, dict(s["vms"][-1]))
                continue
            if st == "ready" and not stop and time.time() >= s.get("not_before", 0):
                if self.projected_usd() > STOP_LAUNCH_USD:
                    if not self.state.get("budget_hold"):
                        self.state["budget_hold"] = utc()
                        log("budget hold: projected", round(self.projected_usd(), 2))
                    continue
                spec = self.choose(shard)
                if not spec:
                    continue
                s["attempt"] += 1
                s["spec"] = spec
                vm = {"provider": spec["provider"], "vcpus": spec["vcpus"], "mem_gib": spec["mem_gib"],
                      "created_epoch": time.time()}
                s.setdefault("vms", []).append(vm)
                s["state"] = "provisioning"
                s["action"] = "provision"
                self.note(shard, "provisioning", provider=spec["provider"], attempt=s["attempt"])
                self.busy[shard] = self.pool.submit(self.act_provision, shard, spec, s["attempt"], vm)
        # a shard that is done no longer needs its compressed export (the top and fault ones stay)
        for shard, s in self.state["shards"].items():
            k = export_key(shard)
            if s["state"] == "done" and not s.get("spool_deleted") and k.startswith("site:") and \
                    all(self.sh(o)["state"] in DONE_STATES for o in self.state["shards"] if export_key(o) == k):
                p = Path(ex.get(k, {}).get("file", "/nonexistent"))
                if not manifest_has_kernel_hashes(k):
                    continue        # `remanifest` reads it first
                if p.exists():
                    p.unlink()
                s["spool_deleted"] = utc()
        if stop:
            for shard in wanted:
                s = self.sh(shard)
                vm = s["vms"][-1] if s.get("vms") else {}
                if shard not in self.busy and vm.get("id") and not vm.get("deleted_epoch") \
                        and not s["state"].startswith("destroy_then_"):
                    s["state"] = "destroy_then_retry"
        self.state["spent_usd"] = {k: round(v, 4) for k, v in self.spent_usd().items()}
        self.state["projected_usd"] = round(self.projected_usd(), 2)
        self.state["heartbeat"] = utc()
        self.save()
        live_vm = any(s.get("vms") and s["vms"][-1].get("id") and not s["vms"][-1].get("deleted_epoch")
                      for s in self.state["shards"].values())
        if drain and not stop:
            if not self.busy:
                log("drained: nothing in flight; VMs left running for the next start")
            return bool(self.busy)
        if stop:
            return bool(self.busy) or live_vm
        return bool(self.busy) or live_vm or any(self.sh(w)["state"] not in DONE_STATES for w in wanted)

    def loop(self) -> None:
        log("fleet loop start", os.getpid())
        (RUN / "fleet.pid").write_text(str(os.getpid()) + "\n")
        while self.step():
            time.sleep(10)
        self.pool.shutdown(wait=True)
        self.save()
        log("fleet loop end")


def cmd_run(a) -> None:
    fl = Fleet(a)
    if a.want:
        fl.state["wanted"] = [x for x in a.want.split(",") if x]
    if a.add:
        fl.state["wanted"] = fl.state.get("wanted", []) + [x for x in a.add.split(",")
                                                           if x and x not in fl.state.get("wanted", [])]
    if a.novita_shards is not None:
        fl.state["novita_shards"] = [x for x in a.novita_shards.split(",") if x]
    if a.scale:
        fl.state["scale"] = a.scale
    fl.state.setdefault("launch_utc", utc())
    fl.save()
    fl.loop()


def cmd_deadman(a) -> None:
    """Deletes every registered VM at the deadline or when RUN/STOP appears, then checks
    each provider's own listing for anything left with this run's label."""
    deadline = a.deadline
    log("deadman start", os.getpid(), "deadline", time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(deadline)))
    while time.time() < deadline and not (RUN / "STOP").exists():
        time.sleep(30)
    log("deadman triggered:", "deadline" if time.time() >= deadline else "STOP")
    ib, nv = InstaBox(), Novita()
    for rnd in range(10):
        left = registry()
        for (prov, vid), r in left.items():
            try:
                if prov == "instabox":
                    ib.delete(vid)
                    gone = ib.machine(vid) is None
                else:
                    nv.kill(vid)
                    gone = True
                log("deadman delete", prov, vid, "gone" if gone else "pending")
                if gone:
                    registry_add({"provider": prov, "id": vid, "event": "deleted", "by": "deadman"})
            except Exception as e:
                log("deadman error", prov, vid, str(e)[:300])
        try:
            stray_ib = [m for m in ib.list_mine() if m.get("state") not in ("deleting",)]
            stray_nv = nv.list_mine()
        except Exception as e:
            log("deadman listing error", str(e)[:300])
            stray_ib, stray_nv = [{}], []
        for m in stray_ib:
            if m.get("id"):
                log("deadman stray instabox", m["id"], m.get("name"))
                ib.delete(m["id"])
        for s in stray_nv:
            log("deadman stray novita", s.sandbox_id)
            nv.kill(s.sandbox_id)
        if not registry() and not stray_ib and not stray_nv:
            log("deadman: nothing of this run remains on either provider")
            return
        time.sleep(60)
    log("deadman: gave up after 10 rounds; check by hand")


def cmd_sweep(a) -> None:
    ib, nv = InstaBox(), Novita()
    mine = ib.list_mine()
    print("instabox:", [(m["id"], m["name"], m["state"]) for m in mine])
    nvs = nv.list_mine()
    print("novita:", [(s.sandbox_id, (s.metadata or {}).get("shard")) for s in nvs])
    print("registry (not deleted):", list(registry().keys()))
    if a.delete:
        for m in mine:
            ib.delete(m["id"])
            registry_add({"provider": "instabox", "id": m["id"], "event": "deleted", "by": "sweep"})
        for s in nvs:
            nv.kill(s.sandbox_id)
            registry_add({"provider": "novita", "id": s.sandbox_id, "event": "deleted", "by": "sweep"})


def origin(module: str) -> str:
    """The census groups of Stage A (`RUNS.md`, the sampling windows)."""
    r = module.split(".")[0]
    if r in ("Init", "Std", "Lean", "Lake"):
        return "core"
    if r == "Mathlib":
        return "Mathlib"
    if r in ("Batteries", "Aesop", "Qq", "Plausible", "ProofWidgets", "ImportGraph", "LeanSearchClient", "Cli"):
        return "deps"
    if r == "ZetaLean":
        return "ZetaLean"
    if r.startswith("RHHeight") or r.startswith("Hardy") or r == "Zeta23":
        return "hunt137"
    if r == "Rung3Assembly":
        return "assembly"
    if r.startswith(("CB_", "Cg_")) or r == "Ccentre":
        return "sites"
    return "other"


def read_zst_lines(p: Path):
    r = subprocess.run(["zstd", "-dc", str(p)], capture_output=True, check=True)
    return r.stdout.decode().splitlines()


def cmd_coverage(a) -> None:
    """Joins the manifests, the receipts and the phase0 census and closure."""
    P = production()
    fleet = load_json(RUN / "fleet.json", {"shards": {}})
    info = json.loads((PHASE0 / "top-info.json").read_text())
    sites = sorted(P.plan_sites())
    shards = ["top"] + [f"site:{s}" for s in sites]
    accepted = {k: s for k, s in fleet["shards"].items() if s["state"] == "done" and (s.get("verdict") or {}).get("ok")}
    by_key = {}
    for k in accepted:
        by_key.setdefault(export_key(k), []).append(k)
    missing = [x for x in shards if x not in by_key]
    fault = {k: s.get("verdict") for k, s in fleet["shards"].items() if export_key(k).startswith("fault:")}
    # consistency of every constant held by more than one shard
    # kernel hashes (columns 6 to 8): binder names and binder info left out, as the kernel does
    seen: dict[str, tuple[str, str, str]] = {}
    clashes, decls_total, binder_only = [], 0, set()
    types: dict[str, str] = {}
    glue_defs: dict[str, str] = {}
    old_format = []
    for sh in shards:
        if sh not in by_key:
            continue
        for line in read_zst_lines(manifest_path(sh)):
            f = line.split("\t")
            if len(f) != 8:
                old_format.append(sh)
                break
            name, kind, h, th, vh, kh, kth, kvh = f
            decls_total += 1
            if name in seen:
                if seen[name][0] != kh:
                    clashes.append([name, seen[name][1], sh])
                elif seen[name][2] != h:
                    binder_only.add(name)
            else:
                seen[name] = (kh, sh, h)
            if sh == "top" and name.startswith("Rung3Glue.T."):
                glue_defs[name[len("Rung3Glue.T."):]] = kvh
            if sh != "top" and kind == "thm":
                types[name] = kth
    glue = {"site_theorems": len(info["site_theorems"]), "matched": 0, "mismatched": [], "absent": []}
    for sname in info["site_theorems"]:
        if sname not in glue_defs or sname not in types:
            glue["absent"].append(sname)
        elif glue_defs[sname] == types[sname]:
            glue["matched"] += 1
        else:
            glue["mismatched"].append(sname)
    abstracted = set(info["abstracted"])
    glue_present = sum(1 for c in abstracted if f"Rung3Glue.{c}" in seen)
    closure = set(read_zst_lines(PHASE0 / "closure18.txt.zst"))
    census = [l.split("\t") for l in read_zst_lines(PHASE0 / "census.tsv.zst")]
    rows: dict[str, dict] = {}
    unchecked = []
    for name, mod, kind in census:
        g = origin(mod)
        r = rows.setdefault(g, {"constants": 0, "in_closure": 0, "checked": 0, "closure_checked": 0,
                                "closure_via_glue": 0, "closure_unchecked": 0})
        r["constants"] += 1
        chk = name in seen
        r["checked"] += chk
        if name in closure:
            r["in_closure"] += 1
            if chk:
                r["closure_checked"] += 1
            elif name in abstracted:
                r["closure_via_glue"] += 1
            else:
                r["closure_unchecked"] += 1
                unchecked.append(name)
    census_names = {c[0] for c in census}
    not_in_census = sorted(n for n in closure if n not in census_names)[:20]
    out = {"utc": utc(), "shards_expected": len(shards), "shards_accepted": len(shards) - len(missing),
           "missing": missing, "fault": fault, "declarations_in_accepted_shards": decls_total,
           "distinct_constants_checked": len(seen), "clashes": clashes[:50], "clash_count": len(clashes),
           "shared_constants_differing_only_in_binder_names_or_info": len(binder_only),
           "manifests_without_kernel_hashes": old_format,
           "glue": glue, "abstracted": len(abstracted), "abstracted_with_glue_in_top": glue_present,
           "closure_size": len(closure), "closure_not_in_census": not_in_census,
           "census_constants": len(census), "by_origin": rows, "closure_unchecked": unchecked[:50],
           "closure_unchecked_count": len(unchecked)}
    save_json(RUN / "coverage.json", out)
    print(json.dumps({k: v for k, v in out.items() if k != "by_origin"}, indent=1))
    print("| origin | constants | in the closure of the 18 | checked by con-ron | closure, checked | closure, via glue | closure, unchecked |")
    print("|---|---|---|---|---|---|---|")
    for g in ("sites", "Mathlib", "core", "deps", "hunt137", "ZetaLean", "assembly", "other"):
        if g in rows:
            r = rows[g]
            print(f"| {g} | {r['constants']:,} | {r['in_closure']:,} | {r['checked']:,} | {r['closure_checked']:,} | "
                  f"{r['closure_via_glue']:,} | {r['closure_unchecked']:,} |")


def cmd_record(a) -> None:
    """The run's record for `pilot.json` (`production.replay.stage_b_fleet`): the tools'
    hashes, phase0, every shard's export and verdict, the planted faults, the coverage, and
    the cost per provider (InstaBox from its usage API per machine, Novita at list price
    from the recorded creation and deletion times)."""
    fleet = load_json(RUN / "fleet.json", {"shards": {}})
    ex = load_exports()
    ph = load_json(RUN / "phase0.json", {}).get("phase0", {})
    cov = load_json(RUN / "coverage.json", {})
    info = json.loads((PHASE0 / "top-info.json").read_text())
    ib = InstaBox()
    shards, ib_usd, nv_usd, vms, first, last = {}, 0.0, 0.0, 0, None, None
    for k, s in sorted(fleet["shards"].items()):
        v = s.get("verdict") or {}
        e = ex.get(export_key(k), {})
        row = {"state": s["state"], "attempts": s["attempt"], "bytes": e.get("bytes_ndjson"),
               "sha256": e.get("sha256_ndjson"), "export_wall_s": (e.get("export") or {}).get("wall_s"),
               "lines": v.get("verdict_lines"), "accepted": v.get("accepted_declarations"),
               "exit_code": v.get("exit_code"), "wall_s": v.get("wall_s"), "cpu_s": v.get("cpu_s"),
               "maxrss_kib": v.get("maxrss_kib"), "vms": []}
        for vm in s.get("vms", []):
            if not vm.get("id"):
                continue
            vms += 1
            t0, t1 = vm["created_epoch"], vm.get("deleted_epoch")
            first = t0 if first is None else min(first, t0)
            last = t1 if (t1 and (last is None or t1 > last)) else last
            rec = {"provider": vm["provider"], "id": vm["id"], "spec": f"{vm['vcpus']}/{vm['mem_gib']}",
                   "alive_s": round((t1 or time.time()) - t0, 1)}
            if vm["provider"] == "instabox":
                try:
                    u = ib.usage(vm["id"])
                    rec["usd"] = round(u["vcpuSeconds"] / 3600 * IB_VCPU_H + u["memGiBSeconds"] / 3600 * IB_GIB_H, 5)
                    rec["running_s"] = u["runningSeconds"]
                except Exception as err:          # the local times, as an upper bound
                    rec["usd"] = round(rec["alive_s"] * Fleet.rate_per_s(vm), 5)
                    rec["usage_error"] = str(err)[:120]
                ib_usd += rec["usd"]
            else:
                rec["usd"] = round(rec["alive_s"] * Fleet.rate_per_s(vm), 5)
                nv_usd += rec["usd"]
            row["vms"].append(rec)
        shards[k] = row
    out = {"date": "2026-10-27", "run_dir": "<cache>/rung3-conron-fleet-20261027",
           "tools": load_json(RUN / "build" / "build.json", {}) | {
               "conron_shard.py": sha256(HERE / "conron_shard.py"),
               "shard_manifest.py": sha256(HERE / "shard_manifest.py")},
           "phase0": {k: ph.get(k) for k in ("assembled", "census", "closure")},
           "top_info": {"site_theorems": len(info["site_theorems"]), "abstracted": info["abstracted"],
                        "site_constants_reached_otherwise": len(info["site_constants_reached_otherwise"]),
                        "export_names": info["export_names"]},
           "shards": shards, "coverage": cov,
           "cost_usd": {"instabox": round(ib_usd, 3), "novita_list": round(nv_usd, 3)},
           "vms_created": vms,
           "first_vm_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(first)) if first else None,
           "last_vm_deleted_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(last)) if last else None,
           "registry_alive": len(registry())}
    save_json(RUN / "stage_b_fleet.json", out)
    if a.write_pilot:
        pj = HERE / "pilot.json"
        d = json.loads(pj.read_text())
        pub = json.loads(json.dumps(out))      # the committed copy keeps no VM ids
        for sh in pub["shards"].values():
            for v in sh["vms"]:
                v.pop("id", None)
        d["production"]["replay"]["stage_b_fleet"] = pub
        pj.write_text(json.dumps(d, indent=1) + "\n")
    print(json.dumps({k: out[k] for k in ("cost_usd", "vms_created", "first_vm_utc", "last_vm_deleted_utc",
                                          "registry_alive")}, indent=1))


def cmd_status(_a) -> None:
    st = load_json(RUN / "fleet.json", {"shards": {}})
    ex = load_exports()
    from collections import Counter
    print("exports:", Counter(v.get("status") for v in ex.values()), "spool GB",
          round(spool_bytes() / 1e9, 2), "disk free GB", round(disk_free_gb(), 1),
          "MemAvailable GiB", round(mem_available_gib(), 1))
    print("fleet:", Counter(s["state"] for s in st["shards"].values()), "spent", st.get("spent_usd"),
          "projected", st.get("projected_usd"), "heartbeat", st.get("heartbeat"))
    print("registry alive:", len(registry()))


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("build")
    sub.add_parser("phase0")
    e = sub.add_parser("export")
    e.add_argument("--jobs", default="")
    e.add_argument("--workers", type=int, default=3)
    r = sub.add_parser("run")
    r.add_argument("--want", default="")
    r.add_argument("--add", default="")
    r.add_argument("--workers", type=int, default=8)
    r.add_argument("--instabox-max", type=int, default=90)
    r.add_argument("--novita", action="store_true")
    r.add_argument("--novita-max", type=int, default=5)
    r.add_argument("--novita-shards", default=None)
    r.add_argument("--poll-s", type=int, default=240)
    r.add_argument("--scale", type=float, default=0.0)
    d = sub.add_parser("deadman")
    d.add_argument("--deadline", type=float, required=True)
    s = sub.add_parser("sweep")
    s.add_argument("--delete", action="store_true")
    sub.add_parser("status")
    sub.add_parser("coverage")
    rm = sub.add_parser("remanifest")
    rm.add_argument("--wait", action="store_true")
    rm.add_argument("--workers", type=int, default=4)
    rc = sub.add_parser("record")
    rc.add_argument("--write-pilot", action="store_true")
    a = ap.parse_args()
    if a.cmd in ("phase0", "export", "run", "deadman", "remanifest"):
        RUN.mkdir(parents=True, exist_ok=True)
        (RUN / f"{a.cmd}.pid").write_text(f"{os.getpid()}\n")
    {"build": cmd_build, "phase0": cmd_phase0, "export": cmd_export, "run": cmd_run,
     "deadman": cmd_deadman, "sweep": cmd_sweep, "status": cmd_status, "coverage": cmd_coverage, "remanifest": cmd_remanifest,
     "record": cmd_record}[a.cmd](a)


if __name__ == "__main__":
    main()
