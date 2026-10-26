"""Bounded, watched odd referee inputs; no implicit retries or source mixing."""

import os
from pathlib import Path
import modal

HERE = Path(__file__).resolve().parent
NAMES = ("odd.py", "l119.py", "independent.py", "frozen_envelope_L119.json", "ODD_FORMULAS.md")
app = modal.App("oob-independent-odd-referee")
volume = modal.Volume.from_name("oob-envelope-referee", create_if_missing=False)
image = (modal.Image.debian_slim(python_version="3.12")
         .pip_install("python-flint==0.9.0", "mpmath==1.3.0", "gmpy2==2.2.1"))
for name in NAMES:
    image = image.add_local_file(HERE/name, "/root/"+name)


@app.function(image=image, cpu=(1,1), memory=(1024,1792), timeout=900,
              startup_timeout=180, retries=0, max_containers=10,
              single_use_containers=True, nonpreemptible=True, volumes={"/out":volume})
def execute(unit: str, revision: str, source: str = ""):
    import gzip
    import hashlib
    import importlib.metadata
    import json
    import signal
    import time
    import traceback
    os.environ["OPENBLAS_NUM_THREADS"] = "1"
    os.environ["OMP_NUM_THREADS"] = "1"
    started = time.time()
    folder = Path("/out/odd")/revision/unit
    if folder.exists():
        raise RuntimeError("refuse existing unit directory")
    folder.mkdir(parents=True)
    manifest = {"unit":unit,"revision":revision,"started_unix":started,"status":"running",
                "cpu":1,"memory_limit_MiB":1792,"profile":"teal-sea",
                "packages":{p:importlib.metadata.version(p) for p in ("python-flint","mpmath","gmpy2")},
                "input_sha256":{n:hashlib.sha256(Path("/root",n).read_bytes()).hexdigest() for n in NAMES}}

    def checkpoint(payload,artifact="progress.json"):
        temp = folder/(artifact+".tmp")
        temp.write_text(json.dumps(payload,indent=2,allow_nan=False)+"\n")
        temp.replace(folder/artifact)
        if artifact in ("matrix.json","factor.json"):
            with gzip.open(folder/(artifact+".gz"),"wb",compresslevel=6) as out:
                out.write((folder/artifact).read_bytes())
        volume.commit()

    def alarm(signum,frame):
        raise TimeoutError("odd referee unit reached its bounded work deadline")

    limit = 870 if unit.startswith("reduce_") else 165
    manifest["work_limit_s"] = limit
    checkpoint(manifest,"manifest.json")
    signal.signal(signal.SIGALRM,alarm)
    signal.alarm(limit)
    from flint import ctx
    previous = ctx.prec
    try:
        import odd
        parts = unit.split("_")
        case = parts[1]
        ctx.prec = odd.CASES[case]["bits"]
        if parts[0]=="panels":
            start,stop = map(int,parts[2:])
            assert 0<=start<stop<=2*odd.CASES[case]["T"] and stop-start<=10
            result = odd.partial(case,start,stop,checkpoint)
        elif parts[0]=="reduce":
            assert source
            paths = sorted((Path("/out/odd")/source).glob("panels_"+case+"_*/matrix.json"))
            result = odd.reduce(case,paths,checkpoint)
        else:
            raise ValueError("unknown unit")
        checkpoint(result,"result.json")
        manifest["status"] = result["status"]
    except BaseException as exc:
        manifest["status"] = "failed"
        checkpoint({"error":str(exc),"traceback":traceback.format_exc()},"error.json")
    finally:
        signal.alarm(0)
        ctx.prec = previous
        manifest["elapsed_s"] = time.time()-started
        manifest["output_sha256"] = {p.name:hashlib.sha256(p.read_bytes()).hexdigest()
                                    for p in folder.iterdir() if p.is_file() and p.name!="manifest.json"}
        checkpoint(manifest,"manifest.json")
    return {"volume":"oob-envelope-referee","directory":str(folder),"manifest":manifest}


@app.local_entrypoint()
def main(revision: str, unit: str = "", batch: str = "", source: str = ""):
    import json
    if os.environ.get("MODAL_PROFILE")!="teal-sea":
        raise RuntimeError("explicit teal-sea profile required")
    dest = HERE/"outputs_odd"/revision
    dest.mkdir(parents=True,exist_ok=True)
    if batch:
        assert not unit and batch in ("main","zhu")
        end = 990 if batch=="main" else 300
        jobs = [(f"panels_{batch}_{a:04d}_{a+10:04d}",revision,"") for a in range(0,end,10)]
        responses = execute.starmap(jobs,order_outputs=False)
    else:
        responses = [execute.remote(unit,revision,source)]
    for receipt in responses:
        man = receipt["manifest"]
        (dest/(man["unit"]+"_receipt.json")).write_text(json.dumps(receipt,indent=2)+"\n")
        print(json.dumps({"unit":man["unit"],"status":man["status"],"elapsed_s":man["elapsed_s"]}),flush=True)
        if man["status"]!="completed":
            raise RuntimeError("failed or inconclusive input: stop and inspect evidence")
