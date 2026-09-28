"""One bounded L119 unit per container, durable evidence before return."""

from pathlib import Path
import modal

HERE = Path(__file__).resolve().parent
app = modal.App("oob-referee-l119")
volume = modal.Volume.from_name("oob-envelope-referee", create_if_missing=False)
image = (modal.Image.debian_slim(python_version="3.12")
         .pip_install("python-flint==0.9.0", "mpmath==1.3.0", "gmpy2==2.2.1")
         .add_local_file(HERE / "l119.py", "/root/l119.py")
         .add_local_file(HERE / "independent.py", "/root/independent.py")
         .add_local_file(HERE / "frozen_envelope_L119.json", "/root/frozen_envelope_L119.json"))


@app.function(image=image, cpu=(1, 1), memory=(1024, 1792), timeout=900,
              startup_timeout=180, retries=0, max_containers=10,
              single_use_containers=True, volumes={"/out": volume})
def execute(unit: str, revision: str):
    import hashlib
    import importlib.metadata
    import json
    import os
    import signal
    import time
    import traceback
    os.environ["OPENBLAS_NUM_THREADS"] = "1"
    os.environ["OMP_NUM_THREADS"] = "1"
    started = time.time()
    folder = Path("/out/l119") / revision / unit
    if folder.exists():
        raise RuntimeError("unit path exists; refuse overwrite or silent reuse")
    folder.mkdir(parents=True)
    manifest = {"unit": unit, "revision": revision, "started_unix": started,
                "status": "running", "cpu": 1, "memory_limit_MiB": 1792,
                "timeout_s": 900, "profile": "teal-sea",
                "packages": {p: importlib.metadata.version(p) for p in ("python-flint", "mpmath", "gmpy2")},
                "input_sha256": {n: hashlib.sha256(Path("/root", n).read_bytes()).hexdigest()
                                 for n in ("l119.py", "independent.py", "frozen_envelope_L119.json")}}

    def checkpoint(payload, artifact="progress.json"):
        temp = folder / (artifact+".tmp")
        temp.write_text(json.dumps(payload, indent=2, allow_nan=False)+"\n")
        temp.replace(folder / artifact)
        if unit.startswith("reduce_") and artifact in {"matrix.json", "factor.json"}:
            import gzip
            # Preserve raw JSON on the volume and a compact identical payload
            # for local review. This is file compression, not a new result.
            with gzip.open(folder / (artifact+".gz"), "wb", compresslevel=6) as stream:
                stream.write((folder / artifact).read_bytes())
        volume.commit()

    def alarm(signum, frame):
        raise TimeoutError("bounded referee unit exceeded 870 seconds")

    checkpoint(manifest, "manifest.json")
    signal.signal(signal.SIGALRM, alarm)
    signal.alarm(870)
    try:
        import l119
        if unit.startswith("panels_"):
            _, a, b = unit.split("_")
            start, stop = int(a), int(b)
            assert 0 <= start < stop <= 1000 and stop-start <= 10
            result = l119.partial(start, stop, checkpoint)
        elif unit.startswith("reduce_"):
            source = unit[len("reduce_"):]
            paths = sorted(Path("/out/l119", source).glob("panels_*/matrix.json"))
            result = l119.reduce(paths, checkpoint)
        else:
            raise ValueError("unknown unit")
        checkpoint(result, "result.json")
        manifest["status"] = result["status"]
    except BaseException as exc:
        manifest["status"] = "failed"
        checkpoint({"error": str(exc), "traceback": traceback.format_exc()}, "error.json")
    finally:
        signal.alarm(0)
        manifest["elapsed_s"] = time.time()-started
        manifest["output_sha256"] = {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                                      for p in folder.iterdir()
                                      if p.is_file() and p.name != "manifest.json" and not p.name.endswith(".tmp")}
        checkpoint(manifest, "manifest.json")
    return {"volume": "oob-envelope-referee", "directory": str(folder), "manifest": manifest}


@app.local_entrypoint()
def main(revision: str, unit: str = "", batch: bool = False):
    import json
    import os
    if os.environ.get("MODAL_PROFILE") != "teal-sea":
        raise RuntimeError("explicit teal-sea profile required")
    dest = HERE / "outputs_L119" / revision
    dest.mkdir(parents=True, exist_ok=True)
    if batch:
        if unit:
            raise ValueError("unit and batch are mutually exclusive")
        units = [f"panels_{a:04d}_{a+10:04d}" for a in range(0, 990, 10)]
        responses = execute.starmap(((u, revision) for u in units), order_outputs=False)
    else:
        responses = [execute.remote(unit, revision)]
    for receipt in responses:
        man = receipt["manifest"]
        (dest / (man["unit"]+"_receipt.json")).write_text(json.dumps(receipt, indent=2)+"\n")
        print(json.dumps({"unit": man["unit"], "status": man["status"], "elapsed_s": man["elapsed_s"]}), flush=True)
        if man["status"] != "completed":
            raise RuntimeError("unit failed or inconclusive; inspect durable evidence before any further launch")
