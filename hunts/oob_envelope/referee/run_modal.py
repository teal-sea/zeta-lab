"""Dispatch exactly one approved referee unit. Importing creates no run.

Use profile teal-sea. No numerical work takes place in the local entrypoint.
Every invocation uses its own container and writes its own durable artifacts.
The five-unit authorization and stop conditions are recorded in RUNS.md.
"""

from pathlib import Path
import modal

HERE = Path(__file__).resolve().parent
app = modal.App("oob-envelope-independent-referee")
volume = modal.Volume.from_name("oob-envelope-referee", create_if_missing=True)
image = (modal.Image.debian_slim(python_version="3.12")
         .pip_install("python-flint==0.9.0", "mpmath==1.3.0",
                      "numpy==2.2.6", "scipy==1.15.3")
         .add_local_file(HERE / "independent.py", "/root/independent.py")
         .add_local_file(HERE / "frozen_envelope.json", "/root/frozen_envelope.json"))


@app.function(image=image, cpu=(1, 1), memory=(1024, 1792), timeout=600,
              startup_timeout=600, retries=0, max_containers=1,
              single_use_containers=True, volumes={"/out": volume})
def execute(unit: str, revision: str):
    import hashlib
    import importlib.metadata
    import json
    import os
    import platform
    import signal
    import sys
    import time
    import traceback
    import uuid
    from pathlib import Path

    if unit not in {"controls", "leading160", "leading192", "dh512", "dh768"}:
        raise ValueError("unknown unit")
    os.environ["OPENBLAS_NUM_THREADS"] = "1"
    os.environ["OMP_NUM_THREADS"] = "1"
    sys.path.insert(0, "/root")

    started = time.time()
    run_id = f"{unit}-{uuid.uuid4().hex}"
    directory = Path("/out") / revision / run_id
    directory.mkdir(parents=True)
    hashes = {name: hashlib.sha256(Path("/root", name).read_bytes()).hexdigest()
              for name in ("independent.py", "frozen_envelope.json")}
    manifest = {"unit": unit, "revision_label": revision, "run_id": run_id,
                "input_sha256": hashes, "python": platform.python_version(),
                "packages": {p: importlib.metadata.version(p)
                             for p in ("python-flint", "mpmath", "numpy", "scipy")},
                "cpu_limit": 1, "memory_limit_MiB": 1792,
                "timeout_s": 600, "profile_requested": "teal-sea",
                "started_unix": started, "status": "running"}

    def write(name, payload):
        temp = directory / (name + ".tmp")
        temp.write_text(json.dumps(payload, indent=2, allow_nan=False) + "\n")
        temp.replace(directory / name)
        volume.commit()

    def checkpoint(payload, artifact="progress.json"):
        write(artifact, payload)

    def timed_out(signum, frame):
        raise TimeoutError("referee unit reached its 570-second work budget")

    write("manifest.json", manifest)
    signal.signal(signal.SIGALRM, timed_out)
    signal.alarm(570)
    result = None
    try:
        import independent
        result = independent.run(unit, checkpoint)
        if unit == "controls":
            gate = (set(result["lesions_detected"]) ==
                    {"inband", "one_prime_sign", "dropped_power"}
                    and len(result["frequency_K3"]) == 2)
        elif unit.startswith("leading"):
            gate = (result["author_bracket_agreement"]
                    and result["safe_endpoint_1_1579e_17"]
                    and result["K1_full_bound"]
                    and result["ldl"]["1.158e-17"]["status"] == "positive_definite"
                    and result["ldl"]["1.1585e-17"]["status"] == "negative_pivot"
                    and all((directory / f).is_file()
                            for f in ("matrix.json", "ldl.json", "budget.json")))
        else:
            gate = (result["K2_negative_witness"]
                    and result["domination_on_witness_measured"]
                    and result["R_matrix_scalar_agreement"]
                    and result["rejection_observed"]
                    and not result["positive_result"])
        result["acceptance_gate"] = bool(gate)
        write("result.json", result)
        manifest["status"] = "completed" if gate else "inconclusive"
    except BaseException as error:
        manifest["status"] = "failed"
        manifest["error_type"] = type(error).__name__
        write("error.json", {"error": str(error), "traceback": traceback.format_exc()})
    finally:
        signal.alarm(0)
        manifest["elapsed_s"] = time.time() - started
        manifest["output_sha256"] = {
            p.name: hashlib.sha256(p.read_bytes()).hexdigest()
            for p in directory.glob("*.json") if p.name != "manifest.json"}
        write("manifest.json", manifest)
    return {"volume": "oob-envelope-referee", "directory": str(directory),
            "manifest": manifest, "result": result}


@app.local_entrypoint()
def main(unit: str, revision: str, approved: bool = False):
    import json
    import os
    if not approved:
        raise RuntimeError("Supervisor approval required before dispatch.")
    if os.environ.get("MODAL_PROFILE") != "teal-sea":
        raise RuntimeError("Set MODAL_PROFILE=teal-sea explicitly.")
    response = execute.remote(unit, revision)
    dest = HERE / "outputs" / response["manifest"]["run_id"]
    dest.mkdir(parents=True, exist_ok=False)
    (dest / "receipt.json").write_text(json.dumps(response, indent=2) + "\n")
    print(json.dumps({"status": response["manifest"]["status"],
                      "volume_path": response["directory"],
                      "local_receipt": str(dest / "receipt.json")}))
