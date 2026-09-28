"""Stage A of the L = 1.19 run on Modal: one unit = one t-range of panels.

Each unit computes the partial sums G, C_Psi, C_H (assemble.panel_sums),
writes them to the Modal volume as soon as it finishes (per-unit
checkpoint; a unit whose file exists is skipped on rerun), and returns its
timing. reduce_stage.py sums the units locally and reads lambda_min at the
checkpoints. Measured grade: no quadrature/tail/coupling bound.

    modal run stage_modal.py                 # the approved stage A plan
    python stage_modal.py --local ...        # same units in-process (validation)
"""
import json
import sys
import time
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
PLAN = {  # approved stage A plan (RUNS.md)
    "L": "119/100", "env": "sine:16", "N": 360, "q": 64, "prec": 384, "h": "1/2",
    "bounds": [0, 80, 160, 240, 320, 350, 400, 450, 500, 525],
    "tag": "stageA_L119",
}


def run_unit(L, env, N, q, prec, h, t0, t1, outdir, tag):
    sys.path.insert(0, str(HERE))
    from flint import ctx
    from assemble import encode_mats, panel_sums
    ctx.prec = prec
    hh = Fraction(h)
    k0, k1 = int(Fraction(t0) / hh), int(Fraction(t1) / hh)
    path = Path(outdir) / f"{tag}_{t0}_{t1}.json"
    if path.exists():
        return {"unit": [t0, t1], "skipped": True}
    start = time.time()
    acc = panel_sums(Fraction(L), [env], N, q, hh, k0, k1)
    secs = time.time() - start
    rec = {"L": L, "env": env, "N": N, "q": q, "prec": prec, "h": h, "t0": t0, "t1": t1,
           "seconds": secs, "mats": encode_mats(acc)}
    tmp = path.with_suffix(".tmp")
    tmp.write_text(json.dumps(rec))
    tmp.rename(path)
    return {"unit": [t0, t1], "seconds": secs}


try:
    import modal

    app = modal.App("oob-envelope-stage-a")
    image = (modal.Image.debian_slim(python_version="3.12")
             .pip_install("python-flint==0.9.0")
             .add_local_file(str(HERE / "assemble.py"), "/root/assemble.py")
             .add_local_file(str(HERE / "envelope.json"), "/root/envelope.json")
             .add_local_file(str(HERE / "reduce_stage.py"), "/root/reduce_stage.py"))
    vol = modal.Volume.from_name("oob-envelope-stages", create_if_missing=True)

    @app.function(image=image, cpu=1.0, memory=2048, timeout=3600, volumes={"/out": vol}, retries=2)
    def unit(t0, t1):
        p = PLAN
        res = run_unit(p["L"], p["env"], p["N"], p["q"], p["prec"], p["h"], t0, t1, "/out", p["tag"])
        vol.commit()
        return res

    @app.function(image=image, cpu=1.0, memory=2048, timeout=3600, volumes={"/out": vol})
    def reduce():
        sys.path.insert(0, "/root")
        from reduce_stage import reduce_units
        vol.reload()
        out = f"/out/{PLAN['tag']}_reduced.json"
        rows = reduce_units("/out", PLAN["tag"], out)
        vol.commit()
        return rows

    @app.local_entrypoint()
    def main(reduce_only: bool = False):
        b = PLAN["bounds"]
        t_start = time.time()
        if not reduce_only:
            for res in unit.starmap(list(zip(b[:-1], b[1:])), order_outputs=False):
                print(json.dumps(res), flush=True)
            print(f"units wall {time.time() - t_start:.0f} s", flush=True)
        for row in reduce.remote():
            print(json.dumps(row), flush=True)
        print(f"total wall {time.time() - t_start:.0f} s", flush=True)
except ImportError:  # local validation without the modal package
    pass


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--local", action="store_true")
    ap.add_argument("--L", default="4/5")
    ap.add_argument("--env", default="sine:16")
    ap.add_argument("--N", type=int, default=96)
    ap.add_argument("--q", type=int, default=64)
    ap.add_argument("--prec", type=int, default=256)
    ap.add_argument("--h", default="1/2")
    ap.add_argument("--bounds", nargs="+", type=int, default=[0, 40, 70, 100])
    ap.add_argument("--outdir", required=True)
    ap.add_argument("--tag", default="local")
    a = ap.parse_args()
    for t0, t1 in zip(a.bounds[:-1], a.bounds[1:]):
        print(run_unit(a.L, a.env, a.N, a.q, a.prec, a.h, t0, t1, a.outdir, a.tag), flush=True)
