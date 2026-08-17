"""Checkpointed extension runner for the corrected C_{kappa,i} tables.

Targets (all mode "corrected", assembly "coefficient" = eq (10.1)):
    --target row2   kappa = 2 row
    --target row3   kappa = 3 row
    --target diag   stable diagonal C_{i-2,i}

Every computed value is written to coefficients_ext.json immediately
(atomic replace under an fcntl lock, safe for concurrent runners), and a
one-line progress record is appended to extend_log.md. Existing values
(from coefficients.json for i <= 20, or from an earlier run) are used as
a correctness gate: recomputation must reproduce them exactly, otherwise
the runner aborts.

The cons4_sig cache is persisted per target (c4cache_<target>.pkl) so a
killed session resumes cheaply. With --procs > 1, the missing inner
constants of each level are computed in parallel worker processes
(exact Fraction arithmetic per pair; the assembly stays in the parent).

Usage:
    .venv/bin/python hunts/rogue_frontier/fkappa/extend_run.py \
        --target row2 --imax 32 [--procs 4]
"""

import argparse
import fcntl
import json
import os
import pickle
import sys
import time
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import bian_engine as be
import extend_engine as ee

EXT = os.path.join(HERE, "coefficients_ext.json")
LOCK = os.path.join(HERE, ".ext_lock")
LOG = os.path.join(HERE, "extend_log.md")


# ---------------------------------------------------------------- storage

def _locked(fn):
    with open(LOCK, "w") as lk:
        fcntl.flock(lk, fcntl.LOCK_EX)
        try:
            return fn()
        finally:
            fcntl.flock(lk, fcntl.LOCK_UN)


def load_ext():
    def go():
        if os.path.exists(EXT):
            with open(EXT) as f:
                return json.load(f)
        return {}
    return _locked(go)


def store_value(section, key, i, value, seconds):
    """section: 'rows' or 'diagonal'; key: kappa as str or None."""
    def go():
        data = {}
        if os.path.exists(EXT):
            with open(EXT) as f:
                data = json.load(f)
        c = data.setdefault("corrected", {})
        if section == "rows":
            c.setdefault("rows", {}).setdefault(key, {})[str(i)] = str(value)
            c.setdefault("timing_rows", {}).setdefault(key, {})[str(i)] = \
                round(seconds, 2)
        else:
            c.setdefault("diagonal", {})[str(i)] = str(value)
            c.setdefault("timing_diagonal", {})[str(i)] = round(seconds, 2)
        tmp = EXT + ".tmp"
        with open(tmp, "w") as f:
            json.dump(data, f, indent=1, sort_keys=True)
        os.replace(tmp, EXT)
    _locked(go)


def log_line(text):
    def go():
        with open(LOG, "a") as f:
            f.write(text + "\n")
    _locked(go)


# ------------------------------------------------------- parallel workers

def _worker_init():
    ee.install()
    be.READING = "corrected"


def _worker_pair(args):
    sigv, sigw = args
    return (sigv, sigw), be.cons4_sig(sigv, sigw)


def missing_pairs(i, kapa):
    """All canonical (sigv, sigw) pairs level i needs that are not yet in
    the c4 cache (mirrors coefficient()'s loop without evaluating)."""
    n = i - 1
    need = set()
    for m in range(1, n // 2 + 1):
        mw = n - m
        j0 = m
        bv = be.side_signed(kapa, m, j0)
        bw = be.side_signed(kapa, mw, j0)
        for ma, itemsv in bv.items():
            itemsw = bw.get(ma)
            if not itemsw:
                continue
            for sv, _wv in itemsv:
                for sw, _ww in itemsw:
                    a, b = (sv, sw) if sv <= sw else (sw, sv)
                    if (a, b, True) not in be._c4_cache:
                        need.add((a, b))
    return sorted(need)


def compute_level(i, kapa, procs, cachefile=None):
    """Fill the c4 cache for level i (parallel if procs > 1), then
    assemble the coefficient. During long parallel phases the cache is
    persisted every ~120 s so a killed session loses little."""
    if procs > 1:
        pairs = missing_pairs(i, kapa)
        if pairs:
            import multiprocessing as mp
            # big pairs first for load balance
            pairs.sort(key=lambda p: -(sum(a + b for a, b in p[0])
                                       + sum(a + b for a, b in p[1])))
            lastsave = time.time()
            with mp.Pool(procs, initializer=_worker_init) as pool:
                for (sv, sw), val in pool.imap_unordered(
                        _worker_pair, pairs, chunksize=8):
                    be._c4_cache[(sv, sw, True)] = val
                    if cachefile and time.time() - lastsave > 120:
                        with open(cachefile + ".tmp", "wb") as f:
                            pickle.dump(be._c4_cache, f)
                        os.replace(cachefile + ".tmp", cachefile)
                        lastsave = time.time()
    return be.coefficient(i, kapa)


# ---------------------------------------------------------------- driver

def seed_values(target, kapa):
    """Known-correct values for the gate: corrected coefficients.json
    plus anything already in coefficients_ext.json."""
    seeds = {}
    with open(os.path.join(HERE, "coefficients.json")) as f:
        base = json.load(f)["corrected"]
    src = base["diagonal"] if target == "diag" else base["rows"][str(kapa)]
    for k, v in src.items():
        seeds[int(k)] = Fraction(v)
    ext = load_ext().get("corrected", {})
    src2 = (ext.get("diagonal", {}) if target == "diag"
            else ext.get("rows", {}).get(str(kapa), {}))
    for k, v in src2.items():
        seeds.setdefault(int(k), Fraction(v))
    return seeds


def run(target, imax, procs):
    ee.install()
    be.READING = "corrected"
    kapa = {"row2": 2, "row3": 3, "diag": None}[target]
    seeds = seed_values(target, kapa)
    cachefile = os.path.join(HERE, f"c4cache_{target}.pkl")
    if os.path.exists(cachefile):
        try:
            with open(cachefile, "rb") as f:
                be._c4_cache.update(pickle.load(f))
            print(f"loaded {len(be._c4_cache)} cached inner constants",
                  flush=True)
        except Exception as exc:
            print(f"cache load failed ({exc}); starting cold", flush=True)

    log_line(f"- [{target}] runner start, imax={imax}, procs={procs}, "
             f"seeds up to i={max(seeds)}")
    partial = Fraction(0)   # running sum for the simple-zeros bound
    for i in range(1, imax + 1):
        t0 = time.time()
        kap_i = (i - 2 if i > 2 else 1) if target == "diag" else kapa
        c = compute_level(i, kap_i, procs if i > 20 else 1,
                          cachefile=cachefile)
        dt = time.time() - t0
        if i in seeds and c != seeds[i]:
            log_line(f"- [{target}] GATE FAILURE at i={i}: computed {c}, "
                     f"expected {seeds[i]}; ABORTING")
            print(f"GATE FAILURE at i={i}: {c} != {seeds[i]}", flush=True)
            sys.exit(2)
        section = "diagonal" if target == "diag" else "rows"
        store_value(section, None if kapa is None else str(kapa), i, c, dt)
        partial += Fraction(2) * c / ((i + 1) * (i + 2))
        bound = Fraction(1) - partial
        root = float(abs(c)) ** (1.0 / i) if c else 0.0
        gate = "gate-ok" if i in seeds else "NEW"
        msg = (f"- [{target}] i={i}: {dt:.1f}s {gate} "
               f"bound_thru_i={float(bound):.6f} root={root:.4f} "
               f"c4={len(be._c4_cache)}")
        print(msg, flush=True)
        if i > 18 or gate == "NEW":
            log_line(msg)
        if i >= 18:
            with open(cachefile + ".tmp", "wb") as f:
                pickle.dump(be._c4_cache, f)
            os.replace(cachefile + ".tmp", cachefile)
    log_line(f"- [{target}] runner done through i={imax}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--target", choices=["row2", "row3", "diag"],
                    required=True)
    ap.add_argument("--imax", type=int, required=True)
    ap.add_argument("--procs", type=int, default=1)
    args = ap.parse_args()
    run(args.target, args.imax, args.procs)


if __name__ == "__main__":
    main()
