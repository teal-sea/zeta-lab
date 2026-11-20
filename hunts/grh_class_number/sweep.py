"""An independent completeness sweep of the H = 5000 lists (review control).

    .venv/bin/python -m hunts.grh_class_number.sweep run OUTDIR LO HI STEP P TOL OUT.jsonl
    .venv/bin/python -m hunts.grh_class_number.sweep record REVIEWER_DIR RERUN_DIR

Written by the computation reviewer of 2026-11-20 (who ran it over the whole
range in the session scratchpad) and committed here by the repair pass,
adapted to read the chunk lists directly.  It shares no code with cn.c or
cnx.c: `lsieve.c` sieves the fundamental discriminants itself and estimates
every class number by a truncated Euler product,

    est(n) = sqrt(n)/pi * prod_{p <= P} (1 - chi_{-n}(p)/p)^(-1),

and every fundamental n in [LO, HI] with est(n) <= H exp(TOL) must be either
listed with a class number within exp(+-TOL) of est(n), or is sent to PARI
`qfbclassno`.  A PARI class number <= H for an unlisted n is a missing field;
a listed n outside tolerance, or listed but not flagged, is checked by PARI
too.

What it can catch: a dropped field at any h (the plant in the test drops one
with even h above 2000, where no published table exists), and a listed class
number that is wrong by more than the tolerance.  What it cannot catch: a
listed class number that is wrong by less than the tolerance (a field listed
at h + 1 instead of h passes), and a field whose Euler estimate overshoots its
true class number by more than exp(TOL) beyond H.  It is a detector, not a
bound: the truncated product carries no error term, and PARI is a cross-check,
not an oracle of record.
"""

from __future__ import annotations

import json
import math
import subprocess
import sys
import time
from pathlib import Path

import numpy as np

from hunts.grh_class_number import search

HERE = Path(__file__).resolve().parent
SRC = HERE / 'lsieve.c'
BIN = search.BUILD / 'lsieve'
H = 5000
REC = np.dtype([('n', '<u8'), ('e', '<f4')])


def build() -> Path:
    search.BUILD.mkdir(exist_ok=True)
    if not BIN.exists() or BIN.stat().st_mtime < SRC.stat().st_mtime:
        subprocess.run(['gcc', '-O3', '-march=native', '-o', str(BIN), str(SRC), '-lm'], check=True)
    return BIN


def candidates(lo: int, hi: int, P: int, T: float, tmp: Path):
    """(number of fundamental n in [lo, hi], n with est <= T, their estimates)."""
    r = subprocess.run([str(build()), str(lo), str(hi), str(P), repr(T), str(tmp)],
                       check=True, capture_output=True, text=True)
    nf = int(r.stdout.split()[0].split('=')[1])
    rec = np.fromfile(tmp, dtype=REC)
    return nf, rec['n'].astype(np.int64), rec['e'].astype(np.float64)


def listed_in(outdir: Path, lo: int, hi: int, X: int = 16396235837):
    """The listed (n, h) with lo <= n <= hi, read from the chunk files."""
    ns, hs = [np.zeros(0, np.int64)], [np.zeros(0, np.int64)]
    for c_lo, c_hi, *_ in search.chunks(X):
        if c_hi < lo or c_lo > hi:
            continue
        raw = search.chunk_path(outdir, c_lo, c_hi).read_bytes()
        if raw:
            a = np.array(raw.split(), dtype=np.int64).reshape(-1, 2)
            keep = (a[:, 0] >= lo) & (a[:, 0] <= hi)
            ns.append(a[keep, 0])
            hs.append(a[keep, 1])
    return np.concatenate(ns), np.concatenate(hs)


def sweep_window(lo: int, hi: int, Ln: np.ndarray, Lh: np.ndarray, P: int, tol: float,
                 tmp: Path, pari=None, H: int = H) -> dict:
    """Compare the listed (Ln, Lh) on [lo, hi] with the Euler-product candidates."""
    if pari is None:
        import cypari2
        pari = cypari2.Pari()
        pari.allocatemem(2 * 10**8)
    t0 = time.time()
    nf, rn, re_ = candidates(lo, hi, P, H * math.exp(tol), tmp)
    order = np.argsort(Ln)
    Ln, Lh = Ln[order], Lh[order]
    j = np.searchsorted(Ln, rn)
    inl = j < len(Ln)
    inl[inl] &= Ln[j[inl]] == rn[inl]
    lr = np.log(re_[inl] / Lh[j[inl]])
    covered = np.zeros(len(Ln), bool)
    covered[j[inl]] = True
    unlisted = rn[~inl]
    off = np.abs(lr) > tol
    to_check = np.concatenate([rn[inl][off], Ln[~covered]])
    missing, wrong, minh = [], [], None
    for n in unlisted.tolist():
        hp = int(pari.qfbclassno(-n))
        minh = hp if minh is None else min(minh, hp)
        if hp <= H:
            missing.append((n, hp))
    for n in to_check.tolist():
        hp = int(pari.qfbclassno(-n))
        k = int(np.searchsorted(Ln, n))
        if hp != int(Lh[k]):
            wrong.append((n, hp, int(Lh[k])))
    return dict(lo=lo, hi=hi, P=P, tol=tol, fundamental=nf, records=len(rn), listed=len(Ln),
                listed_in_records=int(inl.sum()), listed_outside_records=int((~covered).sum()),
                listed_off_tolerance=int(off.sum()), pari_unlisted=len(unlisted),
                pari_listed=len(to_check), min_h_unlisted=minh,
                log_ratio_min=float(lr.min()) if len(lr) else None,
                log_ratio_max=float(lr.max()) if len(lr) else None,
                MISSING=missing, WRONG=wrong, seconds=round(time.time() - t0, 1))


def run(outdir: Path, LO: int, HI: int, step: int, P: int, tol: float, out: Path):
    done = set()
    if out.exists():
        done = {json.loads(line)['lo'] for line in out.read_text().splitlines()}
    lo = LO
    while lo <= HI:
        hi = min(lo + step - 1, HI)
        if lo not in done:
            Ln, Lh = listed_in(outdir, lo, hi)
            row = sweep_window(lo, hi, Ln, Lh, P, tol, out.with_suffix('.bin'))
            with out.open('a') as f:
                f.write(json.dumps(row) + '\n')
            print(json.dumps({k: v for k, v in row.items() if k not in ('MISSING', 'WRONG')}), flush=True)
        lo = hi + 1


def summarise_rows(rows) -> dict:
    """Totals of a list of sweep rows (one zone)."""
    lr_min = [r['log_ratio_min'] for r in rows if r.get('log_ratio_min') is not None]
    lr_max = [r['log_ratio_max'] for r in rows if r.get('log_ratio_max') is not None]
    mh = [r['min_h_unlisted'] for r in rows if r.get('min_h_unlisted') not in (None, 10**9)]
    return dict(rows=len(rows), lo=min(r['lo'] for r in rows), hi=max(r['hi'] for r in rows),
                fundamental=sum(r['fundamental'] for r in rows),
                listed=sum(r['listed'] for r in rows),
                pari_unlisted=sum(r['pari_unlisted'] for r in rows),
                pari_listed=sum(r['pari_listed'] for r in rows),
                min_h_unlisted=min(mh) if mh else None,
                log_ratio_min=min(lr_min) if lr_min else None,
                log_ratio_max=max(lr_max) if lr_max else None,
                missing=sum(len(r['MISSING']) for r in rows),
                wrong=sum(len(r['WRONG']) for r in rows))


def _compact(r):
    if r.get('min_h_unlisted') == 10**9:        # the reviewer's sentinel for "no candidate"
        r = dict(r, min_h_unlisted=None)
    return {k: r.get(k) for k in ('lo', 'hi', 'fundamental', 'listed', 'pari_unlisted', 'pari_listed',
                                  'min_h_unlisted', 'log_ratio_min', 'log_ratio_max')} | {
        'missing': len(r['MISSING']), 'wrong': len(r['WRONG'])}


def record(reviewer_dir: Path, rerun_dir: Path):
    """controls_sweep.json from the reviewer's jsonl files and the repair rerun."""
    def rows(p):
        return [json.loads(line) for line in p.read_text().splitlines()]
    zones = {}
    for tag, name, P, tol in (('fullzone', 'sweep_fullzone.jsonl', 20000, 0.025),
                              ('fullzone_b', 'sweep_fullzone_b.jsonl', 20000, 0.025),
                              ('filterzone', 'sweep_filterzone.jsonl', 3000, 0.06)):
        rs = rows(reviewer_dir / name)
        zones[tag] = summarise_rows(rs) | {'P': P, 'tol': tol, 'chunks': [_compact(r) for r in rs]}
    c = rows(reviewer_dir / 'sweepC.jsonl')
    theorem_c = {'lo': min(r['lo'] for r in c), 'hi': max(r['hi'] for r in c),
                 'fundamental': sum(r['fundamental'] for r in c), 'pari': sum(r['pari'] for r in c),
                 'violations': sum(len(r['VIOLATIONS']) for r in c),
                 'smallest_h_over_hmax': min((r['smallest_h_over_hmax'] for r in c
                                              if r['smallest_h_over_hmax']), key=lambda t: t[0], default=None)}
    rerun = {}
    for tag, name, P, tol in (('first_chunk', 'sweep_rerun.jsonl', 20000, 0.025),
                              ('fullzone_b', 'sweep_rerun_b.jsonl', 20000, 0.025),
                              ('filterzone', 'sweep_rerun_filter.jsonl', 3000, 0.06)):
        p = rerun_dir / name
        if p.exists():
            rs = rows(p)
            rerun[tag] = summarise_rows(rs) | {'P': P, 'tol': tol,
                                                'cpu_seconds_recorded': round(sum(r['seconds'] for r in rs))}
    # does the rerun reproduce the reviewer's rows?
    same = {}
    for tag, rev in (('first_chunk', 'fullzone'), ('fullzone_b', 'fullzone_b'), ('filterzone', 'filterzone')):
        p = rerun_dir / {'first_chunk': 'sweep_rerun.jsonl', 'fullzone_b': 'sweep_rerun_b.jsonl',
                         'filterzone': 'sweep_rerun_filter.jsonl'}[tag]
        if not p.exists():
            continue
        mine = {r['lo']: _compact(r) for r in rows(p)}
        theirs = {r['lo']: r for r in zones[rev]['chunks']}
        keys = ('hi', 'fundamental', 'listed', 'pari_unlisted', 'pari_listed', 'min_h_unlisted',
                'missing', 'wrong')
        same[tag] = {'rows': len(mine),
                     'identical_rows': sum(all(mine[k][x] == theirs[k][x] for x in keys)
                                           for k in mine if k in theirs)}
    out = {
        'what': 'independent completeness sweep: truncated Euler products (lsieve.c) plus PARI qfbclassno',
        'grade': 'a detector and a cross-check, not a bound and not an oracle of record',
        'reviewer_run': {'by': 'the computation reviewer of 2026-11-20, in the session scratchpad',
                         'zones': zones, 'above_X_against_D_GRH_table': theorem_c},
        'repair_rerun': rerun, 'rerun_reproduces_reviewer': same,
        'missing_total': sum(z['missing'] for z in zones.values()) + sum(z['missing'] for z in rerun.values()),
        'wrong_total': sum(z['wrong'] for z in zones.values()) + sum(z['wrong'] for z in rerun.values()),
    }
    (HERE / 'controls_sweep.json').write_text(json.dumps(out, indent=1) + '\n')
    print(json.dumps({k: v for k, v in out.items() if k != 'reviewer_run'}, indent=1))


if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'run':
        o, lo, hi, st, p, tol, out = sys.argv[2:9]
        run(Path(o), int(lo), int(hi), int(st), int(p), float(tol), Path(out))
    elif cmd == 'record':
        record(Path(sys.argv[2]), Path(sys.argv[3]))
    else:
        raise SystemExit(__doc__)
