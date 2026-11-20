"""Checkpointed driver for cnx.c: every fundamental D < 0, |D| <= X, h(D) <= H.

    .venv/bin/python -m hunts.grh_class_number.search plan H X OUTDIR
    .venv/bin/python -m hunts.grh_class_number.search run H X OUTDIR [workers]
    .venv/bin/python -m hunts.grh_class_number.search summarise H X OUTDIR

plan       print the chunk plan and the cost estimate (write nothing)
run        write one plan file per worker and run the workers; a chunk whose
           .stats file exists is skipped, so a stopped run resumes
summarise  recount everything from the list files with numpy (independent of
           the C tool's own histogram), hash the sorted list, compare the
           bound with the exact L(1, chi_D) of every listed field, and write
           search_H<H>.json and controls_exact_l.json here

The full list (about 1.6 GB of "n h" lines for H = 5000) stays in OUTDIR.
"""

from __future__ import annotations

import bisect
import hashlib
import json
import math
import subprocess
import sys
import time
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
SIBLING = HERE.parent / 'qrh_class_number'
BUILD = HERE / 'build'
SRC = HERE / 'cnx.c'
BIN = BUILD / 'cnx'

#: below this, mode 1 (every class number exact by enumeration of forms)
FULL_TO = 3 * 10**9
FULL_WIDTH = 5 * 10**7
FILT_WIDTH = 10**8
#: filter zones (upper end, composite cap A0, measured seconds per 10^6 of range)
ZONES = [
    (36 * 10**8, 100000, 0.80),
    (5 * 10**9, 28000, 0.62),
    (6 * 10**9, 24000, 0.50),
    (8 * 10**9, 18000, 0.43),
    (10**10, 12000, 0.31),
    (12 * 10**9, 7000, 0.25),
    (14 * 10**9, 4000, 0.21),
    (10**13, 1, 0.19),
]
#: mode 1 costs about this many seconds per 10^6 of range at n = 10^9, times sqrt(n / 10^9)
FULL_RATE = 0.52


def build(force: bool = False) -> Path:
    BUILD.mkdir(exist_ok=True)
    newest = max(SRC.stat().st_mtime, (SIBLING / 'cn.c').stat().st_mtime)
    if force or not BIN.exists() or BIN.stat().st_mtime < newest:
        subprocess.run(['gcc', '-O3', '-march=native', '-Wall', '-Wno-unused-function',
                        '-o', str(BIN), str(SRC), '-lm'], check=True)
    return BIN


def chunks(X: int):
    """(lo, hi, mode, A0, estimated seconds), ascending and adjacent."""
    out = []
    lo = 3
    while lo <= min(X, FULL_TO):
        hi = min(lo + FULL_WIDTH - 1 if lo > 3 else FULL_WIDTH, X, FULL_TO)
        mid = (lo + hi) / 2
        out.append((lo, hi, 1, 0, FULL_RATE * math.sqrt(mid / 1e9) * (hi - lo + 1) / 1e6))
        lo = hi + 1
    while lo <= X:
        cap, a0, rate = next(z for z in ZONES if lo <= z[0])
        hi = min(lo + FILT_WIDTH - 1, X, cap)
        out.append((lo, hi, 0, a0, rate * (hi - lo + 1) / 1e6))
        lo = hi + 1
    assert out[0][0] == 3 and out[-1][1] == X
    for c0, c1 in zip(out, out[1:]):
        assert c0[1] + 1 == c1[0]
    return out


def chunk_path(outdir: Path, lo: int, hi: int) -> Path:
    return outdir / f'chunk_{lo}_{hi}.txt'


def assign(cs, workers: int):
    """Greedy balance by estimated cost, largest first."""
    loads = [0.0] * workers
    plans = [[] for _ in range(workers)]
    for c in sorted(cs, key=lambda c: -c[4]):
        w = loads.index(min(loads))
        plans[w].append(c)
        loads[w] += c[4]
    for p in plans:
        p.sort()
    return plans, loads


def plan(H: int, X: int, outdir: Path, workers: int = 3):
    cs = chunks(X)
    plans, loads = assign(cs, workers)
    full = sum(c[4] for c in cs if c[2] == 1)
    filt = sum(c[4] for c in cs if c[2] == 0)
    print(f'{len(cs)} chunks: {sum(1 for c in cs if c[2] == 1)} full (est {full:.0f} s), '
          f'{sum(1 for c in cs if c[2] == 0)} filter (est {filt:.0f} s); '
          f'total est {full + filt:.0f} CPU-s; per worker {[round(x) for x in loads]}')
    return cs, plans


def run(H: int, X: int, outdir: Path, workers: int = 3):
    outdir.mkdir(parents=True, exist_ok=True)
    build()
    cs, plans = plan(H, X, outdir, workers)
    procs = []
    t0 = time.time()
    for w, p in enumerate(plans):
        if not p:
            continue
        pf = outdir / f'worker{w}.plan'
        pf.write_text(''.join(f'{lo} {hi} {mode} {a0} {chunk_path(outdir, lo, hi)}\n'
                              for lo, hi, mode, a0, _ in p))
        log = open(outdir / f'worker{w}.log', 'a')
        procs.append(subprocess.Popen([str(BIN), str(H), str(pf)], stdout=log, stderr=log))
    rcs = [p.wait() for p in procs]
    print('workers finished', rcs, f'{time.time() - t0:.0f} s wall')
    if any(rcs):
        raise SystemExit(1)


def read_stats(path: Path):
    lines = Path(str(path) + '.stats').read_text().splitlines()
    assert lines[0].startswith('# stats')
    st = {k: int(v) for k, v in (tok.split('=') for tok in lines[0].split()[2:])}
    hist = {}
    for line in lines[1:]:
        h, c, m = line.split()
        hist[int(h)] = (int(c), int(m))
    return st, hist


def _digest_rows(n: np.ndarray, h: np.ndarray) -> bytes:
    return ''.join(f'{a} {b}\n' for a, b in zip(n.tolist(), h.tolist())).encode()


def summarise(H: int, X: int, outdir: Path):
    t0 = time.time()
    cs = chunks(X)
    dt = json.loads((HERE / 'dtable_grh.json').read_text())
    cells = dt['intervals']
    for c0, c1 in zip(cells, cells[1:]):
        assert c0['q_hi'] == c1['q_lo']
    cell_hi = np.array([c['q_hi'] for c in cells], dtype=np.int64)
    cell_L = np.array([c['L_lower'] for c in cells])
    cell_first = cells[0]['q_lo']

    counts = np.zeros(H + 1, dtype=np.int64)
    maxn = np.zeros(H + 1, dtype=np.int64)
    maxk = np.zeros(H + 1, dtype=np.int64)
    c_counts = np.zeros(H + 1, dtype=np.int64)       # the C tool's own histogram
    c_maxn = np.zeros(H + 1, dtype=np.int64)
    tot = {}
    zone_seconds = {}
    sha_all = hashlib.sha256()
    subs = {k: hashlib.sha256() for k in (100, 1000, 1500, 2000) if k < H}
    sub_counts = {k: 0 for k in subs}
    worst = (math.inf, 0, 0)
    n_margin = 0
    margins_hist = np.zeros(60, dtype=np.int64)      # margin in [1 + k/20, 1 + (k+1)/20)
    prev_last = 0
    for lo, hi, mode, a0, _ in cs:
        path = chunk_path(outdir, lo, hi)
        st, hist = read_stats(path)
        assert (st['lo'], st['hi'], st['H'], st['mode'], st['A0']) == (lo, hi, H, mode, a0), st
        for k in ('fundamental', 'stream_survivors', 'exact', 'found'):
            tot[k] = tot.get(k, 0) + st[k]
        key = 'full' if mode else f'filter_A0_{a0}'
        zone_seconds[key] = zone_seconds.get(key, 0) + st['ms'] / 1000
        for h, (c, m) in hist.items():
            c_counts[h] += c
            c_maxn[h] = max(c_maxn[h], m)
        raw = path.read_bytes()
        sha_all.update(raw)
        if not raw:
            assert st['found'] == 0
            continue
        arr = np.fromfile(path, dtype=np.int64, sep=' ').reshape(-1, 2)
        n, h = arr[:, 0], arr[:, 1]
        assert len(n) == st['found']
        assert n[0] > prev_last and n[0] >= lo and n[-1] <= hi
        assert np.all(np.diff(n) > 0), 'list not strictly increasing'
        prev_last = int(n[-1])
        assert h.min() >= 1 and h.max() <= H
        # every row is a fundamental discriminant candidate by residue
        r16 = n % 16
        assert np.all((n % 4 == 3) | (r16 == 4) | (r16 == 8))
        counts += np.bincount(h, minlength=H + 1)
        maxn[h] = n                                   # n ascending: the last write is the largest
        odd = n % 4 == 3
        ko = np.zeros(H + 1, dtype=np.int64)
        ke = np.zeros(H + 1, dtype=np.int64)
        ko[h[odd]] = n[odd]
        ke[h[~odd]] = n[~odd] // 4
        maxk = np.maximum(maxk, np.maximum(ko, ke))
        for k in subs:
            sel = h <= k
            if sel.any():
                subs[k].update(_digest_rows(n[sel], h[sel]))
                sub_counts[k] += int(sel.sum())
        # control: exact L(1, chi_D) = pi h / sqrt(n) against the bound of the cell holding n
        sel = n >= cell_first
        if sel.any():
            nn, hh = n[sel], h[sel]
            idx = np.searchsorted(cell_hi, nn, side='left')
            Lex = math.pi * hh / np.sqrt(nn.astype(np.float64))
            marg = Lex / cell_L[idx]
            n_margin += len(nn)
            j = int(np.argmin(marg))
            if marg[j] < worst[0]:
                worst = (float(marg[j]), int(nn[j]), int(hh[j]))
            b = np.minimum(((marg - 1) * 20).astype(np.int64), 59)
            assert b.min() >= 0, 'a listed field violates the bound'
            margins_hist += np.bincount(b, minlength=60)
    assert np.array_equal(counts, c_counts), 'numpy recount differs from the C histogram'
    assert np.array_equal(maxn, c_maxn)
    assert int(counts.sum()) == tot['found']
    # the bound holds for every unlisted discriminant below x_ctrl as well: there
    # h(D) > H while the bound is at most H
    x_ctrl = cell_first
    for c in cells:
        if math.sqrt(c['q_hi']) * c['L_lower'] / math.pi <= H and c['q_hi'] <= X:
            x_ctrl = c['q_hi']
        else:
            break
    k_w = bisect.bisect_left(cell_hi.tolist(), worst[1])
    summary = {
        'H': H, 'X': X, 'chunks': len(cs),
        'plan': {'full_to': FULL_TO, 'full_width': FULL_WIDTH, 'filter_width': FILT_WIDTH,
                 'zones': [[z[0], z[1]] for z in ZONES]},
        'stats': tot, 'found': int(counts.sum()),
        'sha256_sorted_list': sha_all.hexdigest(),
        'sha256_sublist_h_le': {str(k): v.hexdigest() for k, v in subs.items()},
        'count_sublist_h_le': {str(k): v for k, v in sub_counts.items()},
        'cumulative_by_hundreds': {str(k): [int(counts[1:k + 1].sum()), int(maxn[1:k + 1].max())]
                                   for k in range(100, H + 1, 100)},
        'count_by_h': {str(h): int(counts[h]) for h in range(1, H + 1)},
        'max_absD_by_h': {str(h): int(maxn[h]) for h in range(1, H + 1)},
        'max_squarefree_k_by_h': {str(h): int(maxk[h]) for h in range(1, H + 1)},
        'max_absD_overall': int(maxn.max()),
        'chunk_cpu_seconds_by_zone': {k: round(v, 1) for k, v in zone_seconds.items()},
        'chunk_cpu_seconds_total': round(sum(zone_seconds.values()), 1),
        'cn_c_sha256': hashlib.sha256((SIBLING / 'cn.c').read_bytes()).hexdigest(),
        'cnx_c_sha256': hashlib.sha256(SRC.read_bytes()).hexdigest(),
    }
    (HERE / f'search_H{H}.json').write_text(json.dumps(summary, indent=1) + '\n')
    control = {
        'statement': 'exact L(1, chi_D) = pi h(D) / sqrt|D| against the Arb-enclosed lower bound of '
                     'the dtable_grh.json cell containing |D|',
        'listed_fields_checked': n_margin, 'range_listed': [cell_first, X],
        'worst_margin': {'margin': worst[0], 'absD': worst[1], 'h': worst[2],
                         'L_exact': math.pi * worst[2] / math.sqrt(worst[1]),
                         'L_lower_bound': cells[k_w]['L_lower']},
        'margin_histogram_bins_of_0.05_from_1': margins_hist.tolist(),
        'all_discriminants_range': [cell_first, x_ctrl],
        'all_discriminants_count': None,
        'all_discriminants_note': 'for |D| <= x_ctrl an unlisted fundamental discriminant has h > H while '
                                  'sqrt|D| * bound / pi <= H, so the bound holds there too',
    }
    (HERE / 'controls_exact_l.json').write_text(json.dumps(control, indent=1) + '\n')
    print(json.dumps({k: v for k, v in summary.items()
                      if k not in ('count_by_h', 'max_absD_by_h', 'max_squarefree_k_by_h',
                                   'cumulative_by_hundreds')}, indent=1))
    print(json.dumps(control['worst_margin']), 'x_ctrl', x_ctrl, f'{time.time() - t0:.0f} s')
    return summary


if __name__ == '__main__':
    cmd, H, X, outdir = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), Path(sys.argv[4])
    if cmd == 'plan':
        plan(H, X, outdir)
    elif cmd == 'run':
        run(H, X, outdir, int(sys.argv[5]) if len(sys.argv) > 5 else 3)
    else:
        summarise(H, X, outdir)
