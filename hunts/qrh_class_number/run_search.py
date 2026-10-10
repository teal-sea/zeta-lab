"""Checkpointed driver for cn.c: all fundamental D < 0, |D| <= X, h(D) <= H.

    .venv/bin/python -m hunts.qrh_class_number.run_search H X OUTDIR

Each chunk writes OUTDIR/chunk_<lo>_<hi>.txt; a chunk whose file ends with a
stats line is complete and is skipped on restart.  The summary (counts per h,
largest |D| per h, largest squarefree k per h, sha256 of the sorted list) is
written to search_H<H>.json in this directory.  The full list stays in OUTDIR.
"""

from __future__ import annotations

import hashlib
import json
import sys
import time
from pathlib import Path

from hunts.qrh_class_number import classno

HERE = Path(__file__).resolve().parent


def chunks(X: int):
    """Chunk boundaries: small chunks where the exact stage dominates."""
    edges = [3]
    step = 5 * 10**6
    while edges[-1] < X:
        nxt = edges[-1] + step
        if nxt > 10**8:
            step = 2 * 10**8
        edges.append(min(nxt, X + 1))
    return [(edges[i], edges[i + 1] - 1) for i in range(len(edges) - 1)]


def complete(path: Path) -> bool:
    if not path.exists():
        return False
    with open(path, 'rb') as f:
        f.seek(0, 2)
        size = f.tell()
        f.seek(max(0, size - 400))
        return b'# stats' in f.read()


def run(H: int, X: int, outdir: Path):
    outdir.mkdir(parents=True, exist_ok=True)
    classno.build()
    log = []
    t_all = time.time()
    for lo, hi in chunks(X):
        path = outdir / f'chunk_{lo}_{hi}.txt'
        if complete(path):
            continue
        t0 = time.time()
        classno.run(lo, hi, H, path)
        dt = time.time() - t0
        log.append((lo, hi, round(dt, 2)))
        print(f'chunk {lo}..{hi}: {dt:.1f}s', flush=True)
    return summarise(H, X, outdir, time.time() - t_all, log)


def summarise(H: int, X: int, outdir: Path, seconds: float, log):
    counts = [0] * (H + 1)
    maxn = [0] * (H + 1)
    maxk = [0] * (H + 1)
    stats_tot = {}
    rows = []
    for lo, hi in chunks(X):
        res = classno.parse(outdir / f'chunk_{lo}_{hi}.txt')
        assert res['stats']['lo'] == lo and res['stats']['hi'] == hi
        assert res['stats']['H'] == H
        for k, v in res['stats'].items():
            if k not in ('lo', 'hi', 'H'):
                stats_tot[k] = stats_tot.get(k, 0) + v
        for n, h in res['rows']:
            rows.append((n, h))
            counts[h] += 1
            maxn[h] = max(maxn[h], n)
            k = n if n % 4 == 3 else n // 4
            maxk[h] = max(maxk[h], k)
    rows.sort()
    digest = hashlib.sha256(''.join(f'{n} {h}\n' for n, h in rows).encode()).hexdigest()
    summary = {
        'H': H, 'X': X, 'chunks': len(chunks(X)),
        'stats': stats_tot, 'found': len(rows), 'sha256_sorted_list': digest,
        'count_by_h': {str(h): counts[h] for h in range(1, H + 1)},
        'max_absD_by_h': {str(h): maxn[h] for h in range(1, H + 1)},
        'max_squarefree_k_by_h': {str(h): maxk[h] for h in range(1, H + 1)},
        'max_absD_overall': max(maxn[1:]),
        'seconds_this_session': round(seconds, 1),
        'chunk_log_this_session': log,
    }
    (HERE / f'search_H{H}.json').write_text(json.dumps(summary, indent=1) + '\n')
    return summary


if __name__ == '__main__':
    H, X = int(sys.argv[1]), int(sys.argv[2])
    s = run(H, X, Path(sys.argv[3]))
    print('found', s['found'], 'max |D|', s['max_absD_overall'], s['stats'])
