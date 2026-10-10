"""Controls: the bound against exact L(1, chi_D), the abscissa ladder, Watkins.

    .venv/bin/python -m hunts.qrh_class_number.controls exact_l OUTDIR
    .venv/bin/python -m hunts.qrh_class_number.controls watkins H

exact_l   every fundamental D < 0 with |D| <= 3*10^6: exact h(D) from cn.c
          (no early exit), L(1, chi_D) = 2 pi h / (w sqrt|D|), compared with
          the verified lower bound of the dtable interval containing |D|;
          also the smallest |D| from which L * log log |D| >= 1/10 holds
          throughout the exact range, and PARI lfun at sampled D as an
          independent route to L(1, chi_D).
watkins   counts and largest discriminants for h <= 100 against OEIS
          A046125 / A038552 (Watkins 2004).
pari      PARI qfbclassno (Shanks; an independent implementation, used as a
          cross-check only) at the largest |D| for every h <= H and at 400
          random entries of the search output.
"""

from __future__ import annotations

import bisect
import json
import math
import sys
from pathlib import Path

from hunts.qrh_class_number import classno

HERE = Path(__file__).resolve().parent
X_EXACT = 3 * 10**6


def exact_l(outdir: Path):
    outdir.mkdir(parents=True, exist_ok=True)
    path = outdir / f'full_{X_EXACT}.txt'
    if not (path.exists() and 'stats' in path.read_text()[-300:]):
        classno.run(3, X_EXACT, 20000, path)
    res = classno.parse(path)
    rows = res['rows']
    assert res['stats']['found'] == res['stats']['fundamental'] == len(rows)
    dt = json.loads((HERE / 'dtable.json').read_text())
    ivs = dt['intervals']
    his = [r['q_hi'] for r in ivs]
    worst = None
    n_checked = 0
    for n, h in rows:
        if n < ivs[0]['q_lo']:
            continue
        w = 6 if n == 3 else (4 if n == 4 else 2)
        L = 2 * math.pi * h / (w * math.sqrt(n))
        k = bisect.bisect_left(his, n)        # interval with q_lo <= n <= q_hi
        r = ivs[k]
        assert r['q_lo'] <= n <= r['q_hi']
        margin = L / r['L_lower']
        n_checked += 1
        if worst is None or margin < worst[0]:
            worst = (margin, n, h, L, r['L_lower'])
    # smallest D0 with L * loglog|D| >= 1/10 for all D0 <= |D| <= X_EXACT
    bad = [n for n, h in rows if n >= 3 and
           2 * math.pi * h / ((6 if n == 3 else 4 if n == 4 else 2) * math.sqrt(n))
           * math.log(math.log(n)) < 0.1]
    d0 = (max(bad) + 1) if bad else 3
    minprod = min((math.pi * h / math.sqrt(n)) * math.log(math.log(n))
                  for n, h in rows if n >= d0 and n > 4)
    # PARI lfun at sampled D: an independent route to L(1, chi_D)
    import cypari2
    pari = cypari2.Pari()
    pari.set_real_precision(30)
    sample = [r for r in rows if r[0] in (3, 4, 7, 163, 427, 907, 2383747, 2995523)]
    sample += rows[:: max(1, len(rows) // 25)]
    lchk = []
    for n, h in sample:
        w = 6 if n == 3 else (4 if n == 4 else 2)
        L = 2 * math.pi * h / (w * math.sqrt(n))
        Lp = float(pari(f'lfun(lfuncreate({-n}), 1)'))
        lchk.append({'absD': n, 'h': h, 'L_class_number_formula': L, 'L_pari_lfun': Lp,
                     'rel_diff': abs(L - Lp) / L})
    out = {
        'range': [3, X_EXACT], 'fundamental_checked': n_checked,
        'worst_margin': {'margin': worst[0], 'absD': worst[1], 'h': worst[2],
                         'L_exact': worst[3], 'L_lower_bound': worst[4]},
        'theorem_a_small_range': {'D0': d0, 'min_L_loglogq_from_D0': minprod},
        'pari_lfun_sample': lchk,
        'max_rel_diff_pari': max(x['rel_diff'] for x in lchk),
        'sha256_full_list': classno.digest(rows),
    }
    (HERE / 'controls_exact_l.json').write_text(json.dumps(out, indent=1) + '\n')
    print(json.dumps({k: v for k, v in out.items() if k != 'pari_lfun_sample'}, indent=1))


def watkins(H: int):
    s = json.loads((HERE / f'search_H{H}.json').read_text())
    w = json.loads((HERE / 'watkins.json').read_text())
    bad = []
    for h in range(1, 101):
        a, b = s['count_by_h'][str(h)], w['count_by_h'][str(h)]
        k1, k2 = s['max_squarefree_k_by_h'][str(h)], w['max_squarefree_k_by_h'][str(h)]
        if a != b or k1 != k2:
            bad.append((h, a, b, k1, k2))
    total = sum(s['count_by_h'][str(h)] for h in range(1, 101))
    out = {'H_search': H, 'mismatches': bad, 'total_h_le_100': total,
           'watkins_total': w['total'],
           'largest_absD_h_le_100': max(s['max_absD_by_h'][str(h)] for h in range(1, 101))}
    print(out)
    return out


def pari(H: int, outdir: Path):
    import random
    from hunts.qrh_class_number import run_search
    s = json.loads((HERE / f'search_H{H}.json').read_text())
    rows = []
    for lo, hi in run_search.chunks(s['X']):
        rows += classno.parse(outdir / f'chunk_{lo}_{hi}.txt')['rows']
    pick = {n: h for n, h in rows if n == s['max_absD_by_h'][str(h)]}
    rng = random.Random(124)
    for n, h in rng.sample(rows, 400):
        pick[n] = h
    bad = [(n, h, classno.pari_h(n)) for n, h in sorted(pick.items()) if classno.pari_h(n) != h]
    sub = {}
    for k in (100, 1000):
        if k < H:
            sub[str(k)] = classno.digest([(n, h) for n, h in rows if h <= k])
    out = {'H': H, 'checked': len(pick), 'mismatches': bad,
           'largest_checked': max(pick), 'sha256_sublist_h_le': sub}
    (HERE / f'controls_pari_H{H}.json').write_text(json.dumps(out, indent=1) + '\n')
    print(out)


if __name__ == '__main__':
    if sys.argv[1] == 'exact_l':
        exact_l(Path(sys.argv[2]))
    elif sys.argv[1] == 'pari':
        pari(int(sys.argv[2]), Path(sys.argv[3]))
    else:
        watkins(int(sys.argv[2]))
