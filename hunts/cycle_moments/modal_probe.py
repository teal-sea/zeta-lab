"""Finite CUE experiments for choosing a cycle-moment counting score.

This is a random-matrix experiment, not an estimate for zeta zeros. Run with
`.venv/bin/python -m modal run hunts/cycle_moments/modal_probe.py`.
"""

import json
from pathlib import Path

import modal

app = modal.App('zeta-cycle-moments')
image = modal.Image.debian_slim(python_version='3.11').pip_install('numpy==2.2.6')


@app.function(image=image, cpu=2, memory=4096, timeout=600, max_containers=8)
def sample(size: int, seed: int):
    import numpy as np
    rng = np.random.default_rng(seed)
    z = rng.normal(size=(size, size))+1j*rng.normal(size=(size, size))
    q, r = np.linalg.qr(z)
    q = q*(np.diag(r)/np.abs(np.diag(r))).conj()
    theta = np.angle(np.linalg.eigvals(q))
    out = []
    for width in [0.5, 1.0]:
        modes = int(round(width*size))
        frequencies = (np.arange(modes)-(modes-1)/2)/size
        differences = np.arange(modes)[:, None]-np.arange(modes)[None, :]
        powers = np.exp(1j*np.arange(modes)[:, None]*theta[None, :]).sum(axis=1)
        toeplitz = powers[np.abs(differences)]
        toeplitz = np.where(differences >= 0, toeplitz, toeplitz.conj())
        for profile in ['uniform', 'montgomery_taylor']:
            weights = (np.ones(modes) if profile == 'uniform'
                       else np.cos(np.sqrt(2)*frequencies))
            weights /= weights.sum()
            a = np.sqrt(weights[:, None]*weights[None, :])*toeplitz
            a2 = a@a
            moments = [float(np.trace(a).real/size),
                       float(np.trace(a2).real/size),
                       float(np.einsum('ij,ji->', a2, a).real/size),
                       float(np.sum(np.abs(a2)**2)/size)]
            c1, c2, c3, c4 = moments
            grid = np.linspace(-0.75, 0.75, 1501)
            scores = (2*c1-c2-grid*(c3-3*c2+2*c1)
                      +grid**2*(2*c1-5*c2+4*c3-c4))/(1+grid**2/(4*(1-grid**2)))
            best = int(np.argmax(scores))
            out.append({'width': width, 'profile': profile, 'moments': moments,
                        'quadratic_score': 2*c1-c2,
                        'best_score_measured': float(scores[best]),
                        'best_t_measured': float(grid[best])})
    return {'size': size, 'seed': seed, 'results': out}


@app.local_entrypoint()
def main():
    jobs = [(size, 2026090500+10000*size+j)
            for size in [128, 256, 512] for j in range(12)]
    results = list(sample.starmap(jobs))
    path = Path(__file__).with_name('cue_results.json')
    path.write_text(json.dumps({'status': 'finite random-matrix experiment',
                                'jobs': len(jobs), 'samples': results}, indent=2)+'\n')
    print(f'Wrote {len(results)} samples to {path}')
