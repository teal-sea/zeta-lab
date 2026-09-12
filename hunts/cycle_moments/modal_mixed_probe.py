"""Centered mixed-moment trial on Haar unitary samples.

This tests a finite random-matrix observer, not a zeta asymptotic. Its
deterministic diagonal subtraction uses the explicit finite feature space.
Run from the repo root with the Modal module and this file's path.
"""

import json
import modal

app = modal.App('zeta-mixed-moments')
image = modal.Image.debian_slim(python_version='3.11').pip_install('numpy==2.2.6')

@app.function(image=image, cpu=2, memory=4096, timeout=600, max_containers=8)
def sample(size, seed):
    import numpy as np
    rng=np.random.default_rng(seed)
    z=rng.normal(size=(size,size))+1j*rng.normal(size=(size,size))
    q,r=np.linalg.qr(z)
    q=q*(np.diag(r)/np.abs(np.diag(r))).conj()
    theta=np.angle(np.linalg.eigvals(q))
    x=(np.arange(size)-(size-1)/2)/size
    differences=np.arange(size)[:,None]-np.arange(size)[None,:]
    powers=np.exp(1j*np.arange(size)[:,None]*theta[None,:]).sum(axis=1)
    toeplitz=powers[np.abs(differences)]
    toeplitz=np.where(differences>=0,toeplitz,toeplitz.conj())
    p=np.cos(np.sqrt(2)*x); p/=p.sum()
    a=np.sqrt(p[:,None]*p[None,:])*toeplitz
    poly=3*a-a@a-2*np.eye(size)
    rows=[]
    for mu in [.06,.1,.15]:
        for center in [0.,.25]:
            r=np.where(np.abs(x-center)<mu, (1-((x-center)/mu)**2)**2, 0.)
            r/=r.sum()
            b=np.sqrt(r[:,None]*r[None,:])*toeplitz
            h=b-np.diag(size*r)
            q=h@h
            j=float(np.trace(poly@q).real/size)
            q2=float(np.sum(np.abs(q)**2)/size)
            rows.append(dict(mu=mu,center=center,J=j,Q2=q2,gain=max(j,0)**2/(9*q2)))
    return dict(size=size,seed=seed,rows=rows)

@app.local_entrypoint()
def main():
    from pathlib import Path
    results=list(sample.starmap([(256,2026090600+i) for i in range(12)]))
    Path(__file__).with_name('mixed_cue_results.json').write_text(
        json.dumps(results,indent=2)+'\n')
    for mu in [.06,.1,.15]:
        for center in [0.,.25]:
            rows=[r for s in results for r in s['rows'] if r['mu']==mu and r['center']==center]
            j=sum(r['J'] for r in rows)/len(rows)
            q2=sum(r['Q2'] for r in rows)/len(rows)
            print(dict(mu=mu,center=center,J=j,Q2=q2,gain=max(j,0)**2/(9*q2)))
