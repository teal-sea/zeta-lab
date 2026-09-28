from pathlib import Path
from fractions import Fraction
import numpy as np
import scipy.optimize as opt
import math, time, json

OUT=Path(__file__).parent
rows=[]
for L,M in [(2310,15),(30030,15)]:
    t0=time.perf_counter()
    js=np.array([j for j in range(1,L+1) if L%j==0], dtype=np.int64)
    # Balance eliminates the linear part of the floors.  This bounded
    # residual matrix is less poorly scaled than the original floors.
    r=np.arange(1,L,dtype=np.int64)
    mat=-(r[:,None]%js[None,:])/js[None,:]
    rhs=(r<M).astype(float)
    c=-np.log(js.astype(float))/js/(1-1/M)
    result=opt.linprog(c, A_ub=-mat,b_ub=-rhs,
        A_eq=(1/js.astype(float))[None,:],b_eq=[0.0],
        bounds=[(None,None)]*len(js),method='highs',
        options={'dual_feasibility_tolerance':1e-9,'primal_feasibility_tolerance':1e-9})
    if not result.success:
        raise RuntimeError(result.message)
    aa=[Fraction(float(x)).limit_denominator(1000000) for x in result.x]
    den=math.lcm(*(a.denominator for a in aa))
    ns=np.array([int(a*den) for a in aa],dtype=np.int64)
    balance=sum((a/Fraction(int(j)) for j,a in zip(js,aa)),Fraction(0))
    if balance!=0:raise ValueError(('balance',L,balance))
    # Exact integer floor constraints; choose int64 only after checking
    # a rigorous absolute bound on every intermediate dot product.
    bound=sum(abs(int(n))*(L//int(j)) for n,j in zip(ns,js))
    if bound>=2**62:raise OverflowError('use Python integers for this candidate')
    g=(r[:,None]//js[None,:])@ns
    assert np.all(g>=0)
    assert np.all(g[r<M]>=den)
    a1=aa[list(js).index(1)]
    omitted=[p for p in range(2,102) if all(p%d for d in range(2,math.isqrt(p)+1)) and (L*M)%p]
    jumps=[]
    def W(n):
        s=Fraction(0); scale=1
        while scale<=n:
            s+=sum((a*(n//(int(j)*scale)) for j,a in zip(js,aa)),Fraction(0))
            scale*=M
        return s
    for p in omitted:
        assert W(p)-W(p-1)==a1
        assert W(p)>=2
        jumps.append({'p':p,'W_before':str(W(p-1)),'W_at':str(W(p))})
    item={'L':L,'M':M,'C_float':float(c@np.array([float(a) for a in aa])),
          'A_exact':str(sum(map(abs,aa))), 'coefficients':{str(j):str(a) for j,a in zip(js,aa) if a},
          'period_constraints_checked':len(r), 'integer_denominator':den,
          'min_g_scaled':int(g.min()), 'min_cover_scaled':int(g[r<M].min()),
          'omitted_prime_checks':jumps,'seconds':time.perf_counter()-t0,
          'optimality_proved':False}
    rows.append(item)
    print(json.dumps(item),flush=True)
(OUT/'results.json').write_text(json.dumps(rows,indent=2)+'\n')
