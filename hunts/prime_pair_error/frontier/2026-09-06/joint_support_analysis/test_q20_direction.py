"""Bounded direction test; independent exact support proof is in inspect_support.py."""
from pathlib import Path
from fractions import Fraction as F
import importlib.util,sys,json,math,time
import numpy as np
import mpmath as mp
ROOT=Path(__file__).parent
pkg=ROOT/'inputs/certificate_route_test'
s=importlib.util.spec_from_file_location('r20',pkg/'refine.py'); r=importlib.util.module_from_spec(s);s.loader.exec_module(r)
source=json.loads((ROOT/'inputs/joint_correction_candidate/joint_results.json').read_text())
base=json.loads((pkg/'inputs.json').read_text())
c={int(k):F(v) for k,v in source['new_coefficients'].items()}
star={int(k):F(v) for k,v in base['repair_coefficients'].items()}
old_H=F(source['new_tail_H'])
old_rep=set(map(int,source['repair_coefficients']))
agg=json.loads((pkg/'aggregate_results.json').read_text())
allowed={int(n) for st in agg['stages'] for n,v in st['repairs']}
M,R,den=15,100000,108
T=np.arange(R,dtype=np.int64)
def lift(z):
    w=np.zeros_like(z); scale=1
    while scale<R:
        w+=z[T//scale];scale*=M
    return w
Cstar_b=tuple(x/F(14,15) for x in r.kappa_bounds(star))
Cstar=r.kappa(star)/r.mpf(F(14,15))
oldkb=r.kappa_bounds(c)
oldbounds=tuple((oldkb[i]+old_H/R*Cstar_b[i])/F(14,15) for i in (0,1))
rows=[]
for amount in [F(1,108),F(1,2),F(1)]:
    start=time.monotonic(); cc=r.add_coeff(c,r.stencil_coeff(20),-amount)
    seed,_=r.floor_array(cc,R,den);w=lift(seed)
    fixes=[]
    for n in range(1,R):
        deficit=den-int(w[n])
        if deficit>0:
            alpha=F(deficit,den);fixes.append((n,alpha))
            cc=r.add_coeff(cc,r.bump_coeff(n),alpha)
            scale=1
            while n*scale<R:
                w[n*scale:]+=deficit*r.bump(n,T[n*scale:]//scale)
                scale*=M
    vv,_=r.floor_array(cc,R,den);assert np.array_equal(w,lift(vv))
    assert w[1:].min()>=den
    assert r.balanced(cc)
    newH=old_H+3*amount
    kb=r.kappa_bounds(cc);assert kb[0]>0
    nb=tuple((kb[i]+newH/R*Cstar_b[i])/F(14,15) for i in (0,1))
    lower=oldbounds[0]-nb[1];upper=oldbounds[1]-nb[0]
    cv=(r.kappa(cc)+r.mpf(newH)*Cstar/R)/r.mpf(F(14,15))
    rows.append({'amount':str(amount),'new_C':str(cv),'finite_mass':str(r.mass(cc)),
        'tail_H':str(newH),'net_constant_saving_bounds':r.outward_summary((lower,upper)),
        'strict_decrease':lower>0,'repair_count':len(fixes),'new_repair_sites':sum(n not in allowed for n,a in fixes),
        'first_repair_sites':[[n,str(a),n in allowed] for n,a in fixes[:30]],
        'weight20':str(F(int(w[20]),den)),'weight220':str(F(int(w[220]),den)),
        'coefficient_count':len(cc),'seconds':time.monotonic()-start,
        'all_repairs':[[n,str(a)] for n,a in fixes]})
    print({k:v for k,v in rows[-1].items() if k not in ('all_repairs','first_repair_sites')},flush=True)
(ROOT/'q20_direction_results.json').write_text(json.dumps(rows,indent=2)+'\n')
