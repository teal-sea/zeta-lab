#!/usr/bin/env python3
"""Reproduce the exploratory dictionary search and its two LP proposals.

Numerical search is only a proposer. build.py and check.py test the retained
rational block. No claim of exhaustive search or exact optimization optimality.
"""
from __future__ import annotations
import argparse,json,math,time
from fractions import Fraction as F
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix,eye,hstack
import build as b
rc=b.rc

def main(out):
 if out.exists():raise FileExistsError(f'Refusing to overwrite {out}; choose a fresh output directory')
 out.mkdir(parents=True);start=time.monotonic()
 old,joint,seeds=b.inputs();d=rc.load_coeff(joint['new_coefficients']);fold=rc.load_coeff(old['final_direct_coefficients']);star=rc.load_coeff(seeds['repair_coefficients'])
 w=rc.lift_array(rc.floor_array(d,b.R))+rc.floor_array(fold,b.R)
 t=np.arange(b.R,dtype=np.int64);k=np.zeros(b.R);k[1:]=np.log1p(1/t[1:])/t[1:]+np.log(t[1:])/(t[1:]*(t[1:]+1))
 Cstar=float(rc.kappa(star)/(14/15))
 wheels={}
 for P in (1,2,6,30,210):
  pref=np.zeros(P,dtype=np.int64)
  for n in range(1,P):pref[n]=pref[n-1]+(math.gcd(n,P)==1)
  phi=sum(math.gcd(n,P)==1 for n in range(1,P+1))
  wheels[P]=(pref,phi,b.wheel_bound(P)['upper'])
 def arr(P,a,c,e):
  pref,phi,_=wheels[P]
  def count(z):return (z//P)*phi+pref[z%P]
  return count(t//a)-count(t//c)-count(t//e)
 def score(P,a,c,e):
  pref,phi,H=wheels[P];h=arr(P,a,c,e)
  raw=np.maximum(b.DEN-w+b.DEN*h,0);raw[0]=0
  gross=phi/P*(math.log(c)/c+math.log(e)/e-math.log(a)/a)
  pot=float(raw@k/b.DEN)
  return dict(P=P,q=a,b=c,c=e,H=H,gain=gross-pot-H*Cstar/b.R,gross=gross,pot=pot,defsum=float(raw.sum()/b.DEN),raw_count=int(np.count_nonzero(raw)))
 rows=[]
 for P in wheels:
  for a in range(2,81):
   if w[a]<=b.DEN:continue
   for v in range(1,a+1):
    if a*a%v==0:rows.append(score(P,a,a+v,a+a*a//v))
 rows.sort(key=lambda x:-x['gain'])
 (out/'scouting_scores.json').write_text(json.dumps(rows,indent=2)+'\n')
 def key(x):return tuple(x[k] for k in ('P','q','b','c'))
 def normallow(x):return 3*len(b.divisors_mu(x['P']))
 chosen={}
 for x in rows[:16]:chosen[key(x)]=x
 for x in sorted([r for r in rows if r['gain']>0],key=lambda x:-x['gain']/(normallow(x)+3*x['defsum']+15*x['H']))[:16]:chosen[key(x)]=x
 for a in (18,19,20,21,24,25,32):
  x=score(210,a,a+1,a*(a+1));chosen[key(x)]=x
 proposals=list(chosen.values());matrix=np.stack([arr(x['P'],x['q'],x['b'],x['c']) for x in proposals],axis=1)
 slack=(w-b.DEN)/b.DEN;slack[0]=0
 ix=np.flatnonzero(np.maximum(matrix,0).sum(axis=1)>slack);ix=ix[ix>0]
 constraints=hstack((csr_matrix(matrix[ix]),-eye(len(ix))),format='csr')
 cs=np.array([x['gross']-x['H']*Cstar/b.R for x in proposals]);summary=[]
 for policy in ('gain','envelope'):
  obj=-cs.copy();dobj=k[ix].copy()
  if policy=='envelope':
   N=10**8;log=1+math.log(N);s1r=float(rc.budget_sums(N)[1])
   obj+=(np.array([normallow(x) for x in proposals])*log+15*np.array([x['H'] for x in proposals])*s1r)/N
   dobj+=3*log/N
  sol=linprog(np.r_[obj,dobj]*1e6,A_ub=constraints,b_ub=slack[ix],bounds=[(0,1)]*len(proposals)+[(0,None)]*len(ix),method='highs')
  if not sol.success:raise RuntimeError(sol.message)
  # Rounding need not preserve LP feasibility: deficits are recomputed and
  # repairs are rebuilt afterwards. Exact acceptance happens in build.py.
  yn=np.rint(sol.x[:len(proposals)]*b.DEN).astype(np.int64)
  hs=matrix@yn;dd=np.maximum(b.DEN-w+hs,0);dd[0]=0
  gross=sum(x['gross']*int(y)/b.DEN for x,y in zip(proposals,yn));H=sum((F(int(y),b.DEN)*x['H'] for x,y in zip(proposals,yn)),F())
  G=gross-float(dd@k/b.DEN)-float(H)*Cstar/b.R
  repaired,patches=rc.repair(w-hs)
  C=float(old['final_C']['lower_decimal'])-gross+sum(float(v)*k[n] for n,v in patches)+float(H)*Cstar/b.R
  record=dict(policy=policy,selection=[dict(x,amplitude=str(F(int(y),b.DEN))) for x,y in zip(proposals,yn) if y],guaranteed_gain_float=G,actual_C_float=C,patches=[[n,str(v)] for n,v in patches],H=str(H),all_proposals=proposals,solver_message=sol.message,rounding_denominator=b.DEN)
  (out/f'{policy}.json').write_text(json.dumps(record,indent=2)+'\n');summary.append({'policy':policy,'actions':len(record['selection']),'C_float':C})
  if policy=='gain':
   saved=json.loads((b.ROOT/'selection.json').read_text())
   small=lambda r:[{k:x[k] for k in ('P','q','b','c','amplitude')} for x in r['selection']]
   assert small(record)==small(saved) and record['patches']==saved['patches']
 print(json.dumps({'scouted':len(rows),'block_variables':len(proposals),'active_constraints':len(ix),'results':summary,'seconds':time.monotonic()-start},indent=2))
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--output-dir',type=Path,required=True);a=p.parse_args();main(a.output_dir)
