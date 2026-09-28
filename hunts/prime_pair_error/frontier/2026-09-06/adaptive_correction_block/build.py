#!/usr/bin/env python3
"""Rebuild and check the frozen adaptive block. No LP optimality is asserted.

The original repair-cost package is read-only input. Its helper routines are
reused by this producer; check.py supplies a different implementation.
"""
from __future__ import annotations
import argparse, hashlib, json, math, sys, time, zipfile
from collections import defaultdict
from fractions import Fraction as F
from pathlib import Path
import mpmath as mp
import numpy as np
ROOT=Path(__file__).resolve().parent
ARCHIVE=ROOT/'inputs/repair_cost_rule.zip'
EXPECTED='ea5fb1ab56e3515358e7ff54ed309fe9eb1e7e87b98e3991c80b7ccc91579582'
assert hashlib.sha256(ARCHIVE.read_bytes()).hexdigest()==EXPECTED
sys.path.insert(0,str(ARCHIVE)+'/repair_cost_rule')
import repair_cost as rc
M,R,DEN=15,100000,108

def inputs():
 with zipfile.ZipFile(ARCHIVE) as z:
  assert z.testzip() is None
  read=lambda x:json.loads(z.read('repair_cost_rule/'+x))
  return read('results.json'),read('inputs/joint_results.json'),read('inputs/seeds.json')

def divisors_mu(P):
 ds={1:1}
 for p in (2,3,5,7):
  if P%p==0:ds.update({p*d:-s for d,s in list(ds.items())})
 assert math.prod(p for p in (2,3,5,7) if P%p==0)==P
 return ds

def h_coeff(row):
 q,b,c=(row[x] for x in ('q','b','c'))
 assert F(1,q)==F(1,b)+F(1,c)
 out=defaultdict(F)
 for d,s in divisors_mu(row['P']).items():
  out[d*q]+=s;out[d*b]-=s;out[d*c]-=s
 return {j:v for j,v in out.items() if v}

def wheel_bound(P):
 # F_P(n) = phi(P)*floor(n/P)+prefix[n mod P], F_P(0)=0.
 pref=np.zeros(P,dtype=np.int64)
 for n in range(1,P):pref[n]=pref[n-1]+(math.gcd(n,P)==1)
 phi=sum(math.gcd(n,P)==1 for n in range(1,P+1))
 r=np.arange(P,dtype=np.int64);low=0;high=0;tests=0
 for a in range(P):
  for e in (0,1):
   u=a+r+e
   vals=(u//P)*phi+pref[u%P]-pref[a]-pref
   low=min(low,int(vals.min()));high=max(high,int(vals.max()));tests+=P
 return {'P':P,'phi':phi,'lower':low,'upper':high,'residue_cases':tests}

def scientific_comparisons(d,fold,fnew,star,H0,Told,Tnew,Cold,Cnew):
 ans=[];aold=rc.mass(rc.add(d,fold));anew=rc.mass(rc.add(d,fnew));ad=rc.mass(d);ast=rc.mass(star)
 for N in (10**4,10**6,10**7,10**8,10**12):
  s1,s1r,s2=rc.budget_sums(N);l=1+mp.log(N)
  Uold=Cold*N+rc.fmt(aold)*l+rc.fmt(ad)*(s1-l)+rc.fmt(H0*ast)*s2+rc.fmt(Told*ast)*s1r
  Unew=Cnew*N+rc.fmt(anew)*l+rc.fmt(ad)*(s1-l)+rc.fmt(H0*ast)*s2+rc.fmt(Tnew*ast)*s1r
  Bbase=rc.base_certificate(d,H0,star,N)
  Bold=Bbase+rc.extra_certificate(fold,Told,star,N)
  Bnew=Bbase+rc.extra_certificate(fnew,Tnew,star,N)
  assert Bold<=Uold and Bnew<=Unew
  ans.append({'N':N,**{k:mp.nstr(v,70) for k,v in dict(old_B=Bold,new_B=Bnew,B_saving=Bold-Bnew,old_U=Uold,new_U=Unew,U_saving=Uold-Unew).items()}})
 return ans

def main(out):
 st=time.monotonic();old,joint,seeds=inputs();proposal=json.loads((ROOT/'selection.json').read_text())
 d=rc.load_coeff(joint['new_coefficients']);star=rc.load_coeff(seeds['repair_coefficients']);fold=rc.load_coeff(old['final_direct_coefficients'])
 H0=F(joint['new_tail_H']);Told=F(old['final_extra_tail']);assert Told==6
 w=rc.lift_array(rc.floor_array(d,R))+rc.floor_array(fold,R);assert w[1:].min()>=DEN
 wheels={P:wheel_bound(P) for P in (1,2,6,30,210)}
 hc={};H=F();actions=[]
 for row in proposal['selection']:
  y=F(row['amplitude']);assert 0<y<=1 and (108*y).denominator==1
  c=h_coeff(row);assert rc.balance(c)==0
  bound=wheels[row['P']]['upper'];assert bound==row['H']
  hc=rc.add(hc,c,y);H+=y*bound
  actions.append({k:row[k] for k in ('P','q','b','c','amplitude')})
 assert H==F(2633,108)
 raw=w-rc.floor_array(hc,R);deficits=np.maximum(DEN-raw,0);deficits[0]=0
 ds={int(n):F(int(deficits[n]),DEN) for n in np.flatnonzero(deficits)}
 fixed,patches=rc.repair(raw)
 assert patches==[(int(n),F(v)) for n,v in proposal['patches']]
 assert all(v<=ds[n] for n,v in patches)
 pc={};phic={}
 for n,v in patches:pc=rc.add(pc,rc.bump_coeff(n),v)
 for n,v in ds.items():phic=rc.add(phic,rc.bump_coeff(n),v)
 step=rc.add(pc,hc,F(-1));fnew=rc.add(fold,step);Tnew=Told+H
 assert rc.balance(step)==0 and rc.balance(fnew)==0
 assert np.array_equal(fixed,rc.lift_array(rc.floor_array(d,R))+rc.floor_array(fnew,R))
 cs=rc.scale_interval(rc.kappa_bounds(star),F(15,14))
 cb=rc.scale_interval(rc.add_interval(rc.kappa_bounds(d),rc.scale_interval(cs,H0/R)),F(15,14))
 cp=rc.add_interval(cb,rc.add_interval(rc.kappa_bounds(fold),rc.scale_interval(cs,Told/R)))
 cn=rc.add_interval(cb,rc.add_interval(rc.kappa_bounds(fnew),rc.scale_interval(cs,Tnew/R)))
 gross=rc.kappa_bounds(hc);potential=rc.kappa_bounds(phic);cost=rc.kappa_bounds(pc);tail=rc.scale_interval(cs,H/R)
 G=rc.subtract_interval(rc.subtract_interval(gross,potential),tail)
 actual=rc.subtract_interval(cp,cn)
 assert G[0]>0 and actual[0]>F(1,90) and actual[0]>G[1]
 assert rc.kappa_bounds(d)[0]>0 and rc.kappa_bounds(star)[0]>0
 deltaA=rc.mass(rc.add(d,fnew))-rc.mass(rc.add(d,fold))
 deltaT=H*rc.mass(star)
 assert deltaA==F(22097,108) and deltaT==F(13165,36)
 # Uniform U improvement for N>=10^6, as proved in the note.
 assert rc.logarithm_bounds(10)[0]>2 and rc.logarithm_bounds(10)[1]<F(7,3)
 assert rc.logarithm_bounds(15)[0]>2
 q_at_N0=deltaA*15+deltaT*F(65,9)
 assert q_at_N0<F(10**6,90)
 Cstar=rc.kappa(star)/rc.fmt(F(14,15));Cbase=(rc.kappa(d)+rc.fmt(H0)*Cstar/R)/rc.fmt(F(14,15))
 Cprev=Cbase+rc.kappa(fold)+rc.fmt(Told)*Cstar/R
 Cnew=Cbase+rc.kappa(fnew)+rc.fmt(Tnew)*Cstar/R
 early={str(n):{'old':str(F(int(w[n]),DEN)),'new':str(F(int(fixed[n]),DEN))} for n in (18,19,20,21,24,25,32,42,48,50,51,54,68,74,80)}
 record={'status':'finite all-cutoff construction; producer exact checks; no novelty, optimality, asymptotic rate or RH claim',
 'parameters':{'M':M,'R':R,'denominator':DEN},'actions':actions,'wheel_bounds':list(wheels.values()),
 'old_C':rc.interval_record(cp),'new_C':rc.interval_record(cn),'gross':rc.interval_record(gross),'raw_potential':rc.interval_record(potential),'actual_repair_cost':rc.interval_record(cost),'tail_cost':rc.interval_record(tail),'guaranteed_saving':rc.interval_record(G),'actual_saving':rc.interval_record(actual),
 'old_C_decimal':mp.nstr(Cprev,70),'new_C_decimal':mp.nstr(Cnew,70),
 'block_H':str(H),'old_extra_tail':str(Told),'new_extra_tail':str(Tnew),'unchanged_double_tail':str(H0),
 'old_first_level_mass':str(rc.mass(rc.add(d,fold))),'new_first_level_mass':str(rc.mass(rc.add(d,fnew))),
 'step_mass':str(rc.mass(step)),'correction_mass':str(rc.mass(hc)),'raw_deficit_count':len(ds),'raw_deficit_mass':str(sum(ds.values(),F())),
 'patch_count':len(patches),'patch_mass':str(sum((v for n,v in patches),F())),
 'raw_deficits':[[n,str(v)] for n,v in ds.items()],'patches':[[n,str(v)] for n,v in patches],
 'step_coefficients':rc.coeff_record(step),'final_direct_coefficients':rc.coeff_record(fnew),
 'min_prefix':str(F(int(fixed[1:].min()),DEN)),'early_weights':early,
 'comparisons':scientific_comparisons(d,fold,fnew,star,H0,Told,Tnew,Cprev,Cnew),
 'eventual_U_improvement':{'N0':10**6,'gain_lower_bound':'1/90','delta_first_mass':str(deltaA),'delta_tail_allowance':str(deltaT),'Q_at_N0_upper':str(q_at_N0),'positive_margin':str(F(10**6,90)-q_at_N0)},
 'input_sha256':EXPECTED,'seconds':time.monotonic()-st}
 out.write_text(json.dumps(record,indent=2)+'\n')
 print(json.dumps({k:v for k,v in record.items() if k not in ['raw_deficits','patches','step_coefficients','final_direct_coefficients','actions','comparisons']},indent=2))
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--output',type=Path,default=ROOT/'rerun_results.json');a=p.parse_args()
 with mp.workdps(80):main(a.output)
