#!/usr/bin/env python3
"""Separate-code exact self-check. Imports neither build.py nor baseline code.

Uses divisor events rather than the producer's numpy floor arrays, an event-based
repair recurrence, and mpmath interval logs/log-gamma rather than rational log
series. This is still a self-check by the originating session, not peer review.
"""
from __future__ import annotations
import argparse,hashlib,json,math,time,zipfile
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path
import mpmath as mp
ROOT=Path(__file__).resolve().parent
M,R,S=15,100000,108

def parse(c):return {int(k):Q(v) for k,v in c.items() if Q(v)}
def plus(a,b,m=Q(1)):
 c=defaultdict(Q,a)
 for j,v in b.items():c[j]+=m*v
 return {j:v for j,v in c.items() if v}
def norm(c):return sum(map(abs,c.values()),Q())
def bal(c):return sum((v/j for j,v in c.items()),Q())
def mu(n):
 s=1;p=2
 while p*p<=n:
  if n%p==0:
   n//=p;s=-s
   if n%p==0:return 0
  p+=1
 return -s if n>1 else s

def stencil(P,a,b,c):
 assert Q(1,a)==Q(1,b)+Q(1,c)
 ans=defaultdict(Q)
 for d in range(1,P+1):
  if P%d==0:
   ans[d*a]+=mu(d);ans[d*b]-=mu(d);ans[d*c]-=mu(d)
 return {j:v for j,v in ans.items() if v}
def bump(n):
 out=defaultdict(Q);out[n]+=1;out[n+1]-=1;out[n*(n+1)]-=1
 return {j:v for j,v in out.items() if v}
def scaled(c,k,v=Q(1)):return {j*k:a*v for j,a in c.items()}
def lift(c,N):
 out={};k=1
 while k<=N:
  out=plus(out,scaled(c,k));k*=M
 return out

def event_values(c,N,den=S):
 inc=[0]*N
 for j,v in c.items():
  x=v*den;assert x.denominator==1
  for n in range(j,N,j):inc[n]+=x.numerator
 out=[];s=0
 for v in inc:s+=v;out.append(s)
 return out

def interval(q):
 q=Q(q);return mp.iv.mpf(q.numerator)/q.denominator

def ki(c):return -sum((interval(v)*mp.iv.log(j)/j for j,v in c.items()),mp.iv.mpf(0))
def fmt(x):
 def rational(t):
  sign,man,exp,_=t
  return Q(-man if sign else man)*Q(2)**exp
 lo,hi=(rational(t) for t in x._mpi_)
 scale=10**55
 a=(lo.numerator*scale)//lo.denominator
 b=-((-hi.numerator*scale)//hi.denominator)
 def decimal(n):
  sign='-' if n<0 else '';n=abs(n)
  return sign+str(n//scale)+'.'+str(n%scale).zfill(55)
 return {'lower':decimal(a),'upper':decimal(b),'lower_exact':str(lo),'upper_exact':str(hi),'width_exact':str(hi-lo)}
def agrees(x,rec):
 lo=interval(Q(rec['lower']));hi=interval(Q(rec['upper']))
 assert x.a>=lo.a and x.b<=hi.b

def certificate_coeff(d,f,star,H0,T,N):
 c=plus(lift(d,N),f);scale=R;m=0
 while scale<=N:
  c=plus(c,scaled(star,scale,H0*(m+1)+T));m+=1;scale*=M
 return c

def main(source,out):
 t0=time.monotonic();p=ROOT/'inputs/repair_cost_rule.zip'
 assert hashlib.sha256(p.read_bytes()).hexdigest()=='ea5fb1ab56e3515358e7ff54ed309fe9eb1e7e87b98e3991c80b7ccc91579582'
 with zipfile.ZipFile(p) as z:
  assert z.testzip() is None
  get=lambda n:json.loads(z.read('repair_cost_rule/'+n))
  old=get('results.json');joint=get('inputs/joint_results.json');seeds=get('inputs/seeds.json')
 rec=json.loads(source.read_text());d=parse(joint['new_coefficients']);star=parse(seeds['repair_coefficients']);fold=parse(old['final_direct_coefficients'])
 H0=Q(joint['new_tail_H']);Told=Q(old['final_extra_tail'])
 assert bal(d)==bal(star)==bal(fold)==0
 seedvals=event_values(star,2310,1);assert min(seedvals)>=0 and min(seedvals[1:15])>=1
 mp.mp.dps=90;mp.iv.dps=80
 assert ki(d).a>0 and ki(star).a>0
 cstar=ki(star)/interval(Q(14,15));cbase=(ki(d)+interval(H0/R)*cstar)/interval(Q(14,15))
 cprev=cbase+ki(fold)+interval(Told/R)*cstar
 agrees(cprev,rec['old_C'])
 # Universal carry bounds: exactly 2P^2 cases, independent of the start q.
 bounds={};wheel_cases=0
 for item in rec['wheel_bounds']:
  P=item['P'];F=[0]
  for n in range(1,2*P+1):F.append(F[-1]+(math.gcd(n,P)==1))
  vals=[F[i+j+e]-F[i]-F[j] for i in range(P) for j in range(P) for e in (0,1)]
  assert min(vals)==item['lower'] and max(vals)==item['upper']
  bounds[P]=max(vals);wheel_cases+=len(vals)
 hc={};H=Q();period_cases=0
 for item in rec['actions']:
  P,a,b,c=(item[k] for k in ('P','q','b','c'));y=Q(item['amplitude'])
  assert 0<y<=1
  h=stencil(P,a,b,c);assert bal(h)==0
  # This period is independent of any numerical samples at huge t.
  L=math.lcm(*h);assert all(L%j==0 for j in h)
  values=event_values(h,L,1);period_cases+=L
  assert max(values)<=bounds[P] and min(values)>=(-bounds[P] if P>1 else 0)
  assert values[:a]==[0]*a and values[a]==1
  hc=plus(hc,h,y);H+=y*bounds[P]
 assert H==Q(rec['block_H'])==Q(2633,108)
 oldc=plus(lift(d,R-1),fold);w=event_values(oldc,R);assert min(w[1:])>=S
 raw=event_values(plus(oldc,hc,-1),R)
 ds={n:Q(S-v,S) for n,v in enumerate(raw) if n>0 and v<S}
 assert ds=={n:Q(v) for n,v in rec['raw_deficits']}
 # Independent greedy recurrence, by event scheduling instead of suffix arrays.
 events=[0]*R;repair_weight=0;patches={};covered=[]
 for n in range(1,R):
  repair_weight+=events[n]
  v=raw[n]+repair_weight
  if v<S:
   z=S-v;patches[n]=Q(z,S);repair_weight+=z;v+=z
   for m in range(2*n,R,n):events[m]+=z
   for m in range(n+1,R,n+1):events[m]-=z
   for m in range(n*(n+1),R,n*(n+1)):events[m]-=z
  assert v>=S;covered.append(v)
 assert patches=={n:Q(v) for n,v in rec['patches']}
 assert all(0<=v<=ds[n] for n,v in patches.items())
 pc={};phic={}
 for n,v in patches.items():pc=plus(pc,bump(n),v)
 for n,v in ds.items():phic=plus(phic,bump(n),v)
 step=plus(pc,hc,-1);fnew=plus(fold,step)
 assert step==parse(rec['step_coefficients']) and fnew==parse(rec['final_direct_coefficients'])
 assert bal(step)==bal(fnew)==0
 rebuilt=event_values(plus(lift(d,R-1),fnew),R)
 assert rebuilt[1:]==covered and min(covered)==S
 assert norm(plus(d,fnew))==Q(rec['new_first_level_mass'])==Q(28306,27)
 assert norm(plus(d,fold))==Q(91127,108)
 assert len(ds)==498 and len(patches)==82
 assert sum(ds.values(),Q())==Q(48119,108) and sum(patches.values(),Q())==Q(5243,108)
 gross=ki(hc);phi=ki(phic);paid=ki(pc);tail=interval(H/R)*cstar
 guarantee=gross-phi-tail;actual=gross-paid-tail;cnew=cprev-actual
 for value,name in [(gross,'gross'),(phi,'raw_potential'),(paid,'actual_repair_cost'),(tail,'tail_cost'),(guarantee,'guaranteed_saving'),(actual,'actual_saving'),(cnew,'new_C')]:agrees(value,rec[name])
 assert guarantee.a>0 and actual.a>interval(Q(1,90)).b
 Tnew=Told+H;assert Tnew==Q(rec['new_extra_tail'])==Q(3281,108)
 comparisons=[]
 Anew=norm(plus(d,fnew));Aold=norm(plus(d,fold));Ad=norm(d);As=norm(star)
 for N in (10**4,10**6,10**7,10**8,10**12):
  scale=1;s1=mp.iv.mpf(0)
  while scale<=N:s1+=1+mp.iv.log(interval(N)/scale);scale*=15
  scale=R;s1r=mp.iv.mpf(0);s2=mp.iv.mpf(0);m=0
  while scale<=N:
   x=1+mp.iv.log(interval(N)/scale);s1r+=x;s2+=(m+1)*x;scale*=15;m+=1
  log=1+mp.iv.log(N)
  Uold=cprev*N+interval(Aold)*log+interval(Ad)*(s1-log)+interval(H0*As)*s2+interval(Told*As)*s1r
  Unew=cnew*N+interval(Anew)*log+interval(Ad)*(s1-log)+interval(H0*As)*s2+interval(Tnew*As)*s1r
  def B(f,T):
   coeff=certificate_coeff(d,f,star,H0,T,N)
   return sum((interval(v)*mp.iv.loggamma(N//j+1) for j,v in coeff.items() if N//j>=2),mp.iv.mpf(0))
  Bold=B(fold,Told);Bnew=B(fnew,Tnew)
  assert (Uold-Bold).a>0 and (Unew-Bnew).a>0
  assert (Bold-Bnew).a>0
  if N>=10**6:assert (Uold-Unew).a>0
  else:assert (Uold-Unew).b<0
  comparisons.append({'N':N,'B_saving':fmt(Bold-Bnew),'U_saving':fmt(Uold-Unew)})
 # Exact factorial exponent identities via a separate sieve.
 sieve=[True]*10001;sieve[0]=sieve[1]=False
 for a in range(2,101):
  if sieve[a]:
   for n in range(a*a,10001,a):sieve[n]=False
 primes=[n for n in range(2,10001) if sieve[n]];exponents=0
 for N in (2000,10000):
  coeff=certificate_coeff(d,fnew,star,H0,Tnew,N)
  for p in primes:
   if p>N:break
   lhs=Q();rhs=Q();power=p
   while power<=N:
    lhs+=sum((v*((N//j)//power) for j,v in coeff.items()),Q())
    wt=sum((v*((N//power)//j) for j,v in coeff.items()),Q())
    assert wt>=1;rhs+=wt;power*=p
   assert lhs==rhs;exponents+=1
 # Elementary all-N envelope certificate.
 da=Q(22097,108);dt=Q(13165,36)
 assert Anew-Aold==da and H*As==dt
 assert mp.iv.log(10).a>2 and mp.iv.log(10).b<interval(Q(7,3)).a and mp.iv.log(15).a>2
 Qupper=da*15+dt*Q(65,9)
 assert Qupper==Q(925045,162)<Q(10**6,90)
 for n,item in rec['early_weights'].items():
  n=int(n);assert Q(w[n],S)==Q(item['old']) and Q(rebuilt[n],S)==Q(item['new'])
 receipt={'status':'PASS: separate-code self-check, not an independent-agent or human review','input_sha256':hashlib.sha256((ROOT/'inputs/repair_cost_rule.zip').read_bytes()).hexdigest(),
 'actions':len(rec['actions']),'prefix_cells':R-1,'universal_wheel_cases':wheel_cases,'selected_full_period_cells':period_cases,
 'patches':len(patches),'raw_deficit_cells':len(ds),'factorial_prime_exponent_identities':exponents,
 'old_C':fmt(cprev),'new_C':fmt(cnew),'guaranteed_saving':fmt(guarantee),'actual_saving':fmt(actual),
 'new_first_mass':str(Anew),'new_extra_single_tail':str(Tnew),'unchanged_double_tail':str(H0),
 'envelope_threshold':10**6,'exact_Q_upper':str(Qupper),'comparisons':comparisons,'seconds':time.monotonic()-t0}
 out.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--results',type=Path,default=ROOT/'results.json');ap.add_argument('--output',type=Path,default=ROOT/'rerun_checks.json');args=ap.parse_args();main(args.results,args.output)
