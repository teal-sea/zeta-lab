"""Independent exact check of inherited-support obstruction and one q=20 direction.

Does not import the candidate, refine.py, or the direction generator.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import defaultdict
import json, math, hashlib
from mpmath import mp, iv
ROOT=Path(__file__).resolve().parent
IP=ROOT/'inputs'
source=json.loads((IP/'joint_correction_candidate/joint_results.json').read_text())
base=json.loads((IP/'certificate_route_test/inputs.json').read_text())
agg=json.loads((IP/'certificate_route_test/aggregate_results.json').read_text())
trials=json.loads((ROOT/'q20_direction_results.json').read_text())
M,R,den=15,100000,108
original={int(j):F(a) for j,a in source['new_coefficients'].items()}
g0={int(j):F(a) for j,a in base['starting_coefficients'].items()}
star={int(j):F(a) for j,a in base['repair_coefficients'].items()}
H0=F(source['new_tail_H'])
allowed=sorted({int(n) for s in agg['stages'] for n,a in s['repairs']})
mu={1:1}
for p in (2,3,5,7): mu.update({p*d:-v for d,v in list(mu.items())})
def balance(c): return sum((a/F(j) for j,a in c.items()),F())
def floorv(c,t): return sum((a*(t//j) for j,a in c.items()),F())
def bump(n,t): return t//n-t//(n+1)-t//(n*(n+1))
def masked(q,t): return sum(a*bump(q,t//d) for d,a in mu.items())
def lift_fun(f,t):
    result=F()
    while t:
        result+=f(t);t//=M
    return result

def table(c,limit,den=108):
    increments=[0]*limit
    for j,a in c.items():
        scaled=a*den; assert scaled.denominator==1
        for n in range(j,limit,j):increments[n]+=scaled.numerator
    total=0
    for n in range(limit):total+=increments[n];increments[n]=total
    return increments

def lifted_table(seed):
    out=seed[:]
    for n in range(1,len(seed)):out[n]+=out[n//M]
    return out

# Entire old menu, not only nine chosen variables, at the obstruction rows.
obstruction_rows=[]
for t in (13,16,20,220):
    hs={q:int(lift_fun(lambda z:masked(q,z),t)) for q in range(13,37)}
    bs={n:int(lift_fun(lambda z:bump(n,z),t)) for n in allowed}
    row={'t':t,'W0':str(lift_fun(lambda z:floorv(g0,z),t)),
         'masked_nonzero':{str(q):v for q,v in hs.items() if v},
         'repairs_nonzero':{str(n):v for n,v in bs.items() if v}}
    obstruction_rows.append(row)
assert obstruction_rows==[
 {'t':13,'W0':'1','masked_nonzero':{'13':1},'repairs_nonzero':{}},
 {'t':16,'W0':'1','masked_nonzero':{'16':1},'repairs_nonzero':{}},
 {'t':20,'W0':'3','masked_nonzero':{'20':1},'repairs_nonzero':{}},
 {'t':220,'W0':'1','masked_nonzero':{'13':-1,'16':1,'20':1},'repairs_nonzero':{}}]
assert len(allowed)==411 and min(allowed)==189 and 220 not in allowed
for c,L in [(g0,30030),(star,2310)]:
    assert balance(c)==0
    v=table(c,L); assert min(v)>=0 and min(v[1:15])>=den
hvals=[masked(20,t) for t in range(210*20*21)]
assert max(hvals)==3 and min(hvals)==-3
oldseed=table(original,R);oldlift=lifted_table(oldseed)
assert min(oldlift[1:])==108
trial=next(x for x in trials if x['amount']=='1')
cc=defaultdict(F,original)
for d,s in mu.items():
    cc[20*d]-=s;cc[21*d]+=s;cc[420*d]+=s
for n,aa in trial['all_repairs']:
    a=F(aa);assert a>0
    cc[n]+=a;cc[n+1]-=a;cc[n*(n+1)]-=a
cc={j:a for j,a in cc.items() if a}
assert balance(cc)==0
assert sum(map(abs,cc.values()),F())==F(1405,2)
newH=H0+3;assert newH==F(809,36)
seed=table(cc,R);lift=lifted_table(seed)
assert min(lift[1:])==108 and lift[20]==216 and lift[220]==108
assert len(cc)==834 and len(trial['all_repairs'])==145
assert sum(n not in allowed for n,a in trial['all_repairs'])==100
iv.dps=65

def ivq(q): return iv.mpf(q.numerator)/q.denominator

def kappai(c):
    s=iv.mpf(0)
    for j,a in c.items():s-=ivq(a)*iv.log(j)/j
    return s

with mp.workdps(80):
    kstar=kappai(star);kold=kappai(original);knew=kappai(cc)
    assert knew.a>0 and kstar.a>0
    one=ivq(F(14,15)); Cs=kstar/one
    Cold=(kold+ivq(H0/R)*Cs)/one
    Cnew=(knew+ivq(newH/R)*Cs)/one
    assert Cnew.b<Cold.a
    interval_gain=Cold-Cnew
    def endpoints(v):return [mp.nstr(mp.make_mpf(v._mpi_[i]),72) for i in (0,1)]
    def mpq(q):return mp.mpf(q.numerator)/q.denominator
    def kval(c):return -mp.fsum(mpq(a)*mp.log(j)/j for j,a in c.items())
    cs=kval(star)/mpq(F(14,15))
    cold=(kval(original)+mpq(H0)*cs/R)/mpq(F(14,15))
    cnew=(kval(cc)+mpq(newH)*cs/R)/mpq(F(14,15))
    def levels(N):
        out=[];s=1
        while s<=N:out.append(s);s*=M
        return out
    def factorial_expression(c,H,N):
        vals=[]
        for scale in levels(N):
            vals.extend(mpq(a)*mp.loggamma(N//(scale*j)+1) for j,a in c.items() if scale*j<=N)
        for k,scale in enumerate(levels(N//R)):
            vals.extend(mpq(H*a)*(k+1)*mp.loggamma(N//(R*scale*j)+1) for j,a in star.items() if R*scale*j<=N)
        return mp.fsum(vals)
    def env(c,H,C,N):
        A=sum(map(abs,c.values()),F())
        s1=mp.fsum(1+mp.log(mp.mpf(N)/s) for s in levels(N))
        s2=mp.fsum((k+1)*(1+mp.log(mp.mpf(N)/(R*s))) for k,s in enumerate(levels(N//R)))
        return C*N+mpq(A)*s1+mpq(15*H)*s2
    comparisons=[]
    for N in (10**4,10**6,10**8,10**12):
        ob=factorial_expression(original,H0,N);nb=factorial_expression(cc,newH,N)
        ou=env(original,H0,cold,N);nu=env(cc,newH,cnew,N)
        assert ob<=ou and nb<=nu
        comparisons.append({'N':N,'B_saving':mp.nstr(ob-nb,40),'U_saving':mp.nstr(ou-nu,40)})
    record={'scope':'Own new direction calculation, not included in review PR 200. Checks elementary inputs and finite feasibility; not an asymptotic rate, novelty or independent-agent review.',
        'source_archive_sha256':hashlib.sha256((ROOT/'original_archives/joint_correction_candidate.zip').read_bytes()).hexdigest(),
        'obstruction_rows':obstruction_rows,'old_repair_cells':411,
        'q20_period_cells':len(hvals),'prefix_cells':R-1,
        'new_C_interval':endpoints(Cnew),'C_decrease_interval':endpoints(interval_gain),
        'finite_mass':str(F(1405,2)),'tail_H':str(newH),'tail_budget_coefficient':str(15*newH),
        'repairs':145,'repair_sites_not_in_old_dictionary':100,
        'weight20':str(F(lift[20],108)),'weight220':str(F(lift[220],108)),
        'kappa_D_lower':endpoints(knew)[0],
        'comparisons_high_precision_not_intervals':comparisons,
        'new_coefficients':{str(j):str(a) for j,a in sorted(cc.items())}}
(ROOT/'INDEPENDENT_CHECK.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k!='new_coefficients'},indent=2))
