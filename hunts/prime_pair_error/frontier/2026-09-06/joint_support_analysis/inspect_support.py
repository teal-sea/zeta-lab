from pathlib import Path
from fractions import Fraction as F
from collections import defaultdict
import json
ROOT=Path(__file__).parent/'inputs'
base=json.loads((ROOT/'certificate_route_test/inputs.json').read_text())
agg=json.loads((ROOT/'certificate_route_test/aggregate_results.json').read_text())
cand=json.loads((ROOT/'joint_correction_candidate/joint_results.json').read_text())
a0={int(k):F(v) for k,v in base['starting_coefficients'].items()}
cnew={int(k):F(v) for k,v in cand['new_coefficients'].items()}
rep=sorted({int(n) for s in agg['stages'] for n,v in s['repairs']})
mask={1:1}
for p in (2,3,5,7):mask.update({d*p:-s for d,s in list(mask.items())})
def g(a,t):return sum((v*(t//j) for j,v in a.items()),F())
def w(a,t):
    v=F()
    while t:
        v+=g(a,t);t//=15
    return v

def b(n,t):return t//n-t//(n+1)-t//(n*(n+1))
def h(q,t):return sum(s*b(q,t//d) for d,s in mask.items())
def lift(f,n,t):
    s=0
    while t:s+=f(n,t);t//=15
    return s
print('repair count and early repair cells',len(rep),rep[:20])
for t in [13,14,15,16,20,21,220,231,240,252,260,273]:
    print(t,'W0=',w(a0,t),'Wnew=',w(cnew,t),'h_cols=',[(q,lift(h,q,t)) for q in range(13,37) if lift(h,q,t)],'b_cols=',[(n,lift(b,n,t)) for n in rep if lift(b,n,t)])
