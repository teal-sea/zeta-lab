"""Layer-cake upper bounds; external KLN Table1 constants rounded up."""
import sys
import json
from math import isqrt
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'prime-gap'))
from density import arb,b,F,moment

# sigma, upper rounded A,B from KLN Table1, arxiv2101.12263v1.
ROWS=[('0.75','5.28','4.41'),('0.8','6.92','4'),('0.85','8.98','3.59'),
      ('0.86','9.45','3.52'),('0.87','9.93','3.44')]

def rare(a,row):
    sigma,A,C=map(arb,row); r=arb(8)/3*(1-sigma);q=5-2*sigma
    B=max(arb(b.H0),arb('4.5')*a);l=B.log()
    return A*B**r*l**q*moment(a,B,r+q/l)+C*l**2*moment(a,B,2/l)

def bound(La,Lb,k=7):
    assert k*La>=8 # Each positive layer coefficient decreases in x.
    old=b.interval_bound(b.KthPowers(k),F(7,8),La,Lb)
    a=old['a_star'];lx=k*La
    high=2*(-lx/4).exp()*b.S_high(a)
    for i,row in enumerate(ROWS):
        s=arb(row[0]);t=arb(ROWS[i+1][0]) if i+1<len(ROWS) else arb(7)/8
        coefficient=((t-1)*lx).exp()-((s-1)*lx).exp()
        assert coefficient>0
        high+=2*coefficient*rare(a,row)
    return 1-old['low']-high-old['triv']-old['prime_power_share']

def tail(k=7,L=50):
    baseline=b.kth_power_tail(k,F(3,4),F(L))
    assert baseline['decreasing'] and baseline['prereq']
    total=baseline['sup_bound']
    assert moment(arb(1),arb('4.5'),arb('.8'))<3
    assert arb('4.5')**(arb(2)/3)<3
    for i,row in enumerate(ROWS):
        s,A,C=map(arb,row);r=arb(8)/3*(1-s);q=5-2*s
        t=arb(ROWS[i+1][0]) if i+1<len(ROWS) else arb(7)/8
        d=k*(1-t)-r
        assert r+q/L<arb('.8')
        assert q<4
        assert d>arb(4)/(L+2)
        assert k*(1-t)>arb(2)/(L+2)
        total+=18*A*(-d*L).exp()*(L+2)**4+6*C*(-k*(1-t)*L).exp()*(L+2)**2
    return total

if __name__=='__main__':
    worst=(1,None)
    for i in range(764):
        L=arb(36+i)/16
        m=bound(L,L+arb(1)/16)
        assert m>arb('.13045')
        if float(m)<worst[0]:worst=(float(m),str(L))
    t=tail()
    assert t<1
    assert t<arb('.012961')
    def prime(p):return p>=2 and all(p%d for d in range(2,isqrt(p)+1))
    witnesses=[]
    for n in range(1,10):
        p=n**7+1
        while not prime(p):p+=1
        assert n**7<p<(n+1)**7
        witnesses.append([n,p])
    print(json.dumps({'intervals':764,'logn_start':'2.25','logn_end':'50','worst_margin':worst,
                     'tail_error':str(t),'witnesses':witnesses},indent=2))
    for k in [6,7]:
        for L in [25,28,29,30,32,40,50,100]:print(k,L,bound(arb(L),arb(L),k))
