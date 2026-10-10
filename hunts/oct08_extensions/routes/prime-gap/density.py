"""Bounded Arb experiment using the pinned PR276 weight and KLN density."""
import json
from math import isqrt
from fractions import Fraction as F
from flint import arb
import base_bound as b

b.set_precision(256)
S = F(17,20)

def moment(a, B, v):
    """Integral from B>=4.5a of (t/B)^v (-G'(t)) dt."""
    t2=b.U2()*a
    assert v<3
    if B>=t2:
        return 648*a**3/B**3/(3-v)
    assert v<1
    mid=arb('4.5')*a/B*(1-(t2/B)**(v-1))/(1-v)
    tail=648*a**3/B**v*t2**(v-3)/(3-v)
    return mid+tail

def rare(a):
    # Keep the endpoint enclosure: rounding B upward would omit a positive sliver.
    B=max(arb(b.H0),arb('4.5')*a)
    l=B.log()
    # log t <= log B * (t/B)^(1/log B), for t>=B.
    return (9*B**arb('0.4')*l**arb('3.3')*moment(a,B,arb('0.4')+arb('3.3')/l)
            +4*l**2*moment(a,B,2/l))

def bound(La,Lb,k=8):
    old=b.interval_bound(b.KthPowers(k),F(7,8),La,Lb)
    a=old['a_star']; lx=k*La
    high=2*(-arb('0.15')*lx).exp()*b.S_high(a)+2*(-lx/8).exp()*rare(a)
    margin=1-old['low']-high-old['triv']-old['prime_power_share']
    return margin

def main():
    worst=(1,None)
    # 10 <= n <= e^40, overlapping initial endpoint below log10.
    assert arb(9).log()<arb(36)/16<arb(10).log()
    for i in range(604):
        L=arb(36+i)/16
        m=bound(L,L+arb(1)/16)
        assert m>0, (str(L),str(m))
        assert m>arb('.95468')
        if float(m)<worst[0]: worst=(float(m),str(L))
    tail0=b.kth_power_tail(8,F(17,20),F(40))
    assert tail0['closed'] and tail0['decreasing']
    assert moment(arb(1),arb('4.5'),arb('.5'))<2
    assert arb('4.5')**arb('.4')<2
    tail=tail0['sup_bound']+72*(-arb(40)*arb('.6')).exp()*42**4+16*(-arb(40)).exp()*42**2
    assert tail<1
    assert tail<arb('.045583')
    assert arb(4)/42<arb('.6') and arb(2)/42<1
    def prime(p):
        return p>=2 and all(p%d for d in range(2,isqrt(p)+1))
    witnesses=[]
    for n in range(1,10):
        p=n**8+1
        while not prime(p):p+=1
        assert n**8<p<(n+1)**8
        witnesses.append([n,p])
    assert not prime(341) and not prime(561)
    print(json.dumps({'cover_intervals':604,'L_start':'36/16','L_end':'40', 'worst_margin':worst,
                      'tail_error_upper':str(tail),'witnesses':witnesses},indent=2))
    for L in [25,28,30,32,40,50,100]:
        print(L,str(bound(arb(L),arb(L))))

if __name__=='__main__': main()
