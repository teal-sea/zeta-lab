"""Independent numerical quadrature and adversarial controls, not proof."""
import mpmath as m
from density import arb, b, rare, bound

with m.workdps(40):
    for L in [20,28,30,40]:
        a=1+1/m.expm1(8*m.log1p(m.exp(-L)))
        H=m.mpf(b.H0); t1=m.mpf('4.5')*a; t2=m.sqrt(48)*a
        def D(t):return 9*t**m.mpf('.4')*m.log(t)**m.mpf('3.3')+4*m.log(t)**2
        def f(y):
            t=m.exp(y)
            return D(t)*(m.mpf('4.5')*a/t if t<t2 else 648*(a/t)**3)
        lo=max(H,t1)
        cuts=[m.log(lo)]
        if t2>lo:cuts.append(m.log(t2))
        cuts.append(m.inf)
        q=m.quad(f,cuts)
        r=rare(arb(str(a)))
        assert m.mpf(str(float(r)))>q
        print('L',L,'quadrature',m.nstr(q,14),'majorant ratio',float(r)/float(q))
    # Destructive control: removing density information reopens the k8 wall.
    old=b.interval_bound(b.KthPowers(8),b.Fraction(7,8),arb(30),arb(30))
    assert old['margin']<0
    assert bound(arb(30),arb(30))>0
    assert bound(arb(30),arb(30),7)<0
    print('controls: full N(T) k8 rejected; density k8 passes; single-split k7 rejected')
