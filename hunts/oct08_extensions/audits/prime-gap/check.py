"""Independent bounded audit checks; quadrature is corroboration, not proof."""
import sys
from pathlib import Path
from math import isqrt
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'routes'/'prime-gap'))
import density as d
import mpmath as m
from flint import arb

# Numerical reconstruction from the derivative of the defining g, not moment().
with m.workdps(60):
    for aa,BB,vv in [(1,4.5,.5),(1,7,.5),(10,45,.4),(10,80,.9)]:
        a,B,v=map(lambda x:m.mpf(str(x)),(aa,BB,vv))
        t2=m.sqrt(48)*a
        if B<t2:
            val=m.quad(lambda t:(t/B)**v*m.mpf('4.5')*a/t**2,[B,t2])
            val+=m.quad(lambda t:(t/B)**v*648*a**3/t**4,[t2,m.inf])
        else:val=m.quad(lambda t:(t/B)**v*648*a**3/t**4,[B,m.inf])
        got=d.moment(arb(str(a)),arb(str(B)),arb(str(v)))
        assert abs(float(got)-float(val))<1e-14
print('4 independently reconstructed moment integrals agree (nonrigorous check)')

# Author's floating worst-margin summary is not trusted: assert the claimed
# decimal directly for every closed interval using certain comparisons.
d.b.set_precision(384)
for i in range(604):
    A=arb(36+i)/16
    assert d.bound(A,A+arb(1)/16)>arb('.95468')
print('604 interval margins each > .95468 at 384 bits')
assert arb(36)/16<arb(10).log()
assert arb(36+604)/16==40

# Independent fixed witnesses, with direct exhaustive trial division.
ws=[2,257,6563,65537,390647,1679627,5764817,16777259,43046747]
for n,p in enumerate(ws,1):
    assert n**8<p<(n+1)**8
    assert all(p%j for j in range(2,isqrt(p)+1))
print('9 fixed prime witnesses and strict interval endpoints pass')

# Tail inequalities that underlie uniformity, rather than pointwise samples.
L=arb(40)
assert arb('4.5')*L.exp()>d.b.H0
assert arb('.4')+arb('3.3')/(L+arb('4.5').log())<arb('.5')
assert 2/(L+arb('4.5').log())<arb('.5')
assert d.moment(arb(1),arb('4.5'),arb('.5'))<2
assert arb('4.5')**arb('.4')<2
assert 4/(L+2)<arb('.6') and 2/(L+2)<1
T=d.b.kth_power_tail(8,d.F(17,20),d.F(40))
assert T['closed'] and T['decreasing'] and T['sup_bound']<arb('.037126')
tail=T['sup_bound']+72*(-arb('.6')*L).exp()*(L+2)**4+16*(-L).exp()*(L+2)**2
assert tail<arb('.045583')
print('uniform tail prerequisites and upper error < .045583 pass')
