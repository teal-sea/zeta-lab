"""Independent Acb enclosure of the low-height input to KLN Lemma 3.2."""
from flint import arb, acb, ctx
ctx.prec = 192
count = 3*65536
bound = arb(14604)/10000
maximum = arb(0)
for j in range(count):
    t = arb(arb(2*j+1)/131072, arb(1)/131072)
    value = abs(acb(arb(1)/2, t).zeta())
    assert value < bound, (j, value)
    maximum = maximum.max(value.upper())
print('precision_bits',ctx.prec,'cells',count,'range',[0,3])
print('all cell enclosures < 1.4604; upper bound',maximum)
slack = arb(2851)/1000-arb(63)/100*6/arb(1).exp()-bound
assert slack > 0
print('a2 - 6*a1/e - 1.4604',slack)
