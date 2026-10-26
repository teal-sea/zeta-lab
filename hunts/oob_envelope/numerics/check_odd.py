"""Tiny formula checks only. No matrix assembly or heavy local numerics."""
import json
import sys
from fractions import Fraction
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import mpmath as mp
from flint import arb, ctx
from stage_b_odd_modal import CFGS, common, unit_ranges
from harden import dfact_log


def check():
    old = ctx.prec
    try:
        cfg = dict(CFGS["val"], N=3)
        _, _, beta, nus, pole, La, _ = common(cfg)
        assert bool(beta > 0)
        defects = []
        with mp.workdps(55):
            L = mp.mpf(4)/5
            for i in range(3):
                n = 2*i+1
                nu = mp.mpf(n)+mp.mpf(1)/2
                T = lambda x: mp.sqrt(nu/L)*mp.legendre(n, x/L)
                s = mp.quad(lambda x: T(x)*mp.sinh(x/2), [-L, 0, L])
                pp = mp.mpf(pole[i].mid().str(65, radius=False))
                defects.append(abs(s-pp))
                for t in (mp.mpf(0), mp.mpf(1)/7, mp.mpf(3)):
                    f = mp.quad(lambda x: T(x)*mp.exp(1j*t*x), [-L, 0, L])
                    z = t*L
                    jn = mp.sqrt(mp.pi/(2*z))*mp.besselj(nu,z) if z else 0
                    predicted = 1j*(-1)**i*2*mp.sqrt(L*nu)*jn
                    defects.append(abs(f-predicted))
                # Norm and mutual orthogonality on the first three odd modes.
                for j in range(3):
                    m = 2*j+1
                    g = mp.quad(lambda x: T(x)*mp.sqrt((mp.mpf(m)+mp.mpf(1)/2)/L)*mp.legendre(m,x/L), [-L,0,L])
                    defects.append(abs(g-(i==j)))
                df = 1
                for k in range(1,2*n+2,2):
                    df *= k
                assert dfact_log(n).exp().contains(arb(df))
            assert max(defects) < mp.mpf("1e-48")
            formula_defect = str(max(defects))
        # At each actual cut, ratios agree with direct step-two coefficients.
        ratios = {}
        for name,c in CFGS.items():
            _,_,_,_,_,l,t = common(c)
            n = 2*c["N"]+1
            rs=[]
            for x in (l*t,l/2):
                a = lambda k: 2*(l*(k+arb(1)/2)).sqrt()*(k*x.log()-dfact_log(k)).exp()
                r = x*x/((2*n+3)*(2*n+5))*((n+arb(5)/2)/(n+arb(1)/2)).sqrt()
                assert r.overlaps(a(n+2)/a(n)) and bool(r<1)
                assert bool(a(n+2)<a(n))
                rs.append(r.str(12))
            ratios[name] = rs
            assert sum(b-a for a,b in unit_ranges(c))*Fraction(c["h"]) == Fraction(c["T"])
        print(json.dumps({"ok":True,"max_direct_integral_defect":formula_defect,"tail_ratios":ratios},indent=1))
    finally:
        ctx.prec=old


if __name__ == "__main__":
    check()
