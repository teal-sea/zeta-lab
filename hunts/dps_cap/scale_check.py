"""An order-of-magnitude check that does not go through the Mellin split.

``epstein_completed`` builds Lambda_Q(s) from two incomplete-gamma lattice sums.
This checks the size of the answer a different way, using only the definition
the docstring states,

    Lambda_Q(s) = (sqrt(d)/pi)^s Gamma(s) zeta_Q(s),   d = |D|/4,

and mpmath's own ``gamma``.  Dividing the measured Lambda by the two factors
that are not in question leaves the implied |zeta_Q(s)|.  Epstein zeta at
Re(s) = 0.8 and this height should be O(1) up to a small power of t, so an
implied value of that size corroborates the magnitude and an implied value
many orders from it would refute it.  This bounds the exponent; it does not
check a single digit.
"""

from mpmath import mp, mpc

from zeta.epstein import epstein_completed

FORM = (2, 1, 3)

with mp.workdps(70):
    s = mpc("0.8", "85.7")
    a, b, c = FORM
    d = mp.mpf(a) * c - mp.mpf(b) ** 2 / 4          # 5.75 = |D|/4 for D = -23
    lam = epstein_completed(s, FORM, dps=60)

    gamma_factor = mp.gamma(s)                       # mpmath's own Gamma
    prefactor = (mp.sqrt(d) / mp.pi) ** s
    implied_zeta_q = lam / (gamma_factor * prefactor)

    scale = abs(gamma_factor) * abs(prefactor)       # Lambda's size if |zeta_Q| = 1
    capped = mp.mpf("3.3924673495700062842e-34")      # the dps=20 reading

    print("d                    =", mp.nstr(d, 6))
    print("|Lambda_Q(s)|        =", mp.nstr(abs(lam), 12))
    print("|Gamma(s)|           =", mp.nstr(abs(gamma_factor), 12))
    print("|(sqrt(d)/pi)^s|     =", mp.nstr(abs(prefactor), 12))
    print("prefactor scale      =", mp.nstr(scale, 12), " (= |Lambda| if |zeta_Q| = 1)")
    print("implied |zeta_Q(s)|  =", mp.nstr(abs(implied_zeta_q), 12))
    print()
    print("Gamma decay alone accounts for 10^"
          + mp.nstr(mp.log10(abs(gamma_factor)), 6))
    print()
    print("Same test applied to the capped reading 3.392e-34:")
    print("  implied |zeta_Q(s)| =", mp.nstr(capped / scale, 12))
    print("  An Epstein zeta of that size at Re(s)=0.8 is not a possible value,")
    print("  so the capped reading is refuted by a route that never touches the")
    print("  Mellin split it came from.")
