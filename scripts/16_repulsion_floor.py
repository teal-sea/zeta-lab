"""Level repulsion in the zeta zeros: the small-gap tail, against two models.

"The zeros repel" is not the statement that no gap is ever tiny -- with 138,000
spacings some of them are bound to be small.  It is a statement about the *rate*
at which the density of spacings vanishes at zero.  For a Poisson process the
spacing density is e^{-s}, which is nonzero at s = 0; for GUE it vanishes like
s^2, so the CDF vanishes like s^3.  Those are different by orders of magnitude
in the region that matters, and the difference is measurable.

So this script does not ask "is the minimum gap positive" (it is, trivially, and
a positive minimum is consistent with Poisson too).  It measures the small-s
tail of the empirical spacing CDF and compares it against both models, and it
checks the observed minimum gap against the value GUE predicts for a sample this
size.

Nothing here is evidence for RH (docs/08); GUE agreement is a statement about
the *distribution* of zeros already known to be on the line in this range.
"""

import time

import numpy as np

import zeta.statistics as zs

T_MAX = 100000.0

print("=" * 78)
print("LEVEL REPULSION IN THE ZETA ZEROS: THE SMALL-GAP TAIL")
print("=" * 78)

print("\n1) LOADING ZEROS")
t0 = time.time()
gammas = zs.zero_ordinates(t_max=T_MAX)
n_zeros = len(gammas)
print(f"   {n_zeros} zeros with 0 < gamma < {T_MAX:g}  ({time.time() - t0:.2f}s)")

print("\n2) UNFOLDING")
spacings = zs.nearest_neighbour_spacings(gammas)
n_gaps = len(spacings)
print(f"   {n_gaps} nearest-neighbour spacings")
print(f"   mean     = {spacings.mean():.6f}   (1 by construction)")
print(f"   variance = {spacings.var():.6f}   (GUE bulk ~0.178; the approach is")
print("                             slow in T -- see the CUE-control measurement)")
print(f"   min      = {spacings.min():.6f}")
print(f"   max      = {spacings.max():.6f}")

print("\n3) THE SMALL-GAP TAIL — WHERE REPULSION ACTUALLY SHOWS UP")
print("   Fraction of spacings below s, against both models:\n")
print(f"   {'s':>6}  {'observed':>12}  {'GUE':>12}  {'Poisson':>12}  {'Poisson/obs':>12}")
thresholds = [0.02, 0.05, 0.1, 0.2, 0.3, 0.5]
rows = []
for s in thresholds:
    obs = float(np.mean(spacings < s))
    gue = float(zs.gue_spacing_exact_cdf(s))
    poi = float(zs.poisson_spacing_cdf(s))
    rows.append((s, obs, gue, poi))
    # obs can be exactly 0 in the deepest bin -- that is itself the finding,
    # so report the bound rather than dividing by zero.
    ratio = f"{poi / obs:>11.1f}x" if obs > 0 else f"> {poi * n_gaps:>9.0f}x"
    print(f"   {s:>6.2f}  {obs:>12.3e}  {gue:>12.3e}  {poi:>12.3e}  {ratio:>12}")

print("\n   At s = 0.05 the Poisson model predicts a small-gap rate two to three")
print("   orders of magnitude above what is observed; GUE tracks it.  That gap")
print("   between the models is the repulsion.")

print("\n4) THE MINIMUM GAP, AGAINST WHAT GUE PREDICTS FOR THIS SAMPLE SIZE")
# Near s = 0 the GUE spacing CDF behaves like c*s^3.  Fit c at a small s where
# the cubic regime holds, then the expected smallest of n_gaps draws solves
# c*s^3 ~ 1/n_gaps.
s_fit = 0.01
c = float(zs.gue_spacing_exact_cdf(s_fit)) / s_fit**3
s_expected = (1.0 / (c * n_gaps)) ** (1.0 / 3.0)
i_min = int(np.argmin(spacings))
print(f"   cubic coefficient of the GUE CDF near 0 : c = {c:.5f}   (F ~ c s^3)")
print(f"   predicted smallest of {n_gaps} draws      : s ~ {s_expected:.5f}")
print(f"   observed smallest normalised spacing      : s = {spacings.min():.5f}")
print(f"   ratio observed/predicted                  : {spacings.min() / s_expected:.3f}")
print(f"   it occurs between zeros {i_min + 1} and {i_min + 2}:")
print(f"     gamma_{i_min + 1} = {gammas[i_min]:.6f}")
print(f"     gamma_{i_min + 2} = {gammas[i_min + 1]:.6f}")
print(f"     raw (unnormalised) gap = {gammas[i_min + 1] - gammas[i_min]:.6f}")

print("\n5) VERDICT")
obs_005 = float(np.mean(spacings < 0.05))
poi_005 = float(zs.poisson_spacing_cdf(0.05))
gue_005 = float(zs.gue_spacing_exact_cdf(0.05))
print(f"   Poisson is off by a factor of {poi_005 / obs_005:.0f} at s = 0.05;")
print(f"   GUE is off by a factor of {max(gue_005, obs_005) / min(gue_005, obs_005):.2f}.")
print("   The small-gap tail is cubic, not linear: the zeros repel in the sense")
print("   that matters, and the effect is a property of the distribution, not")
print("   of the single closest pair.  Note that a positive minimum gap on its")
print("   own would prove nothing -- a Poisson sample of this size also has one.")
print("   This says nothing about RH; it describes zeros already known to be on")
print("   the line for this range (docs/08).")
