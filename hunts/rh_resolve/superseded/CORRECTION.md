# CORRECTION: midpoint remainder understated (2026-10-03)

What was wrong: enclose_li_mid.py bounded the midpoint-rule remainder
with M2c = 2M/(rho-R)^2, the Cauchy bound for f'' where
f(z) = log xi(1/(1-z)). But the quadrature integrates
g(t) = f(R e^{it}) e^{-int}, whose second derivative has two more
pieces: the contour chain rule (d/dt = iR e^{it} d/dz) and the
oscillation factor (-in twice). The correct bound is
|g''| <= F2 + 2n F1 + n^2 M with F1 = R M1, F2 = R M1 + R^2 M2c,
M1 = M/(rho-R). The n^2 M term dominates for n >= 5.

Scope of invalidation, precisely: the old bound M2c was valid only
where the true G2 = F2 + 2n F1 + n^2 M did not exceed it. R = 0.7
runs (M2c = 106.38): rows n >= 4 invalid. R = 0.8 runs
(M2c = 303.59): rows n >= 5 invalid. (Panel-covering
enclose_li.py rows are unaffected: pure inclusion, no derivative
bound.) Six JSON files moved to superseded/ in this directory,
unmodified, so the error is preserved and checkable, not silently
rewritten. Corrected re-runs certify n = 1..58 with n = 59 mapped
as the boundary at K = 65536.

Fix: G2 implemented in enclose_li_mid.py; THEOREM.md and RESULTS.md
updated to the re-run boundary. Found by re-deriving the remainder
before writing the final record, not by any test turning red.
