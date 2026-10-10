# CORRECTION: midpoint remainder understated (2026-10-03)

What was wrong: enclose_li_mid.py bounded the midpoint-rule remainder
with M2c = 2M/(rho-R)^2, the Cauchy bound for f'' where
f(z) = log xi(1/(1-z)). But the quadrature integrates
g(t) = f(R e^{it}) e^{-int}, whose second derivative has two more
pieces: the contour chain rule (d/dt = iR e^{it} d/dz) and the
oscillation factor (-in twice). The correct bound is
|g''| <= F2 + 2n F1 + n^2 M with F1 = R M1, F2 = R M1 + R^2 M2c,
M1 = M/(rho-R). The n^2 M term grows fastest; the added terms first
push G2 above M2c at the rows named below. (Until 2026-10-10 this
sentence said the n^2 M term dominates for n >= 5; the saved M2 values
show n >= 5 is where G2 first exceeds M2c at R = 0.8, not where n^2 M
dominates.)

Scope of invalidation, precisely: the old bound M2c was valid only
where the true G2 = F2 + 2n F1 + n^2 M did not exceed it. R = 0.7
runs (M2c = 106.38): rows n >= 4 invalid. R = 0.8 runs
(M2c = 303.59): rows n >= 5 invalid. (Panel-covering
enclose_li.py rows do not use a derivative bound, so this correction
does not touch them.) Six JSON files moved to superseded/ in this
directory, unmodified, so the error is preserved and checkable, not
silently rewritten. Corrected re-runs reported positive lower endpoints
for n = 1..58, with n = 59 mapped as the boundary at K = 65536. Those
corrected rows do not stand as enclosures either: the audit of
2026-10-04 (`../AUDIT.md`) withdrew their enclosure grade, and every Li
row in this hunt, panel-covering rows included, is now graded measured.

Fix: G2 implemented in enclose_li_mid.py; the claim file (then
THEOREM.md, now AUDIT.md) and RESULTS.md updated to the re-run boundary.
Found by re-deriving the remainder before writing the final record, not
by any test turning red.
