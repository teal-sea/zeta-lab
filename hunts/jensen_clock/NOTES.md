# Spine candidates and loose ends — jensen_clock

Things that belong to other parts of the tree, recorded here rather than
done, because this hunt may not touch `zeta/`.

1. **Docstring line for `zeta/li.py`'s hyperbolicity scanners.** The measured
   fact: hyperbolicity of J^{d,0} at degree d inspects the function at
   effective de Bruijn–Newman time |x|/(8d) at image position x, so a scan at
   degree d is blind to any off-line pair whose flow landing time is below
   |x₀|/(8d). For the Davenport–Heilbronn height-85.7 pair that threshold is
   d ≈ 2.08·10⁴; every textbook-scale scan (d ≤ 32 here and in
   `hyperbolicity_scan`'s pinned ranges) sits five hundred times short of it.
   A sentence in the docstring would stop a future hunt from reading a green
   low-degree scan as evidence of anything about off-line zeros. (`zeta/`
   change — needs its own tests, not this hunt's.)

2. **Shift-direction dictionary.** This hunt fixed the shift n = 0 and varied
   the degree. The GORZ shift n → ∞ limit is also a heat limit; a matching
   dictionary t_eff(n, d) for the shifted family J^{d,n} would say which
   (d, n) cells of a full scan grid can see a given pair at all — turning the
   blindness corollary from one axis into the whole table. Same instrument
   would work (the shifted γ-table is a suffix of the same moment table).

3. **The additive identity as a funnel candidate.** t_land(d) + |x₀|/(8d) =
   t\* held at 0.03–0.06% at two degrees. If someone wants a candidate for
   the discovery funnel, the sharp form (does the defect vanish as d → ∞,
   with the d⁻¹-correction coefficient computable from the saddle?) is
   well-posed and cheap to test further. Not entered here: the N-body null
   already explains the quantity as configuration geometry, so under this
   repo's rules it is a closure, not a lead.
