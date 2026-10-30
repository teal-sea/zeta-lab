# 47. The Davenport-Heilbronn zero, kernel-checked

Riemann's zeta function satisfies a functional equation, `xi(s) = xi(1 - s)`, and all of
its zeros that anyone has computed lie on the line Re s = 1/2. A natural question is
whether the functional equation is what forces them there. In 1936 Davenport and
Heilbronn answered no. They built a function with zeta's kind of Dirichlet series and an
equally clean functional equation, which nonetheless has zeros off the line. Spira (1994)
computed the lowest of them, near 0.808517 + 85.699348 i.

This laboratory now has that fact as a theorem checked by Lean's kernel. This page says
what was proved, how, and what it does and does not mean. The full record is hunt #145,
`hunts/rung3_ball_production/` (`RESULTS.md` first).

## 1. What is proved

In Lean 4 (`v4.35.0-rc2`, Mathlib `065356127b1d`), with zero `sorry` and only the three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`), one theorem states the
result:

```lean
theorem davenport_heilbronn_strip :
    ∃ (f : ℂ → ℂ) (s : ℂ), Differentiable ℂ f ∧ dh_series_rep f ∧ dh_functional_eq f ∧
      f s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ s.re ≠ 1/2
```

Some entire function, given by the Davenport-Heilbronn Dirichlet series for Re s > 1 and
satisfying its functional equation, has a zero in the open critical strip off the line.
The witness is `DH`. The theorem sits in its own module, downstream of the 215 sites, and
bundles three theorems that, read together, carried the result before it:

- `dh_analytic_half` (`lean/ZetaLean/DHAnalytic.lean`): this `DH`, built from the quartic
  character mod 5, is entire, is given by the Davenport-Heilbronn Dirichlet series for
  Re s > 1, and satisfies its functional equation.
- `dh_zero_located`: a zero of `DH` lies in the closed square of half-width 3/64 about
  808517/10^6 + (21424837/250000) i, so its real part is between 0.761642 and 0.855392.
- `dh_separation_hundred`: below height 100, `DH` has a zero s with 0 < Re s < 1,
  0 < Im s ≤ 100 and Re s ≠ 1/2, while every zero of Mathlib's `riemannZeta` in that
  region has real part 1/2. The second half is hunt #137's RH to height 100 (`docs/45`).
  This one says more than the bundled theorem, since it adds the comparison with zeta.

The proof of `davenport_heilbronn_strip` takes the zero of `dh_zero_located` and the three
facts behind `dh_analytic_half`. It was compiled on 2026-10-26 by a second assembly of the
same 215 site oleans, whose earlier modules came out byte for byte as the first time. A
statement broken in the strip condition, `Re s < 0.76` or a line through the square, was
refused.

The assembly also proves `davenport_heilbronn : davenport_heilbronn_statement`
(`lean/ZetaLean/DavenportHeilbronn.lean`, line 129): some entire function with that
series and functional equation has a zero s with Re s ≠ 1/2. **That statement, as
defined, is also met by the trivial zero s = -1**, so it carries none of the result and
needs none of the 215 sites. `DH` combines the L-functions of two odd characters, which
vanish at s = -1, -3, -5, …, and `davenport_heilbronn_statement_of_trivial_zero`
(`lean/ZetaLean/DHTrivialZero.lean`) proves the statement from `DH (-1) = 0` alone. The
same statement for `riemannZeta` holds at its trivial zero s = -2. The adversarial review
of PR #353 found this on 2026-10-26; the definition stays as it is because the 215 site
oleans were compiled against the module that holds it.

The grade of `davenport_heilbronn_strip` and the three theorems above is
**kernel-checked, pending external verification**. No outside mathematician has reviewed them. Lean's own kernel
replayed the whole closure into an empty environment on 2026-10-27 (`leanchecker --fresh`,
1.57 million constants, accepted in 7 h 17 min), a re-check by the same kernel rather than
an independent one. The same day the independent checker `con-ron --verified` accepted the
closure split into 216 shards, one per site and one for the assembly, with coverage shown:
each of the 675,388 constants the final declarations depend on was checked in an accepted
shard (the final declarations themselves in a form abstracted over the site theorems),
and the shards agree on every constant they share (`RESULTS.md`, door 1).

## 2. How

The analytic half (`DH` entire, its series and its functional equation), the tail bounds
and a minimum-modulus criterion for a square were already kernel-checked in
`lean/ZetaLean`. The criterion says: if `|DH|` is small at the square's centre and
bounded below on its four edges, `DH` has a zero inside. What remained was numeric,
about half a million literal facts about `DH` on the square's boundary.

- **Plan v2** (`lean/cert/rung3_plan2.json`) covers it with 215 sites:
  - 110 boxes on a larger square bound `|DH|` above, which bounds `DH'` on the small
    square;
  - 104 grid points on the small square's edges bound `|DH|` below;
  - the centre bounds it above.
- **Each site** is a generated Lean module tree that evaluates `DH` in ball arithmetic.
  Every prime power `p^(-s)` is decided by the kernel in one step (`decide +kernel` on the
  whole recursive ball value). That step cost about 1 CPU-s against about 66 for the
  older staged form (`docs/37`, "Kernel evaluation by literal tables").
- **The 215 sites** compiled on GitHub Actions in 16.1 core-hours, and one assembly module
  combines their theorems through the criterion.
- **Planted faults** were refused at the declaration they touch: a tower radius one unit
  of 2^-64 low, a tail radius or a bound just under its target, and an eps' at the bound.

## 3. What it means, and what it does not

- **It shows the functional equation alone cannot give RH.** `davenport_heilbronn_strip`
  says so in one statement: a function with zeta's kind of series and functional
  equation has a zero in the open strip off the line. `dh_separation_hundred` adds that
  the zero lies below a height where `riemannZeta` has none. Any proof of RH must use something zeta has and `DH` lacks,
  such as the Euler product. This was known since 1936; what is new is that the
  counterexample is now a kernel-checked theorem in this repository, usable as a battery
  rival (`zeta.epstein.battery`, `docs/08` section 4) with its off-line zero proved
  rather than computed. A rival must use these strip theorems, not
  `davenport_heilbronn_statement`, whose analogue for zeta holds at a trivial zero.
- **It says nothing about RH.** It is a statement about a different function.
- **Prior art.** The lab produced it, so it is *original*. For a kernel-checked or
  formally verified proof of a non-trivial Davenport-Heilbronn zero off the line, the
  record is *searched-and-absent* in four web queries
  (`hunts/rung3_ball_production/PRIOR_ART.md`, which lists what was not searched,
  including zbMATH Open and the Lean Zulip). That is not a novelty claim.

## 4. Doors

The first door, a replay of the assembled environment, ran on 2026-10-27 (section 1):
Lean's own kernel replayed the whole closure (`leanchecker --fresh`), and the independent
`con-ron --verified` accepted the dependency closure of the 18 final declarations, split
site by site. What remains is outside review. The receipts of both runs are on the
operator's machine and not in this tree; the site oleans' GitHub artifacts expire about
2026-11-25, after which a re-run needs the 16 core-hours of sites again. (Updated
2026-10-30: this paragraph first named the replay as still to run.) The door beside it, one
bundled theorem stating the strip result in a single declaration, is done: it is
`davenport_heilbronn_strip` (section 1). The next is cheaper composites and terms by the same kernel decision. After
those come Spira's next off-line zeros, at heights 114.16, 166.48 and 176.70, which need
new plans. `hunts/rung3_ball_production/RESULTS.md`, "The doors", ranks them.
