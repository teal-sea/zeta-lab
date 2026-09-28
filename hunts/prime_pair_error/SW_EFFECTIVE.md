# Is there an effective Siegel-Walfisz constant behind UPPER_BOUND.md Section 7's T_N bound?

`delta_sq_sw_bind.py` evaluates Section 7's proved statement
\(T_N=\sum_{t=1}^N\Delta(t)^2+\sum_{t=1}^{N-1}[\Delta(N)-\Delta(t)]^2\ll_H
N^3L^{-2H}\) (\(L=\log N\)) under an explicit, labeled convention -- assumed
implied constant \(c(H)=1\) -- because the proof, resting on Siegel-Walfisz,
never names \(c(H)\) and never says whether it is effective. That script
found the convention binds at \(H=1,2\) and is violated at \(H=4,8\) against
the measured \(S(N)=\sum_{t\le N}\Delta(t)^2\) in `results_delta_sq.json`.
This note asks the question that script leaves open: is there a real,
computable value in place of the convention, from a known effective version
of Siegel-Walfisz -- or does this hit the same ineffectivity wall
`tb_bind.py` already hit for Theorem B's \(\Omega\) constant?

**Short answer: no, this does not recur, for the specific line Section 7
actually uses.** That line only invokes Siegel-Walfisz at \(q=1\), and the
\(q=1\) case of Siegel-Walfisz is not really Siegel-Walfisz at all -- it is
the classical prime number theorem remainder derived from the zero-free
region for \(\zeta(s)\) alone, which has been effective since de la Vallée
Poussin (1899), decades before Siegel's theorem (1935) or Siegel-Walfisz
(1936) existed, and for a structural reason that has nothing to do with how
much has been proved since: no real Dirichlet character enters at \(q=1\),
so there is no Landau-Siegel zero to fail to exclude. An effective
\(c_1,K,x_0\) with \(|\Delta(t)|\le Kt\exp(-c_1\sqrt{\log t})\) for
\(t\ge x_0\) is known to exist in the literature. What this attempt could
not do, for lack of network or library access in this sandbox, is pull a
citation-checked numeric value for \(c_1\); `delta_sq_sw_effective_bind.py`
instead computes, from the measured data, the threshold \(c_1\) would have
to clear to be violated, and that threshold is loose enough that any
plausible published value very likely clears it. Section 4 states precisely
what remains unverified and why that is a bounded lookup, not a
mathematical wall. Nothing here bears on RH.

## 1. What Section 7 actually invokes, re-read closely

Section 1 item 3 states (SW) in its general form: for fixed \(B,H>0\),
uniformly for \(q\le L^B\), \((b,q)=1\), and \(0\le t\le N\),
\(\psi(t;q,b)=t/\phi(q)+O_{B,H}(NL^{-H})\). This general statement, uniform
over a modulus \(q\) that grows with \(N\) up to any fixed power of \(\log
N\), is the genuine Siegel-Walfisz theorem, and it is the textbook example
of an ineffective result: proving it uniformly in \(q\) requires excluding,
for every \(q\) in the growing range, the possibility of an exceptional real
zero (a Landau-Siegel zero) of \(L(s,\chi)\) for a real primitive character
\(\chi\) mod \(q\), and the only known tool for that exclusion, Siegel's
theorem, is proved by comparing two hypothetical exceptional characters
against each other and produces no computable bound on how close to 1 such
a zero could be -- if one existed. This is the same shape of ineffectivity
`tb_bind.py` and `THEOREM_B_SEQUENCE.md` describe for \(\Theta_\chi\): an
existence statement with no extractable constant.

But Section 7 does not use (SW) at a growing \(q\). It uses it once, at
\(q=1\): "Using (SW) with \(q=1\) gives, for every fixed \(H\),
\(\max_{t\le N}|\Delta(t)|\ll_H NL^{-H}\)." At \(q=1\), \(\phi(q)=1\), the
only reduced residue is \(b=1\), and \(\psi(t;1,1)\) is just \(\psi(t)\).
There is exactly one Dirichlet character mod 1 (the principal character),
and no real primitive character of modulus greater than 1 is involved at
any point. The statement being invoked is

\[
\psi(t)=t+O_H(NL^{-H})\quad\text{for every fixed }H,
\]

which is a corollary of the classical, effective estimate

\[
\psi(x)=x+O\bigl(x\exp(-c_1\sqrt{\log x})\bigr) \tag{$*$}
\]

(or the sharper Vinogradov–Korobov-type saving
\(\exp(-c(\log x)^{3/5}/(\log\log x)^{1/5})\), which decays even faster and
implies $(*)$), since \(\exp(-c_1\sqrt{\log x})\) beats every fixed power of
\(\log x\) as \(x\to\infty\): for any fixed \(H\) there is an explicit,
computable \(x_0(H)\) past which \(\exp(-c_1\sqrt{\log x})\le L^{-H}\), and
below \(x_0(H)\) the maximum of \(|\Delta(t)|\) is controlled by the
trivial, equally effective Chebyshev-type bound \(\psi(t)\le Kt\) for an
absolute, explicit \(K\) (e.g. the classical \(\psi(t)<1.04\,t\) for all
\(t>0\), a completely elementary, long-published constant with no
zero-free-region input at all). So the corollary Section 7 states is not
merely "eventually true for some unnamed constant" -- it follows, term by
term, from a chain of classical statements each of which has always carried
an explicit, computable constant.

## 2. Why $(*)$ is effective and the general (SW) is not: the actual dividing line

The dividing line is not "Siegel-Walfisz versus something else" -- it is
whether a real primitive Dirichlet character is anywhere in the argument.

\(\zeta(s)\) is \(L(s,\chi_0)\) for the principal character mod 1, and the
classical zero-free region \(\sigma>1-c_0/\log(|t|+2)\) for \(\zeta(s)\) is
proved by the elementary "3-4-1" inequality
\(3\log|\zeta(\sigma)|+4\,\mathrm{Re}\log\zeta(\sigma+it)+\mathrm{Re}\log
\zeta(\sigma+2it)\ge0\) (\(\sigma>1\)), applied to \(\zeta\) alone -- no
auxiliary \(L\)-function, no comparison between two hypothetical
characters, and consequently no case split on whether an exceptional zero
exists. This argument, first given by de la Vallée Poussin, produces an
explicit \(c_0\) directly, and turning a zero-free region into a prime
number theorem remainder of the shape $(*)$ by a contour shift past that
region is equally elementary and equally explicit; this chain is standard
material predating Siegel-Walfisz by decades (see e.g. Ingham, *The
Distribution of Prime Numbers*, ch. III; Titchmarsh, *The Theory of the
Riemann Zeta-Function*, ch. III; or the treatment in Montgomery and Vaughan,
*Multiplicative Number Theory I: Classical Theory*, already the source this
hunt cites elsewhere for the large sieve and Vaughan's identity, ch. 6 and
ch. 8 for the zero-free region and PNT error term). Numerically explicit
versions of \(c_0\) and hence of $(*)$'s \(c_1\) have been published and
progressively sharpened for over a century; named examples this attempt can
identify (without a verified citation-checked digit from any of them, see
Section 4) include Rosser and Schoenfeld (1962), McCurley (1984), Kadiri
(2005), Mossinghoff and Trudgian (2015), Platt and Trudgian (2021), and
Broadbent, Kadiri, Lumley, Ng and Wilk (2021), the last group of which
targets the PNT error term itself rather than only the zero-free region.

Siegel-Walfisz proper, for \(q>1\) in a range growing with \(N\), needs the
non-vanishing of \(L(s,\chi)\) near \(\sigma=1\) for every real primitive
\(\chi\) mod every such \(q\) *simultaneously*, and the only known
unconditional tool for that is Siegel's theorem: for every \(\epsilon>0\)
there is a \(c(\epsilon)>0\) with \(L(1,\chi)>c(\epsilon)q^{-\epsilon}\) for
every real primitive \(\chi\) mod \(q\). Siegel's proof is a case split on
whether a second, hypothetical exceptional character exists and compares
the two; the constant \(c(\epsilon)\) it produces is not extractable from
the proof, because one of the two cases the proof splits on is never known
to hold or fail. This is a comparison between two objects that might not
exist, not an "3-4-1"-style direct estimate, and it is the entire reason
Siegel-Walfisz is the textbook example of an ineffective theorem (see also
Tatuzawa's 1951 refinement, which makes \(c(\epsilon)\) effective *for all
but at most one* real primitive character of each conductor size -- still
not effective for a specific, unidentified exceptional modulus, which is
exactly the case a uniform-in-\(q\) statement cannot exclude). At \(q=1\)
this case split never arises: there is no real primitive character mod 1
other than the (trivially non-vanishing, non-exceptional) principal
character, so nothing about Siegel's theorem is invoked, whether or not the
citation attached to (SW) in UPPER_BOUND.md's item 3 names it that way.

## 3. What this changes for T_N, and what it does not change

Squaring $(*)$'s corollary and summing across \(\sim N\) terms the way (29)
does gives, on the same "convention constant" basis `delta_sq_sw_bind.py`
already used (leading constant \(K=1\), labeled, not derived from a named
theorem):

\[
T_N \lesssim N^3\exp(-2c_1\sqrt{\log N}), \tag{$**$}
\]

which is strictly stronger than \(N^3L^{-2H}\) for any fixed \(H\), for the
same reason $(*)$ is stronger than its own \(L^{-H}\) corollary.
`delta_sq_sw_effective_bind.py` evaluates $(**)$ against the measured
\(S(N)\) in `results_delta_sq.json` (the same leading, non-negative half of
\(T_N\) `delta_sq_sw_bind.py` used, with the same one-directional
\(S(N)\le T_N\) caveat: a violated bound against \(S(N)\) is also violated
against \(T_N\); a bound exceeding \(S(N)\) does not by itself show it
would still exceed \(T_N\)).

What this note does **not** change is Section 7's own assessment of what
this component is worth to the larger unconditional upper-bound attempt.
Section 7 already says, in the paragraph introducing this line: "This is
where the unconditional attempt still loses a power of \(N\) on this
component." \(N^3L^{-2H}\) -- or its sharper effective cousin
\(N^3\exp(-2c_1\sqrt{\log N})\) -- is a full power of \(N\) above the
unproved target (31), \(N^{2+\epsilon}\), for every fixed \(H\) or \(c_1\):
the ratio \(N^3\exp(-2c_1\sqrt{\log N})/N^{2+\epsilon}=N^{1-\epsilon}
\exp(-2c_1\sqrt{\log N})\to\infty\). Knowing \(c_1\) explicitly makes the
\(N^3\)-scale statement a genuine number instead of an unnamed-constant
placeholder; it does not shrink the exponent of \(N\), and it does not
discharge (31) or move (23)'s other unresolved pieces (\(U_{2\le q\le
R_0}\), \(Z_{q\le R_0}\), the fourth-moment excess), which Section 7 already
lists as untouched by this estimate. Effectiveness and sufficiency are
different questions; this note and its script answer only the first, and
only for the \(q=1\) term.

It also does not extend to the general (SW) statement as used elsewhere in
this hunt. UPPER_BOUND.md Section 5's major-arc argument and
`SW_MOMENT_SPLICE.md`'s splice both work with \(q\) ranging up to \(L^B\)
for \(q>1\), which is exactly the regime where the Siegel-zero case split
of Section 2 above is unavoidable and no effective constant is known. This
note resolves only the degenerate \(q=1\) instance Section 7 happens to use
for \(T_N\); it says nothing about, and does not weaken, the ineffectivity
of (SW) at \(q>1\) growing with \(N\).

## 4. What is not verified here, and why that is a bounded gap, not a wall

This attempt's tools are `/opt/zeta-venv/bin/python` (mpmath, numpy, scipy,
sympy, python-flint, cypari2) and local text search (`grep`, `rg`, `ls`,
`cat`, `head`, `tail`, `wc`, `find`) over this worktree -- no network access
and no cached copies of Rosser–Schoenfeld (1962), McCurley (1984), Kadiri
(2005), Mossinghoff–Trudgian (2015), Platt–Trudgian (2021), or
Broadbent–Kadiri–Lumley–Ng–Wilk (2021) are present in this worktree to
`cat` or `grep`. So while this attempt is confident, from standard analytic
number theory, that some explicit \((c_1,K,x_0)\) triple for $(*)$ is
published in the literature above -- the *existence* of an effective
constant here is not in serious doubt, unlike \(\Theta_\chi\)'s exact value
or Theorem B's Omega constant in `tb_bind.py`, which are not just
unlooked-up but genuinely open or non-constructive -- this attempt cannot
quote a citation-checked numeric digit for \(c_1\) (or the sharper
Vinogradov–Korobov exponent triple) without risking a misremembered
constant presented as sourced fact, which this hunt's conventions do not
allow.

`delta_sq_sw_effective_bind.py` sidesteps that by solving the comparison
the other way: at each ladder \(N\), it computes the threshold
\(c_1^*(N)=(3\log N-\log S(N))/(2\sqrt{\log N})\) at which the
convention-\(K=1\) bound $(**)$ would exactly equal the measured \(S(N)\);
$(**)$ exceeds (binds against) \(S(N)\) at that \(N\) iff the true \(c_1\)
is below \(c_1^*(N)\). Across the eight ladder points (\(N=10^5\) to
\(10^7\)), \(c_1^*(N)\) ranges from about 2.26 (at \(N=10^5\), the binding
constraint across the whole ladder) up to about 2.50 (at \(N=10^7\)). Any
true effective \(c_1\) below about 2.26 makes $(**)$ exceed measured
\(S(N)\) at every ladder cutoff, in the same "binds, not vacuous" sense
`delta_sq_sw_bind.py` used for \(H=1,2\). Published explicit
zero-free-region constants, as far as this attempt can recall without a
checked citation, sit well below that -- on the order of a few tenths up to
roughly 1 in this normalization, not above 2 -- so it is likely, though not
confirmed in this run, that the true effective bound binds comfortably
everywhere \(S(N)\) has been measured, unlike the convention-1
\(L^{-2H}\) bound at \(H=4,8\) in `results_delta_sq_sw_bind.json`, which was
violated there. The script also reports an illustrative sweep of \(c_1\)
over \([0.05,3.0]\) for the same comparison without relying on the recalled
range being exactly right.

**The residual task** is narrow and concrete: retrieve one of the papers
named in Section 1 (or a survey citing its constant, e.g. via a session
with network or a local mathematics library this sandbox does not have),
extract its explicit \((c_1,K,x_0)\) or Vinogradov–Korobov-type
\((c,\kappa,\lambda,K,x_0)\), and rerun
`delta_sq_sw_effective_bind.py` with that value in place of the swept
range, replacing "likely, not confirmed" with a checked verdict. That is a
literature lookup and an arithmetic substitution, not a new estimate and
not an open problem -- a materially different kind of gap from Theorem B's
missing \(\Theta_\chi\), missing implied constant, and missing witness
sequence in `tb_bind.py`, none of which exist in the literature to be
looked up at all.
