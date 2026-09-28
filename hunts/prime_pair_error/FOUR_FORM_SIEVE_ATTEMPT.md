# Compact attempt: signed four-form sieve for E_corr

2026-09-09. Base #215 at 3645324cf69497e197592fdcc2f630c4ed6504b0.
Working record only. No research PR or push: this mechanism fails to
improve the complete bound. #209-#215 are unchanged.

The chosen mechanism is a direct combinatorial sieve for the four
forms \(n,n+h,m,m+h\). It retains their joint local congruences and
subtracts the actual mixed moment before taking a final bound.
There are no Fourier kernels, window estimates, new sufficient
criteria, or changes to the accepted exceptional correction.
The deductions below are handwritten, with small algebra checks,
not an externally verified or novel result.

## Full budget before the sieve

Put \(p_h=\psi_2(N,h)\), \(t_h=(N-h)\mathfrak S(h)\), and
\(C_h=C_N(h)\), for all \(1\le h\le N\). Define
\[
 Q=\sum_h p_h^2,\quad I=\sum_h p_ht_h,\quad B=\sum_h t_h^2,
 \quad U=\sum_h C_h(p_h-t_h),\quad V=\sum_h C_h^2.
\]
Exactly,
\[
 E_{\rm corr}=2Q-4I+2B-4U+2V.                         \tag{1}
\]
Thus the actual mixed contribution and the centered \(|W|^2\)
contribution remain combined in the original correlations. Nothing
is discarded by decomposing \(F=H+W\). No model-to-target
approximation is made: \(t_h\) and \(C_h\) are the original exact
ones, so no separate sieve-model approximation is set to zero.
All shifts and frequencies are included through (1).

Let
\[
 \mathfrak A=\prod_p(1+(p-1)^{-3}).
\]
The proposed budget was to match the three leading coefficients
\(Q,I,B\) at \(\mathfrak A N^3/3\), retaining \(U,V\), with a
fixed-power remainder. The calculation below instead produces a
sieve multiplier \(\kappa_s\asymp s^4\) in \(Q\). This already leaves
a cubic excess in the no-exception case, before any exceptional
interaction needs bounding.

## The arithmetic information retained

For a prime \(p\), the number of triples \((h,n,m)\bmod p\) for
which all four forms are nonzero is
\[
 (p-1)^2+(p-1)(p-2)^2=p^3-4p^2+6p-3.
\]
The first term is \(h=0\); all other \(h\) give the second.
Consequently the dimension-four sieve density is
\[
 g(p)=4/p-6/p^2+3/p^3,\qquad
 1-g(p)=(1-1/p)^4(1+(p-1)^{-3}).                    \tag{2}
\]
In particular \(g(2)=7/8<1\): parity is retained exactly.
This is the same Euler product that appears in both centered
comparison terms below. Using four unrelated prime densities
would lose this matching constant.

Take the exact sharp region
\[
 \Omega_N=\{(h,n,m)\in\mathbb R^3:
 h>0,\ n>0,\ m>0,\ n+h\le N,\ m+h\le N\}.
\]
Its volume is \(N^3/3\); its integer points have
\(1\le h\le N\), \(1\le n,m\le N-h\).
For squarefree \(d\), CRT gives at most \(4^{\omega(d)}d^2\)
bad residue triples. Counting each residue class by cubes of
side \(d\) gives, for \(d\le N\),
\[
 \#\{(h,n,m)\in\Omega_N\cap\mathbb Z^3:
               d\mid n(n+h)m(m+h)\}
 =\frac{N^3}{3}g(d)+O(N^2 4^{\omega(d)}).             \tag{3}
\]
Indeed a class contributes volume divided by \(d^3\), with error
\(O(N^2/d^2+N/d+1)\). For \(d\le N\) the first term dominates.
Since \(4^{\omega(d)}\le\tau_4(d)\), summing (3) to \(D\) costs
\(O(N^2D(1+\log D)^3)\).

Use \(D=N^{1/2}\), a fixed sufficiently large \(s\ge37\), and
\(z=N^{1/(2s)}\). Here \(z\) is a sieve parameter, not the
source model threshold \(Z\), which is unchanged.
[TT v4, Lemma 5.1](https://arxiv.org/html/2107.02158v4#S5)
applies with dimension 4, \(D=z^s\ge z^{37}\), and an absolute
sieve constant \(K\). Its *actual* relative error is
\(O(e^{36-s}K^{10})\). Applicability at \(s=37\) alone does not
make this error small.

Let \(S_z(N)\) count the triples with all four forms coprime to
\(\prod_{p<z}p\). The lemma and Mertens' product formula give
\[
 S_z(N)=
 \frac{\mathfrak A e^{-4\gamma}N^3}{3(\log z)^4}
 [1+O(e^{36-s}K^{10})+o_s(1)]
 +O(N^{5/2}\log^3N).                                \tag{4}
\]
The \(o_s(1)\) includes the Mertens remainder and is not a power
saving. First fix \(s\) large enough for the indicated sieve
error to be small, then take \(N\) sufficiently large depending
on \(s\). There is no numerical parameter sweep.

If all four forms are primes at least \(z\), their von Mangoldt
product is at most \((\log N)^4\) times this indicator. Cases
involving a prime below \(z\) or any proper prime power are paid
for separately. There are \(O(z+\sqrt N\log N)\) possible bad
values, and fixing any one form leaves at most \(N^2\) triples.
Their total weighted contribution is
\(O(N^{5/2}\log^5 N)\). They are not omitted from \(Q\).
Thus
\[
 Q\le\kappa_s\frac{\mathfrak A N^3}{3}
                         +O(N^{5/2}\log^7N),         \tag{5}
\]
where one may take
\(\kappa_s=2e^{-4\gamma}(2s)^4\) after the choices just stated.
More precisely, the coefficient furnished by (4) is
\[
 e^{-4\gamma}(2s)^4
              [1+O(e^{36-s}K^{10})+o_s(1)].           \tag{6}
\]
It is bounded away from 1 and grows like \(s^4\). Choosing a
larger fixed \(s\) to improve the sieve accuracy makes this
multiplier worse. Taking \(s\) smaller beyond the supported
range does not have a justified error estimate here.

## The signed subtraction is computed, not assumed

Write \(C_2=\prod_{p>2}(1-(p-1)^{-2})\). For odd squarefree
\(d\), set \(u(d)=\prod_{p\mid d}(p-2)^{-1}\), and set \(u(d)=0\)
for other \(d\). Then
\[
 \mathfrak S(h)=2C_2\,1_{2\mid h}\sum_{d\mid h,\ d\ {\rm odd}}u(d).
\]
For a fixed integer \(J\), nonnegativity permits the lower bound
obtained by retaining \(d\le J\).
For each such fixed \(d\), fixed-modulus PNT in progressions and
two-variable partial summation give
\[
 \sum_{\substack{1\le n<m\le N\\m\equiv n\pmod{2d}}}
 (N-m+n)\Lambda(n)\Lambda(m)
       =\frac{N^3}{3\phi(d)}+o_d(N^3).                \tag{7}
\]
The reduced residues contribute \(\phi(2d)\) copies of density
\(1/\phi(2d)^2\), and the weighted triangle has integral
\(N^3/3\). Nonreduced classes contain only powers of primes
dividing \(2d\) and are lower order. The diagonal is excluded
and contributes only \(O(N^2\log N)\) if inserted temporarily.

The precise source input is the PNT for **fixed** \(a,q\),
\(\psi(x;q,a)=x/\phi(q)+o_{a,q}(x)\), explicitly stated in
[Tao's Notes 2, Exercise 50(ii)](https://terrytao.wordpress.com/2014/12/09/254a-notes-2-complex-analytic-multiplicative-number-theory/).
It also follows from the Siegel-Walfisz statement used in
[Montgomery--Vaughan II, Section 18.1, p. 109](https://personal.science.psu.edu/rcv4/571s25/montgomery-vaughanII.pdf).
No growing-modulus or polynomial error estimate is imported.

Define
\[
 \mathfrak A_J=2C_2\sum_{\substack{d\le J\\d\ {\rm odd}}}
                                      \frac{u(d)}{\phi(d)}.
\]
Then (7) proves
\[
 I\ge\frac{\mathfrak A_J}{3}N^3+o_J(N^3),\qquad
 0\le\mathfrak A-\mathfrak A_J\ll J^{-1/2}.            \tag{8}
\]
The limiting Euler factor is
\[
 \left(1-\frac1{(p-1)^2}\right)
 \left(1+\frac1{(p-2)(p-1)}\right)
                   =1+\frac1{(p-1)^3}.
\]
The tail bound follows from convergence of
\(\sum u(d)\sqrt d/\phi(d)\). The \(o_J\) is retained with
\(J\) fixed. Turning it into a power saving is not authorized
by the theorem.

The model square is elementary:
\[
 B=\frac{\mathfrak A}{3}N^3+O(N^{5/2}).              \tag{9}
\]
For detail, expand
\(\mathfrak S(h)^2=4C_2^2 1_{2\mid h}\sum_{d\mid h}v(d)\),
where \(v\) is odd squarefree-supported and
\(v(p)=(2p-3)/(p-2)^2\). Sum
\(\sum_{2d\mid h}(N-h)^2=N^3/(6d)+O(N^2)\).
The error sum uses \(\sum_{d\le N}v(d)\ll\log^2N\);
the tail uses \(\sum_d v(d)/\sqrt d<\infty\).
Its Euler factors give the same \(\mathfrak A\).

## Decisive inequality for the complete corrected error

Keep the exact exceptional terms in (1). The inherited #212 bound
is \(V\ll N^3\Xi_N\), where \(\Xi_N=0\) with no exception and
otherwise
\[
 \Xi_N=
 1_{q\ {\rm odd}}N^{-2(1-\beta)}\frac{q^2}{\phi(q)^4}
 +N^{-4(1-\beta)}\frac{q^2}{\phi(q)^3}.
\]
This covers changing exceptional data and both even conductor
types. Only at this point use
\[
 |U|\le(\sqrt Q+\sqrt B)\sqrt V.
\]
Equations (1), (5), (8), and (9) yield the complete estimate
\[
 \boxed{\begin{aligned}
 E_{\rm corr}\le{}&
 \left[\frac{2\mathfrak A}{3}(\kappa_s-1)
       +O(J^{-1/2})+o_J(1)\right]N^3\\
 &+O_s\!\left(N^3(\sqrt{\Xi_N}+\Xi_N)\right)
  +O(N^{5/2}\log^7N).
 \end{aligned}}                                             \tag{10}
\]
The exceptional cross term is paid for explicitly; no favorable
sign is asserted. There are no remaining frequency ranges or
window recombination costs. The geometric and prime-power
remainders save a fixed power, but the main coefficient does not.

Already with \(\Xi_N=0\), taking \(J\) large and then \(N\) large
leaves the positive cubic coefficient
\(2\mathfrak A(\kappa_s-1)/3\).
The arithmetic step that failed is the replacement
\[
 \prod_{i=1}^4\Lambda(L_i)
 \le(\log N)^4 1_{(\prod_iL_i,P(z))=1}
 \quad\hbox{outside the paid small-value/prime-power cases}.
\]
The sifted population still contains composites. Its computed
weighted density exceeds the needed four-prime density by the
factor in (6). A coefficient-\(1+O(N^{-\eta})\) prime-sensitive
four-form upper estimate is unsupported, as are matching
power-quality mixed-moment errors when \(J\) grows. The argument
supplies neither. This diagnoses this particular sieve mechanism,
not an impossibility theorem for signed dispersion.

The calibration is respected: no prime-counting bound with a
fixed power error was assumed. The known complete
\(E_{\rm corr}\ll_\kappa N^3e^{-c_\kappa(\log N)^\kappa}\)
remains stronger than (10), and is unchanged. Original \(E\)
also receives no improvement. This does not warrant a research PR.

The fixed diagnostic in artifacts/four_form_sieve checks only
finite density, Euler-factor, sharp-count, and centered-expansion
algebra at \(N=32\), with a 30-second cap and one numerical thread.
It does not numerically validate any asymptotic or exceptional zero.
