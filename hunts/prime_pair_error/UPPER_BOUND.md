# Total prime-pair error: an unconditional upper-bound attempt

2026-09-06. This attempt obtains
\[
 E(N)\ll_C N^3(\log N)^{-C}\qquad\text{for every fixed }C>0,
\tag{1}
\]
unconditionally, for all sufficiently large integer \(N\), with ineffective
constants. This reproduces the classical circle-method level for the exact
difference-side quantity. **It is not an improvement over that level.**
The target \(N^{2+\epsilon}\), for every \(\epsilon>0\), remains open here.

The additional deductions are an arc-leakage bound, a large-denominator mixed
moment bound, and an exact description of the first low-denominator obstruction.
Their contribution to **total** \(E\) is recorded below. These are written
arguments from this attempt, not a claim of novelty or external verification.
The A/B project, its review, and its numerical records are separate.

## 1. Established inputs and scope

Write \(L=\log N\) and \(\exp1(t)=\exp(2\pi i t)\). Throughout,
\[
\begin{split}
 F_N(\alpha)&=\sum_{n=1}^N\Lambda(n)\exp1(n\alpha),&
 K_N(\alpha)&=\sum_{n=1}^N\exp1(n\alpha),\\
 \psi_2(N,k)&=\sum_{n=1}^{N-k}\Lambda(n)\Lambda(n+k),&
 E(N)&=2\sum_{k=1}^N
 [\psi_2(N,k)-\mathfrak S(k)(N-k)]^2 .
\end{split}
\]
Here \(\Lambda(p^a)=\log p\) for every \(a\ge1\);
\(\mathfrak S(k)=2C_2\prod_{p\mid k,\ p>2}(p-1)/(p-2)\) for even \(k\),
and is zero for odd \(k\). Also
\(C_2=\prod_{p>2}(1-(p-1)^{-2})\).
Only \(k=0\) is excluded. The \(k=N\) summand is zero. Odd separations remain:
one member of a contributing pair must be a power of 2, giving the elementary
bound \(\psi_2(N,k)\ll L^2\), hence their total contribution is \(O(NL^4)\).
No primes-only replacement, smoothing, or average in \(N\) is made.

The inputs used are:

1. [CHHL, Theorem 2 and Sections 3–4](https://arxiv.org/html/2308.14888v1):
   the lower bound \(E(N)=\Omega(N^{1+2\Theta-\delta})\) for every
   \(\delta>0\), and the centered Fourier setup below. The introduction
   reports \(E(N)\ll N^{5/2}L^c\) **under GRH for Dirichlet \(L\)-functions**.
   The [journal publication](https://doi.org/10.1016/j.jnt.2025.04.009),
   J. Number Theory 278 (2026), 422–450, retains this conditional benchmark.
2. [Goldston–Hunts–Ngotiaoco (GHN), Theorem 2](https://arxiv.org/html/1409.2151):
   the weighted tail estimate, with range and normalization checked in §2.
3. Siegel–Walfisz: for fixed \(B,H>0\), uniformly for \(q\le L^B\),
   \((b,q)=1\), and \(0\le t\le N\),
   \[
   \psi(t;q,b)=t/\phi(q)+O_{B,H}(NL^{-H}).
   \tag{SW}
   \]
   The version with a maximum over \(t\) follows from the usual theorem by
   treating \(t\le N/L^D\) trivially and applying it above that point, with
   \(D\) and the logarithmic saving chosen sufficiently large.
4. Vaughan's unconditional exponential-sum estimate:
   \[
   |F_N(\alpha)|\ll
   (Nq^{-1/2}+N^{4/5}+\sqrt{Nq})L^{5/2},
   \quad (a,q)=1,\quad |\alpha-a/q|\le q^{-2}.
   \tag{V}
   \]
   The additive large sieve at points spaced by at least \(\delta\):
   \[
   \sum_j\left|\sum_{n=1}^N b_n\exp1(nx_j)\right|^2
   \le (N-1+\delta^{-1})\sum_{n=1}^N|b_n|^2.
   \tag{LS}
   \]
   Both statements, with these hypotheses, are in Montgomery and Vaughan,
   [Multiplicative Number Theory II](https://personal.science.psu.edu/rcv4/571s25/montgomery-vaughanII.pdf),
   Theorems 17.1 and 19.4. Its §18.1 also uses (SW).

A bounded check of later work found no stronger theorem for this exact total
error. [Matomäki–Radziwiłł–Tao, Theorem 1.3(i)](https://arxiv.org/html/1707.01315)
controls almost all shifts in shorter ranges, with logarithmic savings, for
correlations on \((X,2X]\). Its stated range is
\(X^{8/33+\epsilon}\le H\le X^{1-\epsilon}\),
\(0\le h_0\le X^{1-\epsilon}\).
[Matomäki–Radziwiłł–Shao–Tao–Teräväinen, Theorem 1.5](https://arxiv.org/html/2411.05770v2)
gives higher-point almost-all-shift asymptotics and identifies the binary case
as already covered in that stronger shift range. Neither statement is imported
across the moving endpoint \(N-k\).
The recent [Srivastav estimate](https://arxiv.org/abs/2505.07803v2)
advertises a log-free range \(q\le N^{2/5-\eta}\); it does not cover the
\(q\asymp\sqrt N\) minor-arc approximants used here.
This is a check of applicable sources, not a claim of exhaustive latestness.
In particular, (1) is proved for differences below, rather than borrowed from
a Goldbach sum-side mean square.

**The RH implication, explicitly.** If \(\Theta=1/2+d\) with \(d>0\), use
CHHL Theorem 2 with \(\delta=d/2\), and the proposed upper-bound family with
\(\epsilon=d/2\). Along the lower-bound sequence the exponent is
\(2+3d/2\), whereas the eventual upper exponent is \(2+d/2\), a contradiction.
Thus the family forces \(\Theta=1/2\) and RH. A fixed factor \(L^c\) is
\(O_\epsilon(N^\epsilon)\), so any \(N^2L^c\) bound also suffices.
A fixed exponent greater than 2 leaves a nonzero gap and does not suffice.

## 2. Reproduced centered setup and the tail budget

For \(1\le z\le\sqrt N\), set
\[
\begin{split}
 c_q(k)&=\sum_{1\le a\le q,\ (a,q)=1}\exp1(ak/q),\\
 \mathfrak S_z(k)&=\sum_{q\le z}\frac{\mu(q)^2}{\phi(q)^2}c_q(k),\\
 V_z(\alpha)&=\sum_{q\le z}\frac{\mu(q)^2}{\phi(q)^2}
              \sum_a^*|K_N(\alpha-a/q)|^2,\\
 d_N&=\sum_{n\le N}\Lambda(n)^2,\qquad
 a_0(N,z)=d_N-N\mathfrak S_z(0),\\
 G_z&=|F_N|^2-V_z-a_0(N,z),\qquad J_{\rm ms}(N,z)=\|G_z\|_2^2.
\end{split}
\]
The notation \(V_z,G_z\) suppresses \(N\) only.
The Ramanujan sums are real and even. The coefficient at zero in
\(|F_N|^2-V_z\) is exactly \(a_0(N,z)\), so
\[
 J_{\rm ms}(N,z)=
 2\sum_{k=1}^N[\psi_2(N,k)-(N-k)\mathfrak S_z(k)]^2.
\tag{2}
\]
In particular the exact expansion is
\[
 J_{\rm ms}=\int|F_N|^4-2\int|F_N|^2V_z+\int V_z^2-a_0(N,z)^2.
\tag{3}
\]
All integrals without a set run over \(\mathbb T=\mathbb R/\mathbb Z\).
The constant term in (3) is subtracted, not added.

Extending \(\mathfrak S\) evenly, define
\[
 D_{\rm tail}(N,z)=2\sum_{k=1}^N(N-k)^2
                  |\mathfrak S(k)-\mathfrak S_z(k)|^2.
\]
The triangle inequality in coefficient space proves
\[
 |\sqrt E-\sqrt{J_{\rm ms}(N,z)}|\le\sqrt{D_{\rm tail}(N,z)},\qquad
 E\le2J_{\rm ms}(N,z)+2D_{\rm tail}(N,z).
\tag{4}
\]

GHN Theorem 2 is a **one-sided** sum over \(1\le k\le N\).
With its exact tail sum
\(\mathcal T(z)=\sum_{q>z}\mu(q)^2/\phi(q)^3\ll z^{-2}\),
and its constant \(c_{\rm GHN}\), it gives
\[
\begin{split}
 D_{\rm tail}(N,z)=2\bigg\{
  &\frac{N^3}{3}\mathcal T(z)
  -\frac{N^2}{4}\log^2(N/z^2)
  +c_{\rm GHN}N^2\log(N/z^2)\\
  &+O(N^2)+O(N^2z^{-1/2}\log(2N))\bigg\},
 \quad 1\le z\le\sqrt N.
\end{split}
\tag{5}
\]
Every term has been doubled. CHHL's displayed equation (13) carries the
one-sided coefficients into its two-sided notation; the order bound we need
is unaffected. We use the exact sum \(\mathcal T\), not its printed leading
constant. Its order bound also follows from GHN Lemma 2.
For \(u=N/z^2\ge1\), \(\log^2 u\ll u\), and
\(z^{3/2}\log(2N)/N\ll1\) throughout this range. Consequently
\[
 D_{\rm tail}(N,z)\ll N^3/z^2.
\tag{6}
\]
Fix **\(y=\lfloor\sqrt N\rfloor\)** for the target mean square.
Then \(D_{\rm tail}(N,y)\ll N^2\), including the integer endpoint.

## 3. Exact arcs and a bound for the full integrand on each set

Choose an independent integer \(Q\ge1\) with \(2Q^2<N\), and let
\[
 \delta_q=Q/(qN),\quad
 I_{q,a}=\{\alpha\in\mathbb T:\|\alpha-a/q\|\le\delta_q\},\quad
 \mathfrak M_Q=\bigcup_{q\le Q}\bigcup_a^* I_{q,a},\quad
 \mathfrak m_Q=\mathbb T\setminus\mathfrak M_Q.
\tag{7}
\]
The circular distance between distinct reduced fractions is at least
\(1/(qq')\); their radii sum to \(Q(q+q')/(qq'N)<1/(qq')\).
Thus the arcs are disjoint and \(|\mathfrak M_Q|\le2Q^2/N\).
The fraction \(1/1\) represents zero and its arc wraps around the endpoint.

On an arc set
\[
 P_{q,a}(\alpha)=\frac{\mu(q)}{\phi(q)}K_N(\alpha-a/q),\quad
 R_{q,a}=F_N-P_{q,a},\quad
 A_Q=\sum_{q,a}|P_{q,a}|^2{\bf1}_{I_{q,a}},\quad H_Q=V_Q-A_Q\ge0.
\]
Also set \(B_Q=|F_N|^2-A_Q\), and define
\[
 M_Q=\sum_{q,a}\int_{I_{q,a}}(|F_N|^2-|P_{q,a}|^2)^2,\qquad
 I_Q=\int_{\mathfrak m_Q}|F_N|^4.
\tag{8}
\]
The letter \(A_Q\) here is an arc model, not a reference to the earlier claim A.
Let \(\mathcal C f=f-\int f\), an orthogonal projection, and put
\(T_{y,Q}=\mathcal C(V_y-V_Q)\).
Equations (2) and (6) imply
\[
 \|T_{y,Q}\|_2\le\sqrt{D_{\rm tail}(N,y)}
                        +\sqrt{D_{\rm tail}(N,Q)}
 \ll N^{3/2}/Q.
\tag{9}
\]
This is the explicit relationship between the truncation \(y\) and the arc
parameter \(Q\); they have not been identified.

Pointwise on the whole circle,
\[
 G_y=B_Q-H_Q-a_0(N,Q)-T_{y,Q}.
\tag{10}
\]
Therefore the **full centered integrand** satisfies the two separate bounds
\[
\begin{split}
 \int_{\mathfrak M_Q}|G_y|^2
 &\le4M_Q+4\int_{\mathfrak M_Q}H_Q^2
       +4a_0(N,Q)^2|\mathfrak M_Q|
       +4\int_{\mathfrak M_Q}|T_{y,Q}|^2,\\
 \int_{\mathfrak m_Q}|G_y|^2
 &\le4I_Q+4\int_{\mathfrak m_Q}H_Q^2
       +4a_0(N,Q)^2|\mathfrak m_Q|
       +4\int_{\mathfrak m_Q}|T_{y,Q}|^2.
\end{split}
\tag{11}
\]
The \(V_y\) contribution on minor arcs is covered by \(H_Q,T_{y,Q}\)
and the constant adjustment. It has not been discarded.
CHHL gives \(a_0(N,Q)=N\log(N/Q)+O(N)\), hence its squared contribution
is \(O(N^2L^2)\).

For total \(E\), centering before applying Cauchy saves this extra constant:
\[
 \begin{split}
 J_{\rm ms}(N,Q)
 &=\|\mathcal C(B_Q-H_Q)\|_2^2
 \le 2(M_Q+I_Q)+2\|H_Q\|_2^2,\\
 E(N)&\le4M_Q+4I_Q+4\|H_Q\|_2^2+2D_{\rm tail}(N,Q).
 \end{split}
\tag{12}
\]
This is a bound for all separations at the original sharp cutoff.
It also bounds \(J_{\rm ms}(N,y)\) by (4).

## 4. Derived geometric leakage estimate

Put \(w(Q)=\max_{q\le Q}q/\phi(q)\). Uniformly for the parameters in (7),
\[
 \boxed{\ \|H_Q\|_2^2\ll
       \frac{N^3}{Q^2}\log(2Q)\,w(Q)^2.\ }
\tag{13}
\]
Here is the proof, including overlapping tails. The elementary kernel estimate
is \(|K_N(\beta)|\le\min(N,(2\|\beta\|)^{-1})\).
Integrating the tail outside each arc gives
\[
 \int H_Q\ll
 \sum_{q\le Q}\frac{\mu(q)^2}{\phi(q)\delta_q}
 =\frac NQ\sum_{q\le Q}\frac{\mu(q)^2q}{\phi(q)}\ll N.
\tag{14}
\]
For the last bound use
\(q/\phi(q)=\sum_{d\mid q}\mu(d)^2/\phi(d)\) and the convergent series
\(\sum_d\mu(d)^2/(d\phi(d))\).

In a dyadic denominator block \(R/2<q\le R\), centers are \(R^{-2}\)-spaced.
Every retained distance exceeds \(\delta=Q/(RN)\). Counting points on
successive intervals of length \(R^{-2}\), on each side of \(\alpha\), proves
\[
 \sum_{\substack{x\text{ a center in the block}\\\|\alpha-x\|>\delta}}
       \|\alpha-x\|^{-2}\ll \delta^{-2}+R^2/\delta .
\]
Indeed the first point costs \(O(\delta^{-2})\); the remaining decreasing
sum is bounded by that term plus the integral
\(R^2\int_\delta^\infty t^{-2}\,dt\).
Weights in this block are at most \(4w(Q)^2/R^2\). Hence
\[
 H_{Q,R}(\alpha)\ll
 w(Q)^2\left(N^2/Q^2+RN/Q\right).
\]
Sum the blocks (including the block containing \(q=1\)) to obtain
\[
 \|H_Q\|_\infty\ll
 w(Q)^2\left((N^2/Q^2)\log(2Q)+N\right).
\]
Since \(Q^2<N/2\), multiplying this by (14) proves (13).
In particular no disjointness of the omitted tails was assumed.

For a self-contained logarithmic bound use
\[
 \frac q{\phi(q)}
 =\prod_{p\mid q}(1+p^{-1})\prod_{p\mid q}(1-p^{-2})^{-1}
 \le\zeta(2)\sum_{d\mid q}\frac1d
 \le\zeta(2)(1+\log q).
\tag{15}
\]
With \(Q=\lfloor\sqrt N/3\rfloor\), \(N\ge36\), (6), (12), (13) yield
\[
 \boxed{\ E(N)\le4M_Q+4I_Q+O(N^2L^3).\ }
\tag{16}
\]
Thus the geometric component is in the RH-sufficient budget. It does not
bound \(M_Q\) or \(I_Q\). No improvement of the total exponent follows yet.
For these same square-root parameters, (11) gives explicitly
\[
 \int_{\mathfrak M_Q}|G_y|^2\le4M_Q+O(N^2L^3),\qquad
 \int_{\mathfrak m_Q}|G_y|^2\le4I_Q+O(N^2L^3).
\tag{16a}
\]
These are bounds on the full centered integrand on the two sets.

## 5. The unconditional baseline, proved for differences

First take \(Q=\lfloor L^B\rfloor\), for fixed \(B\), rather than a square-root
arc denominator. By (SW), splitting into residue classes gives uniformly
\[
 F_N(a/q+\beta)=\mu(q)K_N(\beta)/\phi(q)+O_{B,H}(NL^{-H}),
 \quad q\le Q,\quad |\beta|\le Q/(qN),
\tag{17}
\]
for every fixed \(H>0\).
To justify the uniformity, the additive partial sums have error at most
\(q\) times the (SW) error plus \(O(L\log(2q))\) from prime powers whose
prime divides \(q\). Replacing \(t\) by \(\lfloor t\rfloor\) costs \(O(1)\).
Partial summation against \(\exp1(t\beta)\) costs \(O(1+N|\beta|)\).
The arbitrary saving in (SW) absorbs both factors, each at most a fixed
power of \(L\). This includes nonsquarefree \(q\), where the model is zero.

Let \(\rho=O_{B,H}(NL^{-H})\). The local cancellation is retained as
\[
 |F_N|^2-|P_{q,a}|^2
 =2\operatorname{Re}(\overline{P_{q,a}}R_{q,a})+|R_{q,a}|^2,
\quad
 (|F_N|^2-|P_{q,a}|^2)^2\le8|P_{q,a}|^2|R_{q,a}|^2+2|R_{q,a}|^4.
\tag{18}
\]
Since \(\int A_Q\le N\sum_{q\le Q}\mu(q)^2/\phi(q)\ll N\log(2Q)\),
equations (7), (17), (18) give
\[
 M_Q\ll_{B,H}
 N^3\{L^{-2H}\log(2Q)+Q^2L^{-4H}\}.
\tag{19}
\]
This estimates a combined main-term difference in (3), not its three large
integrals independently.

On \(\mathfrak m_Q\), apply Dirichlet approximation with
\(\lceil N/Q\rceil\). It supplies a reduced \(a/q\) with
\[
 Q<q\le\lceil N/Q\rceil\le2N/Q,\qquad
 |\alpha-a/q|\le1/(q\lceil N/Q\rceil)\le q^{-2}.
\]
If \(q\le Q\), that same approximation would put \(\alpha\) in (7), a
contradiction. Thus (V) applies in its actual range. Also
\(d_N\le L\psi(N)\ll NL\), by Chebyshev's bound. Therefore
\[
 \begin{split}
 I_Q&\le\sup_{\mathfrak m_Q}|F_N|^2\int_{\mathbb T}|F_N|^2\\
 &\ll (N^3/Q+N^{13/5})L^6 .
 \end{split}
\tag{20}
\]
Combining (9), (11), (13), (15), (19), (20), the separate centered budgets are
\[
\begin{split}
 \int_{\mathfrak M_Q}|G_y|^2
 &\ll_{B,H}N^3\{L^{-2H}\log(2Q)+Q^2L^{-4H}
                       +Q^{-2}\log^3(2Q)\}+N^2L^2,\\
 \int_{\mathfrak m_Q}|G_y|^2
 &\ll (N^3/Q+N^{13/5})L^6
                  +N^3Q^{-2}\log^3(2Q)+N^2L^2 .
\end{split}
\tag{21}
\]
The dominant proved budget, after making (19) small, is \(N^3L^6/Q\)
from (20). Given \(C>0\), choose \(B=C+8\), \(H=B+C+10\).
Then (21) and \(D_{\rm tail}(N,y)\ll N^2\) prove (1).
All choices are fixed as \(N\to\infty\).

**Comparison.** This is an unconditional logarithmic saving from exponent 3,
not the conditional exponent \(5/2\) reported by CHHL. For each fixed \(C\),
\(N^3/L^C\) still exceeds \(N^{5/2}L^c\) eventually. The proof also gives
\(J_{\rm ms}(N,\lfloor\sqrt N\rfloor)\ll_C N^3/L^C\).
No transfer from a sum-side estimate has occurred: (2), (12) and (18) use
the difference Fourier coefficients throughout.

## 6. Modification: square-root arcs and the mixed moment

Now set \(Q=\lfloor\sqrt N/3\rfloor\). Formula (13) still applies, and the
tail in (16) is small. Formula (17) does **not** apply for all \(q\le Q\).
The same minor-arc proof gives only
\[
 I_Q\ll N^{13/5}L^6 .
\tag{22}
\]
For any fixed \(0<\epsilon<3/5\), this exceeds the desired \(N^{2+\epsilon}\)
budget by \(N^{3/5-\epsilon}\) times logs. The precise loss is
\(\int_{\mathfrak m}|F|^4\le\sup_{\mathfrak m}|F|^2d_N\) in (20).
In (V)'s proof the \(N^{4/5}\) term balances Type I size \(UV\) with
Type II sizes \(N/\sqrt U,N/\sqrt V\) at \(U=V=N^{2/5}\).
Changing \(Q\) cannot remove that term.

Instead of applying a pointwise progression error to every major arc,
use the average in (LS) on the weighted cross contribution. Define
\[
 U_Q=\sum_{q,a}\int_{I_{q,a}}|P_{q,a}|^2|R_{q,a}|^2,\qquad
 Z_Q=\sum_{q,a}\int_{I_{q,a}}|R_{q,a}|^4 .
\]
These are new names for moment components only. By (18) and (16),
\[
 E(N)\le32U_Q+8Z_Q+4I_Q+O(N^2L^3).
\tag{23}
\]
The residual and its cross term are both present.
This sufficient bound may lose phase cancellation compared with \(M_Q\);
it is not asserted equivalent to the original target.

Here is the actual saving from the modification. For \(1\le R<Q\), on the
block \(R<q\le\min(2R,Q)\), the centers \(a/q\) are
\((4R^2)^{-1}\)-spaced. Apply (LS) at these unshifted centers with
\(b_n=\Lambda(n)\exp1(n\beta)\), uniformly in \(\beta\), to obtain
\[
 \sum_{R<q\le\min(2R,Q)}\sum_a^*|F_N(a/q+\beta)|^2
 \le (N-1+4R^2)d_N .
\tag{24}
\]
Using \(|R_{q,a}|^2\le2|F_N|^2+2|P_{q,a}|^2\),
enlarging the \(\beta\)-intervals to \(|\beta|\le Q/(RN)\), and then using
\(\int_{\mathbb T}|K_N|^2=N\), proves
\[
 \begin{split}
 U_{R<q\le\min(2R,Q)}
 &\le\frac{2w(Q)^2}{R^2}(N-1+4R^2)d_NN
       +2N^3\sum_{R<q\le2R}\frac{\mu(q)^2}{\phi(q)^3}\\
 &\ll w(Q)^2N^3L/R^2 .
 \end{split}
\tag{25}
\]
The second term uses \(\int|K_N|^4\le N^3\) and
\(\sum_{q>R}\mu(q)^2/\phi(q)^3\ll R^{-2}\).
The enlarged interval has length at most one for these parameters.
Summing dyadic blocks, for \(1\le R_0<Q\),
\[
 \boxed{\ U_{q>R_0}\ll w(Q)^2 N^3L/R_0^2.\ }
\tag{26}
\]
Take \(R_0=Q/L\). By (15),
\[
 U_{q>R_0}\ll N^2L^5 .
\tag{27}
\]
Thus this entire part contributes at most \(O(N^2L^5)\) to total \(E\)
through (23), an acceptable RH-sufficient budget. It does not control
the remaining \(q\le R_0\) mixed moments.

The fourth residual moment still costs more. On arcs with \(q>R_0\),
\(|\beta|\le Q/(qN)\le q^{-2}\), so (V) bounds \(|F_N|\) there by
\[
 O\big((N/\sqrt{R_0}+N^{4/5}+\sqrt{NQ})L^{5/2}\big).
\]
The arcs are disjoint. Using \(|R|^4\le8(|F|^4+|P|^4)\) and
\(\int|F|^2=d_N\) gives
\[
 Z_{q>R_0}\ll
 (N^3/R_0+N^{13/5}+N^2Q)L^6+N^3/R_0^2
 \ll N^{13/5}L^6 .
\tag{28}
\]
The final inequality is for \(Q=\lfloor\sqrt N/3\rfloor,\ R_0=Q/L\)
and sufficiently large \(N\). It is a component estimate, not a bound on
total \(E\).

## 7. First unresolved low-denominator estimate, made explicit

Let \(\Delta(t)=\psi(t)-t\) for integer \(t\ge0\), and let \(U_1\) be the
\(q=1\) summand of \(U_Q\). Then
\[
 U_1=\int_{\|\beta\|\le Q/N}
                  |K_N(\beta)|^2|F_N(\beta)-K_N(\beta)|^2\,d\beta.
\]
We can identify this weighted integral without any prime-pair assertion:
\[
\begin{split}
 T_N&:=\int_{\mathbb T}|K_N|^2|F_N-K_N|^2\\
 &=\sum_{t=1}^N\Delta(t)^2
   +\sum_{t=1}^{N-1}[\Delta(N)-\Delta(t)]^2\\
 &=\frac{N+1}{2}\Delta(N)^2
      +2\sum_{t=1}^{N-1}[\Delta(t)-\Delta(N)/2]^2.
\end{split}
\tag{29}
\]
Proof: the coefficient of \(\exp1(m\beta)\) in \(K_N(F_N-K_N)\) is
\(\sum_{n=\max(1,m-N)}^{\min(N,m-1)}(\Lambda(n)-1)\).
For \(2\le m\le N+1\) it is \(\Delta(m-1)\); for
\(N+2\le m\le2N\) it is \(\Delta(N)-\Delta(m-N-1)\).
Parseval and completing the square give (29).

This full-circle identity transfers back to the actual arc:
\[
 0\le T_N-U_1
 \le\frac{N^2}{4Q^2}
       \int_{\mathbb T}|F_N-K_N|^2
 =\frac{N^2}{4Q^2}\sum_{n=1}^N(\Lambda(n)-1)^2
 \ll N^2L.
\tag{30}
\]
Thus the first unproved sufficient estimate in (23) already includes
\[
 \sum_{t=1}^N\Delta(t)^2+
 \sum_{t=1}^{N-1}[\Delta(N)-\Delta(t)]^2
 \ll_\epsilon N^{2+\epsilon}\quad\text{for every }\epsilon>0.
\tag{31}
\]
Its contribution would be \(32U_1=O_\epsilon(N^{2+\epsilon})\) in (23).
The exact completed square in (29) shows why an average over \(t\) cannot
hide the endpoint: (31) implies
\(\Delta(N)=O_\epsilon(N^{1/2+\epsilon})\) for every \(\epsilon>0\),
the classical RH-strength prime-counting remainder bound.
Conversely, **assuming RH**, the bound
\(\Delta(t)=O(\sqrt t\log^2(2t))\) yields
\(T_N=O(N^2L^4)\). This discharges only \(U_1\), not (23).
No RH estimate is used in (1), (13), (26), (29), or (30).

Using (SW) with \(q=1\) gives, for every fixed \(H\),
\(\max_{t\le N}|\Delta(t)|\ll_H NL^{-H}\), and (29) only gives
\(T_N\ll_H N^3L^{-2H}\). This is where the unconditional attempt still
loses a power of \(N\) on this component. Naming (31) as a lemma would
conceal an assumption. The modification (24) solves the large-denominator
weighted part but cannot estimate this single low-denominator term.
Even proving (31) would leave \(U_{2\le q\le R_0}\), \(Z_{q\le R_0}\),
and the fourth-moment excess in (22), (28).

The current continuation point is consequently concrete: retain the exact
intensity difference in (18) if attempting to recover phase cancellation
lost in (23), or prove additional cancellation in these displayed weighted
and fourth moments. No such estimate has been established in this attempt.
The obstruction is to this proof, not a new impossibility theorem.

## 8. Error budget and verification status

For \(Q=\lfloor\sqrt N/3\rfloor,\ R_0=Q/L\), the contribution accounting is:

| Component | Bound established here | Contribution to total \(E\) |
| --- | --- | --- |
| Tail and geometric leakage | \(O(N^2L^3)\) | Included in (16), (23) |
| Mixed moment with \(q>R_0\) | \(O(N^2L^5)\) | \(32U_{q>R_0}\) in (23) |
| Minor fourth moment | \(O(N^{13/5}L^6)\) | \(4I_Q\); exceeds target budget |
| Fourth residual moment with \(q>R_0\) | \(O(N^{13/5}L^6)\) | \(8Z_{q>R_0}\); exceeds target budget |
| Mixed moment at \(q=1\) | (29), (30); \(O_H(N^3L^{-2H})\) | \(32U_1\); (31) remains unproved |
| Other moments with \(q\le R_0\) | No adequate estimate here | Still required by (23) |

The strongest completed **total** bound is (1), with \(y=\lfloor\sqrt N\rfloor\)
and polylogarithmic arcs. There is no unconditional exponent improvement
over the classical baseline and no proof of either target.

The six finite cases in tests/test_prime_pair_upper_bound.py check:
direct pair sums against Fourier integration, the diagonal subtraction and
factor 2, nonzero odd shifts and proper prime powers, finite Ramanujan
truncation, the full identity (10) on both arc sets, and the convolution
identity (29) on arbitrary weights. Such checks test identities and indexing.
They do not test or prove an asymptotic estimate.

Independent model review (2026-09-06) found no substantive defect in the
completed logarithmic-saving bound, geometric leakage estimate,
large-denominator mixed moment bound, or \(q=1\) identities. It checked source
normalizations, parameter uniformity, and endpoint indexing. A wording
clarification before (24) was incorporated. The reviewer separately checked
the convolution and completed square on 640 exact signed-integer-weight
examples with \(1\le N\le64\). This is review of a handwritten argument, not
kernel checking or external human verification. It is separate from the
completed A/B review.

Local validation: 23/23 cases passed across the new tests and the required
document-numbering, hunt-discipline and door checks. The generated context
index is current. Both ball-arithmetic backends are installed.
The pre-edit full fast suite had 2813 passes, one skip, three expected
failures, and one failure:
tests/test_dossier_hardy_z.py::test_proved_cites_a_watched_dated_kernel_run_the_tree_corroborates.
Its recorded observation is 2026-08-13 while its Lean file last changed on
2026-09-05. That pre-existing record is outside this upper-bound assignment;
it was not altered. The full suite is not reported green.
