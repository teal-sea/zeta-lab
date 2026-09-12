# RESULTS: Erdős #126, independent-architect arm (`support_f3ab3e34`)

**Hunt, not a result. Nothing here is evidence for or against RH (`docs/08`).**

**Headline.** The problem reduces, in four lines and with no new ideas, to
counting solutions of the unit equation:

> $g(k) \le 2 + N(k+1)$, where $N(r)$ is the maximum number of solutions of
> $x + y = 1$ with $x, y$ in a subgroup of $\mathbb{Q}^{*}$ of rank $r$.

So **$N(r) = \exp(o(r))$ implies Erdős #126**, and the best known bound
$N(r) \le 2^{8r+8}$ (Beukers–Schlickewei) is exactly the exponential wall the
1934 theorem already sits at. The believed truth for $N(r)$ is far below that:
Erdős–Stewart–Tijdeman's construction gives $\exp\{(4+o(1))(s/\log s)^{1/2}\}$
solutions and nobody expects much more. **The whole of Erdős #126 is inside the
gap between what is proved about $N(r)$ and what is believed.** That is where a
proof program belongs, and it is not where the earlier brief's three lanes were
pointed.

Reproduce with `python3 hunts/support_f3ab3e34/probe.py` (3 s, stdlib only,
writes `results.json`).

---

## 1. The statement, and what is actually known

$S$ a set of $k$ primes; $A$ a finite set of distinct positive integers with
every off-diagonal $a+b$ having all prime factors in $S$; $g(k) = \max |A|$.
Equivalently $f(n) = \min_{|A|=n} \omega\!\left(\prod_{a \ne b}(a+b)\right)$ and
$f(n)/\log n \to \infty \iff g(k) = \exp(o(k))$. The inversion is `r_186989`'s
and it is correct; this arm keeps it.

| | statement | source |
|---|---|---|
| upper | $g(k) < 3\cdot 2^{k-1}$ | Erdős–Turán 1934 |
| upper | $g(k) \le 2^k$ | improvement reported in the Erdős–Surányi book |
| upper (two-set) | $\omega(\prod_{a\in A, b\in B}(a+b)) \ge c\log|A|$, $|A|\ge|B|\ge 2$, $c$ effective | Győry–Stewart–Tijdeman 1986 |
| lower (unit eqns) | $ax+by=1$ can have $\exp\{(4+o(1))(s/\log s)^{1/2}\}$ $S$-unit solutions | Erdős–Stewart–Tijdeman, *Compositio* **66** (1988) 37–56 |
| counting | $x+y=1$ in a rank-$r$ group has $\le 2^{8r+8}$ solutions | Beukers–Schlickewei 1996 |
| lower | $g(k) \ge (1+o(1))\,k\log k/2$ | §4 below, elementary |

Two corrections to the brief and to `r_186989`, which both quote $3\cdot2^{k-1}$
as the state of the art: (i) the standard bound quoted in the current literature
is $g(k) \le 2^k$, a factor $3/2$, not important, but it is what a referee will
say; (ii) the whole $\log$-scale content of the 1934 theorem was superseded in
1986 by Győry–Stewart–Tijdeman, whose two-set version gives the same $c \log |A|$
for a genuinely harder object. **Erdős #126 has been in the "$c\log n$, $c$ not
improvable by these methods" regime for forty years.** Any program that does not
say why it escapes $S$-unit counting is not a program.

*Provenance note.* The $2^k$ and the two 1986/1988 attributions come from
secondary sources located during this run (search summaries and
`arXiv:2602.07545`); `erdosproblems.com/126` returned HTTP 403 and was not read.
The Beukers–Schlickewei and Erdős–Stewart–Tijdeman statements are quoted as they
appear in those sources. Treat the four literature rows as *cited, not verified
at the source*. The mathematics in §2–§5 below does not depend on which of
$3\cdot2^{k-1}$ or $2^k$ is right.

## 2. The lemma I attacked, in full: the unit-equation reduction

**Lemma 1 (normalisation).** If $A$ is $S$-valid then $d = \gcd A$ is
$S$-smooth and $A/d$ is $S$-valid.
*Proof.* $d \mid a+b$ for any two elements, and $a+b$ is $S$-smooth, so every
prime factor of $d$ lies in $S$. Each $(a+b)/d$ divides $a+b$, hence is
$S$-smooth. $\square$

**Lemma 2 (the reduction).** Let $A$ be $S$-valid, $|S| = k$, $|A| = n \ge 3$.
Fix distinct $a_1, a_2 \in A$ and put $D = a_1 - a_2 \ne 0$. Let
$\Gamma = \langle -1,\, p_1, \dots, p_k,\, D\rangle \le \mathbb{Q}^{*}$, a
finitely generated group of rank $\le k+1$. Then the map

$$c \;\longmapsto\; (X_c, Y_c) = \Big(\tfrac{a_1+c}{D},\; -\tfrac{a_2+c}{D}\Big)$$

is an injection from $A \setminus \{a_1,a_2\}$ into
$\{(X,Y) \in \Gamma^2 : X + Y = 1\}$.

*Proof.* For $c \notin \{a_1,a_2\}$ both $a_1+c$ and $a_2+c$ are off-diagonal
sums, hence positive $S$-smooth integers, hence elements of $\Gamma$; $D^{-1}$
and $-1$ are in $\Gamma$, so $X_c, Y_c \in \Gamma$. And
$X_c + Y_c = \big((a_1+c)-(a_2+c)\big)/D = D/D = 1$. Injectivity: $X_c$
determines $a_1 + c$ and hence $c$. $\square$

**Corollary.** $g(k) \le 2 + N(k+1)$ with $N$ as in the headline, and
unconditionally $g(k) \le 2 + 2^{8k+16}$.

Checked as exact rationals on the witness $A = \{1,2,3,5,7,13\}$,
$S = \{2,3,5,7\}$: all four solutions lie in the group, all sum to 1, all
distinct (`results.json`, `checks.unit_equation_reduction`).

**What this is and is not.** It is not new: this is essentially how the
$c\log|A|$ bounds are proved, and the constant it yields ($2^{8k}$) is far worse
than $2^k$. Its value is that it is *sharp about where the difficulty lives*:
Erdős #126 is implied by a subexponential count for the unit equation, and the
best known count is exponential in exactly the same way the 1934 bound is. The
two walls are the same wall. Any lane that does not attack it is not attacking
#126.

**Direction check.** The implication runs one way only. A *lower* bound on
$N(r)$, namely Erdős–Stewart–Tijdeman's $\exp\{(4+o(1))(s/\log s)^{1/2}\}$, says
nothing against #126, because their many solutions arise from an equation
$ax+by=1$ with no set $A$ behind it: the reduction consumes only the sums
$a_1+c$ and $a_2+c$, and inverting it would require the remaining
$\binom{n-2}{2}$ sums to be smooth as well. So this route cannot accidentally
refute. Note however that their construction lands in exactly the *twisted*
equation the reduction produces, so it is the relevant lower bound, and it is
$\exp(o(s))$: **the believed truth about $N$ already implies #126, with room to
spare** ($g(k) \le \exp(O(\sqrt{k/\log k}))$ would follow).

## 3. Candidate chains, ranked by the strength of the first unproved step

Ranking is by *how much more than #126 the first step asks for*. Weakest ask
first; that is the opposite of "most likely to finish".

| # | chain | first unproved step | strength of that step | reaches #126? |
|---|---|---|---|---|
| C | **descent with a saving.** Reconstruct the $g(k)\le 2g(k-1)$ induction, show its dichotomy cannot be tight at both branches, get $g(k) \le (2-\delta)^k$. | any $\delta > 0$ | **weaker** than #126 | **no**, any fixed base is still $\exp(\Theta(k))$. Publishable progress, not a program. |
| B | **simultaneous unit equations.** Fix $m$ base points $a_1..a_m$; each other $c$ solves $m-1$ twisted unit equations at once. Show the *system* has $\exp(o(k))$ common solutions. | subexponential count for a constrained system | weaker than A, still stronger than #126 | **yes** |
| A | **the reduction of §2.** | $N(r) = \exp(o(r))$, i.e. beat Beukers–Schlickewei from $2^{8r}$ to subexponential | strictly stronger than #126 | **yes**, immediately |
| D | **height normalisation.** Every extremal $A$ can be normalised into $[1,H(k)]$ with $H(k)=\exp(o(k))$; then enumerate. | effective bound of subexponential height | far stronger; current effective theory (Baker/Győry–Yu) gives $\exp\exp(ck\log k)$ | yes, but blocked at the first step by two exponentials |
| E | **composition / supermultiplicativity.** | a gadget $g(k_1+k_2)\ge g(k_1)g(k_2)$ | n/a | **refutes**, see §5 |

**Recommendation: B, with C as the cheap parallel bet.** B is the only chain
whose first step is both sufficient and not already a famous open problem in its
own right. Its content is that the extra base points are free constraints that
no existing counting argument uses: every known bound for the system factors
through the single-equation bound and therefore inherits the rank-exponential
subspace count. Whether the constraints can be made to bite is, as far as this
run can tell, unexamined. C is worth a separate short run because its
deliverable ("$g(k) \le 1.9^k$") is checkable, self-contained, and the brief
names a smaller exponential base as progress, while being honest that it can
never converge to the conjecture.

**Not recommended: A and D.** Both replace #126 with a harder problem. A run
that "attacks A" is a run attacking the unit-equation count, which should be
briefed as such and not as a ζ-lab-scale hunt.

## 4. Audit of `r_186989`

Reproduced and read against its own data. Three findings.

**4a. Its table replicates, and its universes were more slack than it said.**
Independent branch-and-bound at $N = 200..400$ recovers
$g_N(k) = 2,4,5,6,8,10$ for $k=1..6$ with the same witnesses at $k \le 4$,
i.e. the boxes it used ($6\,000$–$200\,000$) were $10^2$–$10^3$ times larger
than needed, not $60\times$. Its conclusion ("the box is not what binds") is
right and understated.

**4b. Its loose thread 3 is false, and its own witness refutes it.** The thread
proposes proving $|A| \le p-1$ when $p \notin S$ "by pigeonhole on residues mod
$p$ against the pairing $r \leftrightarrow -r$". The pigeonhole does not close:
for odd $p$, two elements in the *same* residue class $r$ have sum $2r \not\equiv 0$,
so a class may be occupied arbitrarily often and the number of *elements* is
unconstrained. $p=2$ is special precisely because $2r \equiv 0$ always. Explicit
counterexample, taken from the hunt's own arm-2 table: $A=\{1,3,7,13\}$ with
$S=\{2,5,7\}$ has no sum divisible by 3, and $|A| = 4 > 3-1$. The correct
residual statement is the one already proved there: **$2 \notin S \Rightarrow
|A| \le 2$**, and it does not generalise to any odd prime. Searches with $3
\notin S$ give $g_N = 4,5,5,6$ for $|S| = 3,4,5,6$, growing normally.

**4c. It reports no lower-bound construction, and the trivial one beats its
table.** $A = \{1,\dots,m\}$ is $S$-valid for $S = \{p \le 2m-1\}$, so
$g(\pi(2m-1)) \ge m$ and $g(k) \ge (1+o(1))\,k\log k/2$. Verified for
$m \le 40$: $g(8) \ge 11$, $g(12) \ge 20$, $g(22) \ge 40$. The hunt's largest
measured value is $g(7)\ge 11$. So $g$ is known to grow at least like
$k \log k$, which reframes its §5: the sequence $g_N(k)^{1/k}$ falling to 1.41
over seven points is not evidence about the limit in either direction, and the
open question is not "is $g$ small" but "is $g$ subexponential" in a range
$[k\log k, 2^k]$ that is entirely unexplored by search.

**What survives the audit intact:** the $f \leftrightarrow g$ inversion, the
$f(n-1) \le f_0(n) \le f(n)$ argument for the Formal Conjectures mismatch, the
composition-law refutation direction (§5), and the parity fact.

## 5. Routes that point at refutation

1. **Composition/supermultiplicativity**, `r_186989`'s arm 3, confirmed:
   $g(1)=2$ plus $g(k_1+k_2)\ge g(k_1)g(k_2)$ gives $g(k)\ge 2^k$ by Fekete,
   which refutes. Sound as stated.
2. **Transferring Erdős–Stewart–Tijdeman.** Their construction produces
   $\exp\{(4+o(1))(s/\log s)^{1/2}\}$ solutions of a twisted unit equation. That
   is $\exp(o(s))$, so even a perfect transfer to a set $A$ would *not* refute
   #126: it would confirm it while showing $g$ is superpolynomial. A refutation
   needs a construction with $\log |A| \gg k$, and the only known family of that
   shape would have to beat the unit-equation record by an exponential. Worth
   saying plainly: **the constructive side has been trying since 1988 and the
   record is subexponential**, which is soft evidence *for* #126.
3. Any "structure theorem" whose output is a semigroup or product structure on
   valid sets is in class 1 and should be treated as a refutation attempt.

## 6. What this run could not settle

- **No new upper bound.** $g(k) \le 2 + 2^{8k+16}$ is proved here and is worse
  than 1934. Nothing in this run improves $2^k$.
- **The $2^k$ proof was not reconstructed.** Chain C's first step needs it, and
  45 minutes was not enough to rederive the Erdős–Surányi induction from
  scratch. This is the single cheapest missing input: get the book's proof, or a
  paper that reproduces it, before funding C.
- **Whether Lemma 2 is stated somewhere in the literature.** It is almost
  certainly folklore inside the Győry–Stewart–Tijdeman method; this run did not
  find it written down, and did not search hard.
- **Chain B's first step was not attacked**, only identified. It is the
  recommendation, not a result.

## The doors

This run measured no ceiling of its own, but it re-ranks the doors of the
family `r_186989` measured.

**1. Active constraints.** What binds is not the search box, the choice of $S$,
or $k_{\max}$. The audit in §4a shows all three are slack by orders of
magnitude. What binds is the *counting theorem*: every route to an upper bound on
$g$ known to this run passes through a solution count for the unit equation, and
every such count is $\exp(\Theta(\mathrm{rank}))$. Shadow price is total: an
$\exp(o(r))$ count buys the whole conjecture, and nothing else buys anything.

**2. Frozen-constant inventory.**

| Frozen | Value | What relaxing it trades |
|---|---|---|
| number of base points in the reduction | $m = 2$ | Going to $m = 3, 4, \dots$ costs at most $m-2$ further generators (the differences $D_{1j}$) and adds $m-1$ simultaneous equations. **This is the door with real trade shape**, and it is chain B. |
| the group in Lemma 2 | $\langle -1, S, D\rangle$, rank $\le k+1$ | Choosing $a_1,a_2$ with $S$-smooth difference drops it to $k$; worth $2^{8}$ and nothing structural. |
| the counting theorem | Beukers–Schlickewei $2^{8r+8}$ | The only door that reaches the conjecture, and it is not ours. |
| $\{1..m\}$ as the lower-bound construction | intervals | Any construction with $\log|A| \gg k\log k$ would be new information about the true growth; the search side has never looked above $k=7$. |

**3. Information class.** Enumeration over $[1,N]$, everything `r_186989` did
and everything this arm re-ran, stays inside the data "which integers have
smooth pairwise sums", and provably cannot produce an upper bound on $g(k)$. The
doors that move #126 all require reading the $S$-unit literature and its
counting technology. The recommended door (chain B, more base points) is the one
door in that class whose first step is *weaker* than the famous open problem,
and it is reachable with the same reduction proved in §2.
