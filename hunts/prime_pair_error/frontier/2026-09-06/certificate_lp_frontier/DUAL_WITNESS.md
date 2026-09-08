# Exact dual witnesses for the attainable-quotient floor T*(y, N)

**Session 2026-09-07 (continuation). Input: main `880ec07`.** Scope: the
attainable-quotient problem T* of `hunts/quotient_certificate/RESULTS.md`
(PR #203), kept separate from the all-cell problem V*. Grade of the two
values in Section 2: enclosure-carrying (exact rational identities plus
interval arithmetic on finitely many log p), and confirmed by an independent
route (Codex's rational primal certificates are upper bounds that agree to
every printed digit). Everything in Sections 3 and 4 is a lower bound only
where it says so, and a negative result where it says so. Nothing here is a
theorem about growth in N.

Notation. Q_N = {floor(N/d) : 2 <= d <= N}; A[q, j] = floor(q/j) for q in Q_N,
j <= y; L_j = log floor(N/j)!; m_q = sum_{d : floor(N/d) = q} Lambda(d) is
the prime-power mass landing in cell q. The dual of T* is

    maximize sum_q nu_q   s.t.   sum_q nu_q floor(q/j) = L_j (j <= y),  nu >= 0,

m is feasible with value psi(N), and any feasible nu certifies
T*(y, N) - psi(N) >= sum_q nu_q - psi(N) (BARRIER.md Lemma 1 on Q_N).

## 1. Basic witnesses are bases, and their gains are the tight certificate's elevations

**Scope correction (2026-09-07, coordinator).** The first version of this
section said "every witness is a basis". That is too strong. A feasible
dual measure need not be a vertex: mixtures of feasible measures are
feasible, and the general feasible set is the polytope {nu >= 0 : A^T nu = L}
whose vertices are the basic solutions below. What follows describes the
basic (vertex) witnesses; Section 6 gives a non-basic construction.

Take y cells S with A_S (the y x y matrix (floor(s/j))_{s in S, j <= y})
invertible. The mass of any cell q is redistributed onto S by the exact
rational rates

    r^{(q)} = (A_S^T)^{-1} A[q, :],     i.e.  sum_{s in S} r^{(q)}_s floor(s/j) = floor(q/j)  for all j <= y,

which preserve every moment, and its gain per unit mass is

    1^T r^{(q)} - 1 = W_c(q) - 1,    c = A_S^{-1} 1,

because c^T A[q, :] = 1^T A_S^{-1} A[q, :] = 1^T r^{(q)}: the primal certificate
that is tight on S. So the dual witness for a basis S is nu = sum_q m_q r^{(q)},
its gain is sum_q m_q (W_c(q) - 1), and it is a valid lower bound exactly when
nu >= 0 on S; if in addition W_c >= 1 on Q_N the same basis gives the upper
bound and T* - psi(N) = sum_q m_q (W_c(q) - 1) exactly. This is complementary
slackness written out; its use here is that it turns "validate a witness"
into two finite checks with exact arithmetic.

Exactness. L_j = sum_p log(p) l^{(p)}_j with integers
l^{(p)}_j = sum_{k >= 1} floor(N/(p^k j)), so nu^{(p)} = (A_S^T)^{-1} l^{(p)} is a
rational vector for each prime p, nu_s = sum_p log(p) nu^{(p)}_s, and the gain
is G = sum_p log(p) s_p with rational s_p = 1^T nu^{(p)} - #{k : p^k <= N}.
The moment identities A_S^T nu^{(p)} = l^{(p)} are checked as exact rational
equalities for every p; the signs of nu_s and the value of G are decided by
interval arithmetic (mpmath.iv at 60 digits) on the finitely many log p.
"Logarithmic right-hand sides" are never rationalized.

`dual_witness.py` does all of this from the basis of a floating dual
simplex vertex, and refuses to report unless the identities hold exactly.

## 2. The two witnesses

| (N, y) | cells | primes | basis = support | moments exact | min lower endpoint of nu on S | tight c feasible on Q_N | T*(y,N) - psi(N) |
|---|---:|---:|---|---|---:|---|---|
| (1000, 31) | 61 | 168 | yes (31 cells) | all 168 p | 3.13e-3 | yes | 41.28216944295939183072469479673415632655762... (width 6e-59) |
| (10^4, 100) | 198 | 1229 | yes (100 cells) | all 1229 p | 6.12e-4 | yes | 226.83268961232150239965751760227398067618... (width 5e-58) |

Both are exact optima: the dual witness (lower bound) and the tight primal
certificate (upper bound) come from the same basis and both verify. Codex's
rational primal certificates (PR #203) gave 41.28216944 and 226.83268961 as
upper bounds; they agree with these values to every digit they print.

Files: `results/dual_witness_N1000_y31.json`, `results/dual_witness_N10000_y100.json`
(basis, exact primal c, per-cell exchange rates and gains as fractions, the
nonzero s_p, the gain interval). Primal c at (1000, 31): c = mu on 1..6,
then c_7 = -22/37, c_8 = -15/37, c_10 = 1, c_11 = -11/74, ... , c_31 = 9/74;
every gain per unit has denominator 74 (the basis determinant), at
(10^4, 100) denominator 8.

## 3. Which cells exchange mass, and why the moments do not move

(1000, 31): 18 cells are emptied, {7, 11, 13, 14, 18, 20, 23, 31} below y and
{32, 34, 52, 62, 111, 125, 142, 200, 250, 333} above, at gains W_c(q) - 1 =
15/37, 63/74, 79/74, 21/74, 35/74, 67/37, 63/74, 83/74 (below) and 83/74,
22/37, 11/74, 39/37, 39/74, 39/74, 57/74, 141/74, 17/37, 1/37 (above). The
largest contributions are cell 7 (the primes 127..139, 8.2 of the 41.3),
then cells 13, 32, 11, 20, 23, 200 (3.1 to 4.6 each). The basis has 22 cells
carrying real mass and 9 carrying none: {26, 28, 30, 35, 38, 66, 71, 100,
166}, all of the form floor(N/d) with every d in the interval composite. The
fake prime measure puts mass there.

(10^4, 100): 40 cells emptied (23 below y, 17 above; three of them, 20, 23
and 120, at gain exactly 0, so the vertex is degenerate but the basis is
still the support), 41 of the 100 basis cells carry no real mass (16 below
y: 40, 46, 48, 56, 58, 60, 65, 70, 77, 84, 92, 94, 95, 96, 98, 100). The
emptied cells above y are exactly the cells of d = 97, 89, 83, 71, 67, 49,
43, 31, 27, 23, 19, 13, 9, 8, 5, 3, 2.

The pattern, in words: the optimal fake measure removes the mass of prime
powers d from their cells floor(N/d) and places it on attainable cells whose
d are composite, at rates fixed by the basis; the moments are unchanged
because each rate vector solves sum_s r_s floor(s/j) = floor(q/j) for all
j <= y, which is a statement about integer division only. The rates are
dense: a unit at cell 333 is spread over all 31 basis cells with coefficients
k/37 of both signs. There is no local three- or five-cell relation behind the
optimum; the gains, not the rates, are the local quantity.

## 4. The explicit family that fails: the Mobius prefix

The one basis with a closed form is S0 = {1, ..., y} (all attainable for
y <= sqrt(N) - 1). A_{S0} is unitriangular, c = mu_{<= y}, and for q > y

    R_q(t) = sum_{k <= y/t} mu(k) floor(q/(t k)),   r^{(q)}_s = R_q(s) - R_q(s+1),   R_q(y+1) = 0,

R_q(t) being the number of multiples of t up to q whose cofactor has no
divisor in [2, y/t]. `prefix_witness.py` checks these closed-form rates
against the exact basis solve for every cell at both sizes: equal. Moving all
mass gives the explicit measure nu_s = N(s) - N(s+1) with
N(t) = sum_{k <= y/t} mu(k) log floor(N/(t k))!, so **the full prefix
transfer is feasible exactly when t -> N(t) is nonincreasing on [1, y]**, and
its gain is B_mu(N) - psi(N) = sum_{q > y} m_q (W_mu(q) - 1). Fractional
transfer theta_q in [0, 1] is a small LP; its rationalized optimum is
re-verified exactly (moments) and by enclosure (signs).

Result: this family certifies almost nothing.

| (N, y) | cells above y with mass | full transfer gain | min nu (full) | positive-gain cells | theta-LP gain | T* - psi |
|---|---:|---:|---:|---:|---:|---:|
| (1000, 31) | 17 | -150.2 | -68.4 | 0 of 17 | 0 | 41.28 |
| (10^4, 100) | 35 | +1120.7 | -390.9 | 35 of 35 | 8.155 (one cell, 169 = floor(N/59)) | 226.83 |

At (1000, 31) M1(31) < 0, so W_mu(q) < 1 on every mass-carrying cell above
y and no move gains; at (10^4, 100) M1(100) > 0, every cell gains under mu
and the unconstrained transfer would exceed the true optimum five times over,
but nonnegativity on S0 (the drains at small s, where R_q(s) - R_q(s+1) is
large and negative) admits one cell. So "the Mobius prefix carries the
barrier" fails at these two instances. **Scope correction (2026-09-07,
coordinator):** this is a finite statement about (1000, 31) and (10^4, 100);
it is not an asymptotic exclusion of prefix-type witnesses, and it says
nothing about other supports or cutoffs. Section 6 shows what this family
missed: it only withdrew mass from cells above y, and the sign it did not
use is the productive one.

The three-cell relation R_q - R_{q-1} = R_1 for a y-rough q (the rough spike
in T* form: remove theta <= m_q from q, add it to q-1 and 1, gain theta)
needs q y-rough with real mass and q-1 attainable. **Correction
(coordinator, 2026-09-07):** an earlier version said this vanishes at
y = sqrt(N) because it looked only below sqrt(N). Consecutive attainable
cells exist above sqrt(N): at (10^4, 100) both 102 = floor(N/98) and
103 = floor(N/97) are attainable, 103 is prime, R_103 - R_102 = e_1 = R_1,
and log(97) (e_1 + e_102 - e_103) is feasible with gain log 97 = 4.5747.
The actual restriction is the attainability of q-1, which above sqrt(N)
holds only where consecutive quotients floor(N/d), floor(N/(d-1)) differ by
one; Section 8 evaluates the family so defined.

## 5. What is established, what is refuted, what remains

Established (enclosure-carrying): the two exact values in Section 2, with
every moment identity exact and every sign enclosed; they equal Codex's
primal upper bounds, so T*(31, 1000) and T*(100, 10^4) are known exactly.

Established (elementary): Section 1, the basis characterization; Section 4,
the closed-form rates and the monotonicity criterion for the prefix family.

Refuted: that the Mobius-prefix basis (equivalently, moving mass onto the
cells where c = mu is tight) certifies a positive proportion of T* - psi at
these sizes; it certifies 0 and 3.6%.

Not established: any witness family valid for all N with gain of order
N/sqrt(y), or any lower bound on T*(y, N) - psi(N) beyond the finite values
above. The exponent 3/4 measured in RESULTS.md 4.6 remains a conjecture, and
nothing here extends it to supports other than y = sqrt(N). The obstacle is
now precise: a witness is a basis; the optimal bases at these sizes contain
9 of 31 and 41 of 100 mass-free composite cells, chosen by the simplex, and
no rule producing such bases for general (N, y) is in hand. A proof of the
barrier for T* needs that rule (or a dual object not tied to a basis, such
as a measure-valued construction whose moment identities hold by an
arithmetic identity rather than by solving a linear system). No such object
was found in this session.

## 6. A tractable non-basic construction: exchanges through the prefix

**The rule, as a perturbation.** Rows R_1, ..., R_y are unitriangular, so
every attainable q > y has the unique expansion R_q = sum_{s <= y} r^{(q)}_s R_s
with the integer rates of Section 4, r^{(q)}_s = R_q(s) - R_q(s+1). Put

    z_q = e_q - sum_{s<=y} r^{(q)}_s e_s          (a measure on Q_N, q > y).

**Lemma 6.** A^T z_q = 0 and 1^T z_q = 1 - W_mu(q). The zero-moment measures
on Q_N are exactly the linear span of {z_q : q in Q_N, q > y}.

*Proof.* A^T z_q = R_q - sum_s r^{(q)}_s R_s = 0 by the expansion, and
1^T z_q = 1 - sum_s r^{(q)}_s = 1 - R_q(1) = 1 - W_mu(q). If delta has zero
moments, delta' = delta - sum_{q>y} delta_q z_q is supported on {1..y} with
zero moments, hence zero by unitriangularity. QED.

(The two-sided LP over the z_q, theta_q >= -m_q, reproduces 41.282169 and
226.832690 at the two sizes, `fake_mass_witness.py`: the numerical check
of the lemma.)

**Construction A (additions).** delta = sum_{q in Q+} theta_q z_q with
theta_q >= 0 and Q+ = {q > y : W_mu(q) < 1}. Support Q_N, A^T delta = 0,
gain sum_q theta_q (1 - W_mu(q)) (exact rational), and

    m + delta >= 0   iff   sum_q theta_q r^{(q)}_s <= m_s  for every s <= y.

It creates mass at q, which may carry no real prime power, by withdrawing
theta_q r^{(q)}_s from the prefix cells. Its exact failure: the withdrawals
land on the cells s in (y/2, y], where r^{(q)}_s = floor(q/s) - floor(q/(s+1))
is 0 or 1 and the real mass m_s is the Lambda-mass of one interval of length
N/s^2 in [1, 4], i.e. a single log p or nothing. At (1000, 31) the best
single cell is q = 40 (W_mu = -3), bound by s = 31 with m_31 = log 2 (the
prime power 32), gain 4 log 2 = 2.7726; the additions LP over all 29 cells of
Q+ certifies exactly that; the constant-parameter version theta_q = t on
Q+ ∩ (y, Y] has t_max = 0 for every Y because prefix cell 17 (d in {56, 57,
58}, all composite) has m_17 = 0 and a positive total drain. At (10^4, 100)
Q+ is empty (M1(100) > 0 makes W_mu(q) >= 1 on every cell above y), so A
certifies 0. Conversely Section 4's withdrawal family is empty at (1000, 31)
and certifies 8.16 at (10^4, 100). The sign of M1(y) decides which one-sided
family exists, and both are capped by the top of the prefix.

**Construction B (exchange a -> prefix -> b).** For a cell a > y with real
mass and any cell b > y, b != a,

    delta = theta_b z_b - theta_a z_a,   0 <= theta_a <= m_a,  theta_b >= 0.

Support Q_N and A^T delta = 0 by Lemma 6;

    m + delta >= 0   iff   m_s + theta_a r^{(a)}_s - theta_b r^{(b)}_s >= 0  for every s <= y
                          (and theta_a <= m_a, which is the condition at a);
    gain = theta_b (1 - W_mu(b)) - theta_a (1 - W_mu(a)).

For the equal-mass exchange theta_a = theta_b = theta this reads

    delta = theta (e_b - e_a) + theta sum_s (r^{(a)}_s - r^{(b)}_s) e_s,
    gain  = theta (W_mu(a) - W_mu(b)),
    feasible iff theta <= m_a and m_s >= theta (r^{(b)}_s - r^{(a)}_s) for all s <= y.

At the top of the prefix, s in (y/2, y], the rate r^{(q)}_s = floor(q/s)
- floor(q/(s+1)) = #{k >= 1 : floor(q/k) = s} is the multiplicity of s
among the quotients of q. **Correction (coordinator, 2026-09-07):** an
earlier version of this paragraph called these rates 0/1 step indicators.
They are counts: they are 0 or 1 only for q < s(s+1), and at (10^4, 100),
q = 5000, s = 51 the rate is 98 - 96 = 2. The implementation always used the
integer rates, so no saved witness is affected; only the explanation was
wrong. The condition at the top is therefore: for every s in (y/2, y],
m_s >= theta (r^{(b)}_s - r^{(a)}_s) with the full multiplicities. Below y/2
the masses are of order N/s^2 and the rates are the Mobius-weighted counts
of Section 4; there the condition is a finite inequality that holds for
theta up to a multiple of m_a in every case computed here.

**Gains established (exact rationals, every touched cell checked by
enclosure, moments checked as exact identities).** Pairs are chosen
greedily, each step's amounts rationalized to 10^-6 and shrunk until the
accumulated delta is feasible; the sum of the steps is a single witness.

| (N, y) | steps | gain established | T* - psi | fraction | first three exchanges (a -> b, gain) |
|---|---:|---:|---:|---:|---|
| (1000, 31) | 10 | 30981661/10^6 = 30.9817 | 41.2822 | 0.75 | 32 -> 166 (fake), 8.25; 62 -> 40, 3.47; 34 -> 35 (fake), 3.37 |
| (10^4, 100) | 25 | 26545907/200000 = 132.7295 | 226.8327 | 0.585 | 232 -> 102 (fake), 18.81; 112 -> 123, 13.47; 140 -> 126, 12.79 |

Files: `results/fake_mass_N1000_y31.json`, `results/fake_mass_N10000_y100.json`
(all pairs with positive gain, the greedy sequence, the exact amounts).

**What it explains about the saved optima.** Mass flows from cells where the
Mobius certificate W_mu is high to cells where it is low, and the prefix pays
the rate difference. At (10^4, 100) the seventeen emptied cells above y have
W_mu = 4, 6, 5, 6, 2, 9, 8, 10, 10, 12, 20, 26, 34, 39, 64, 106, 153 and the
twenty-five fake-only basis cells above y have W_mu = 1 .. 15; the first
greedy exchange, 232 -> 102, moves log 43 from W_mu = 8 to W_mu = 3. At
(1000, 31) every fake-only cell above y has W_mu <= -2 (35, 38: -2; 66, 71:
-3; 100: -6; 166: -9) and the prime cells above y are the only sources, so
the optimum empties them although W_mu < 1 there too: the removal is the
refill of the top prefix cells (r^{(a)}_s >= 0 for s > y/2) that funds the
additions. The mediating cells are the prefix's top, whose real masses are
single logarithms or zero, and those walls are what the exact optimum
balances with its dense rates; the greedy exchange respects the same walls
one pair at a time and reaches three quarters and three fifths of the
optimum with ten and twenty-five pairs.

**Limits, stated.** These are lower bounds at two instances. The greedy
choice is not claimed optimal; the fraction reached is measured, not
predicted; the number of steps was capped at 25; nothing extends to other
N, other supports, or a growth rate. What is proved is Lemma 6 and the
feasibility criteria displayed, which make any chosen family of exchanges
a checkable witness.

## 8. One prescribed family: halving folds, and exactly where it fails

**The formula.** For a real-mass attainable cell a > y let q = floor(a/2) =
floor(N/(2d)), attainable. Since floor(a/j) - 2 floor(q/j) = floor(a/j) mod 2,
define the integer vectors

    kappa_i(a) = T_i(a) - T_{i+1}(a),   T_i(a) = sum_{m <= y/i} mu(m) (floor(a/(im)) mod 2),   T_{y+1} = 0,
    g(a)       = 1 + sum_{j <= y} mu(j) (floor(a/j) mod 2)  =  1 + W_mu(a) - 2 W_mu(q),

and the measure on Q_N

    Fold(a) = -e_a + 2 e_q + sum_{i <= y} kappa_i(a) e_i.

**Lemma 7.** A^T Fold(a) = 0 and 1^T Fold(a) = g(a).

*Proof.* The moment vector of -e_a + 2 e_q is -(floor(a/j) mod 2)_j; the
prefix measure sum_j v_j rho_j with rho_j = sum_{i | j} mu(j/i)(e_i - e_{i-1})
has moment vector v (Section 6), and collecting its coefficient on cell i
gives sum_{j : i | j} v_j mu(j/i) - sum_{j : (i+1) | j} v_j mu(j/(i+1))
= T_i - T_{i+1} = kappa_i for v_j = floor(a/j) mod 2. The mass of
sum_j v_j rho_j is sum_j v_j mu(j), so 1^T Fold(a) = -1 + 2 + sum_j mu(j)
v_j = g(a). QED. (Checked as an exact integer identity for every source at
the three sizes below.)

**The rule.** With the prescribed source set A = {a > y : m_a > 0, g(a) > 0}
and one parameter t in [0, 1],

    D(t) = t sum_{a in A} m_a Fold(a).

Support: the cells a, floor(a/2) and 1..y, all attainable (the prefix must be
attainable, which holds at the three sizes). A^T D(t) = 0 by Lemma 7. Net
capacity on a cell c, with every multiplicity retained:

    m_c + t Delta_c >= 0,
    Delta_c = -m_c [c in A] + 2 sum_{a in A : floor(a/2) = c} m_a + [c <= y] sum_{a in A} m_a kappa_c(a).

Hence D(t) is feasible iff t <= t* := min over cells with Delta_c < 0 of
m_c / (-Delta_c) (and t <= 1), and its gain is

    G(t) = t Gamma,   Gamma = sum_{a in A} m_a g(a) = sum_{a in A} m_a (1 + W_mu(a) - 2 W_mu(floor(a/2))).

The drift a M1(y) cancels in g(a); what remains is a Mobius sum over the j
with odd quotient floor(a/j), of size comparable to sqrt(y) at each source,
so Gamma is of the order psi(N/y) sqrt(y) = N/sqrt(y) when t* is of order one.

**Conditional lemma.** If every cell c with Delta_c < 0 has m_c > 0, then
t* > 0 and T*(y, N) - psi(N) >= t* Gamma. The hypothesis is the wall
condition: no cell of Z = {c : m_c = 0} is drained by D. It is not a
statement about prime density; it is an arithmetic condition on the parity
profiles (floor(a/i) mod 2)_{i <= y} of the sources against the set of
zero-mass prefix cells, which is where Codex's capacity analysis enters.

**Exact failure at the tested sizes.** The wall condition fails, and it fails
at every source separately:

| (N, y) | sources with g > 0 | Gamma | zero-mass prefix cells | t* (F1, all) | binding cell | sources feasible alone | their joint gain (F5) |
|---|---:|---:|---:|---:|---:|---|---:|
| (1000, 31) | 5 (500, 250, 200, 142, 76) | 15.59 | 8 of 31: {17, 19, 22, 25, 26, 28, 29, 30} | 0 | 19 (mass 0) | none (each drains 17, 19 or 25) | 0 |
| (10^4, 100) | 28 | 248.92 | 36 of 100 | 0 | 33 (mass 0) | 169 (g = 2, log 59), 204 (g = 4, log 7) | 15.9387 |
| (3600, 60), holdout | 13 | 72.79 | 17 of 60 | 0 | 30 (mass 0) | 61 (g = 1, log 59), 133 (g = 1, log 3) | 5.1761 |

At the top of the prefix kappa_i(a) is the parity difference
(floor(a/i) mod 2) - (floor(a/(i+1)) mod 2) in {-1, 0, 1}, one third of
the top cells are walls (36 of 100 at N = 10^4), and a source's parity
profile meets a wall with a -1 almost surely; the restrictions F3 (sources
above 2y+1) and F4 (sources in (y, 2y+1], the withdrawals of Section 4)
have t* = 0 for the same reason. Gamma at (10^4, 100) exceeds the exact
optimum 226.83, which is consistent: it is the gain the family would have
if the walls did not exist. The F5 witnesses (15.9387 and 5.1761) are exact
(moments as integer identities, capacities by enclosure at t = 1), and they
are the whole positive content of the family at these sizes.

**A drain-free family (Family R).** For a > y y-rough with real mass and a-1
attainable, R_a - R_{a-1} = e_1 = R_1 (a has no divisor in [2, y]; if y+1 is
prime and divides a the cell y is also touched, which does not occur here),
so Shift(a) = e_1 + e_{a-1} - e_a has zero moments and mass 1, and

    D_R(t) = t sum_{a in Rough} m_a Shift(a),  Rough = {a > y : m_a > 0, a y-rough, a-1 in Q_N},

is feasible for every t in [0, 1] with no condition at all (the only cell
that loses is the source, by t m_a <= m_a), with gain t sum_{a in Rough} m_a.
This is proved, unconditionally. Its values: 0 at (1000, 31) (no such cell),
log 97 = 4.5747 at (10^4, 100) (a = 103), 9.9937 at (3600, 60) (a = 61, 67,
73). Small, but it is the only family here whose gain formula needs no
assumption.

**What this settles and what it hands over.** The prescribed fold rule is
correct (Lemma 7), explicit, and fails at the tested sizes for one exact
reason, the walls. So the question a capacity analysis has to answer is
not the size of the prime mass in the prefix cells but its zeros: the
density and placement of the wall set Z in (y/2, y] and whether a source
set with a prescribed arithmetic shape can have nonnegative parity drains on
all of Z. Nothing here proves or refutes the barrier; the exact optima
(Section 2) show that feasible witnesses of the right size exist, and the
greedy exchanges (Section 6) show how they route around the walls one
pair at a time.

## 9. Compensated folds: the coordinator's bundle, the band lemma, and a prescribed repair rule

**The bundle, verified.** At (1000, 31), D = Fold(76) + 2 Fold(200) + Fold(333)
(`compensated_fold.py --bundle 76:1,200:2,333:1`): support in Q_N, A^T D = 0
as integers, gains per unit 2, 4, 0, total 10 units. Withdrawn cells with
multiplicities: {2: 3, 3: 1, 5: 4, 7: 7, 9: 3, 11: 3, 12: 3, 14: 3, 16: 3,
20: 3, 23: 1, 27: 1, 76: 1, 200: 2, 333: 1}; every wall has D >= 0 (at 19:
-1 + 0 + 1, at 25: 1 - 2 + 1). With M_c the product of the prime bases of
the prime powers in cell c (so m_c = log M_c), the largest scale is
eps* = log(M_20)/3 = log(7)/3, and feasibility at every withdrawn cell is
the integer inequality M_c^3 >= 7^{d_c}, all of which hold (equality at
c = 20). Gain (10/3) log 7 = 6.486367163517711017... . Fold(333) has zero
gain and is the repair: it refills 17, 19, 22, 25, 30 and drains no wall.

**Lemma 8 (band structure of a fold at the top of the prefix).** For a
real-mass cell a > y and a prefix cell w with y/2 < w < y, w != floor(a/2),

    Fold(a)_w = sum_{k >= 1 : floor(a/k) = w} (-1)^{k+1},

and Fold(a)_y = floor(a/y) mod 2 (the last prefix rate is floor(q/y), not a
difference); the destination floor(a/2), if it lies in the range, carries an
additional +2. *Proof.* For w > y/2 the prefix rate of any q is
r^{(q)}_w = floor(q/w) - floor(q/(w+1)) = #{k : floor(q/k) = w}, and with
q = floor(a/2), floor(q/k) = floor(a/(2k)), so
Fold(a)_w = r^{(a)}_w - 2 r^{(q)}_w = #{k : floor(a/k) = w} - 2 #{k even : floor(a/k) = w}.
QED. Checked on every source and every such w at the three sizes (255, 1715,
725 cases, 0 violations). So for w > sqrt(a) a fold drains the wall w
exactly when the unique k with floor(a/k) = w is even, and refills it when
k is odd: the cells a in [kw, k(w+1)) with k odd are the refills of w. Below
y/2 the action is the full Mobius-weighted kappa_w(a) of Lemma 7.

**Rule C (band-matched repair), prescribed.** Start from the profitable
folds, coefficient 1 each (P = {a > y : m_a > 0, g(a) > 0}). Walk the walls
w in increasing order; at the first wall with D_w < 0, add the fold of the
real-mass cell r > y with Fold(r)_w > 0 chosen by the fixed key (drains no
wall, then largest g(r), then smallest r), with the integer multiplicity
ceil(-D_w / Fold(r)_w); repeat until no wall is negative or the chosen wall
has no untried refill, which is reported as the failure. The scale is
eps* = min over withdrawn cells of m_c / (-D_c) and the gain is
eps* (sum_P g(a) + sum_R c_r g(r)), the second sum being the repairs' gain
or sacrifice. Variant C0 uses the key "smallest r".

**Results.**

| (N, y) | walls (all cells with m = 0 below y) | Rule C0 | Rule C |
|---|---|---|---|
| (1000, 31) | 8, all in (y/2, y] | feasible; repairs 34x2, 58, 76x2, 250x2, 52x2, 125x2 with gains -2, -4, 2, 2, -2, -3: net 0 units | feasible; one repair, 333x2 (g = 0, drains no wall); 10 units, eps* = log(3)/2 bound at the repair itself, gain 5 log 3 = 5.4931 |
| (10^4, 100), 36 walls | fails at wall 33 (D = -2 left) | fails at wall 33 (D = -22 left) |
| (3600, 60), 17 walls | fails at wall 30 (D = -10 left) | fails at wall 30 (D = -4 left) |

At (1000, 31) Rule C reproduces the mechanism of the coordinator's bundle
with a different repair set (all five profitable sources plus 2 Fold(333))
and a slightly smaller gain, because its scale is set by the repair's own
mass (2 units withdrawn from cell 333, m = log 3) rather than by cell 20.

**Conditional Lemma 9.** Assume (W_top): every wall lies in (y/2, y].
Assume (R_clean): every wall w has a real-mass refill r_w > y with
Fold(r_w)_w >= 1 that drains no wall. Then Rule C closes every wall in at
most |Z| repair steps, its bundle is feasible with
eps* = min over withdrawn cells of m_c/(-D_c) > 0, and its gain is
eps* (sum_P g(a) + sum_w c_w g(r_w)) with c_w = ceil(-D_w / Fold(r_w)_w)
computed at the moment the wall is treated. *Proof.* A clean repair
increases no wall's deficit, so each wall is treated once and no new
deficit appears; feasibility on the mass cells holds for eps below the
stated minimum, and the gain is the total mass of the bundle times eps*
(Lemma 7). QED. The net withdrawal of the bundle at a mass cell c is
sum_{a in P} kappa_c(a) + sum_w c_w kappa_c(r_w) (plus -1 or -c_w at the
sources themselves), so eps* is the smallest of m_c over these totals; at
(1000, 31) that minimum is attained at the repair source.

**Exact failure, and the first unproved step.** (W_top) is false at
(10^4, 100) and at (3600, 60): the walls 33 and 30 lie at or below y/2,
where a fold's action is the Mobius-weighted parity sum
kappa_w = T_w - T_{w+1}, T_w = sum_{m <= y/w} mu(m) (floor(a/(wm)) mod 2)
(three terms at w = 33: parities at 33, 66, 99), which is negative for most
sources and for most repairs of other walls; the wall becomes a sink, its
deficit grows as other walls are repaired (11, 12, 25, 22 at N = 10^4), and
the finite supply of cells with kappa_33 > 0 is exhausted. A lower-half wall
is a prime-power-free interval (N/(w+1), N/w] of length about N/w^2 >= 4,
i.e. a prime gap of that size near N/w; such gaps exist for every N, so
(W_top) cannot be assumed in general, and the walls it fails at sit in a
band just below y/2. The first unproved step is therefore: **a supply bound
for lower-half walls**, an arithmetic statement that for each wall
w <= y/2 the real-mass cells r with kappa_w(r) > 0 outweigh, in the units of
Rule C, the drains that the profitable sources and the other repairs put on
w. That is a capacity question in Codex's lane; nothing here proves it, and
the failure above is the exact instance where it bites. Not promoted: the
labels 76, 200, 333 of the coordinator's bundle, and 333 as Rule C's
repair, are facts at one input.

## 10. The compensated bundle at (10^4, 100): why Rule C misses it, and the credit identity

**Verified.** With U = sum of the 28 profitable folds (each once, sum U = 91),

    D = 2U + 57 F_163 + 7 F_232 + 5 F_270 + 74 F_434 + 40 F_625
          + 22 F_1250 + 12 F_2500 + 4 F_5000

checks in my implementation (`compensated_fold.py --N 10000 --y 100`): support
in Q_N, all 100 moments zero as integers, every wall D_w >= 0, total gain
sum D = 615 units. With M_c the product of prime bases in cell c, the scale is
eps* = log(M_43)/146 = log(229)/146, binding UNIQUELY at cell 43, and every
negative coordinate satisfies M_c^{146} >= 229^{d_c} (equality only at 43).
Gain E >= (615/146) log 229 = 22.888623508122310848... . The binding cell 43
is a MASS cell (m_43 = log 229), not a wall: the ceiling is drift on the mass
cells, not wall closure.

**Why Rule C fails, precisely.** Cell 33 is a lower-half wall (33 < y/2 = 50)
with 2U_33 = -22. It has exactly 6 fold refills (kappa_33 > 0: cells 232, 434,
1250, 1428, 2000, 3333), each contributing only +1 per unit, and NONE is
clean: every one drains another wall. Five restrictions in Rule C each block
the bundle, and each must be relaxed:

1. **Seed multiplicity fixed at 1.** The feasible repair set lives at the
   doubled deficit; with a single seed the credits at cells 54, 62 are too
   small (see the identity below).
2. **One repair source per wall-visit.** Cell 33 needs +22 assembled from
   several of its six +1 refills at once; no single source supplies it while
   staying feasible elsewhere.
3. **The (r, w) "tried" set.** It forbids ever raising a source's coefficient
   or reusing it; the bundle puts 57 and 74 on single cells.
4. **The clean-first key.** It steers toward refills that drain no wall, but
   cell 33 has none, so Rule C can never even begin to fill it cleanly.
5. **Integer ceil per single wall instead of a joint solve.** A one-source
   fill of cell 33 with 22 units would drain 54 and 62 by 22; only a balanced
   multi-source block cancels those drains down to 2 and 4.

"No untried refill" is thus an algorithmic stopping condition, not an
impossibility: the bundle exists, Rule C's search shape cannot reach it.

**The grouped-cancellation identity.** The repair block
R = 57 F_163 + ... + 4 F_5000 is negative at exactly two walls:

    R_54 = -2 = -(2U)_54,     R_62 = -4 = -(2U)_62,     R >= 0 at every other wall.

So at 54 and 62 the repair spends the entire doubled-seed credit and the final
value is 0; these are the credits Codex was told to retain, and this is why
they cannot be discarded. Everywhere else R only adds to the walls. It follows
that the seed multiplier k = 2 is the UNIQUE feasible one for this R:

    k = 1:  (U + R)_54 = -1 < 0 and (U + R)_62 = -2 < 0    (under-credited);
    k = 2:  (2U + R)_w >= 0 for all 36 walls               (feasible);
    k >= 3: (3U + R)_33 = -33 + 22 = -11 < 0               (re-opens cell 33).

The repair block itself has zero moments and mass equal to the sum of its
gains, 433, so total gain 2(91) + 433 = 615, and the drift it deposits on the
mass cells is what cell 43 caps.

**Lemma 10 (seed-credit repair, sufficient).** Let U be the profitable-fold
seed, k a positive integer, and R a nonnegative integer combination of folds
of real-mass cells such that (i) (kU + R)_w >= 0 at every wall w, and (ii) k
is minimal for (i). Then D = kU + R is a feasible dual witness for T*(y, N)
with scale eps* = min over mass cells c with D_c < 0 of m_c/(-D_c) and gain
eps* (k sum_a g(a) [over profitable a] + mass R). *Proof.* Support in Q_N and
A^T D = 0 by Lemma 7 (each fold contributes both); at walls D >= 0 by (i); at
mass cells D + (1/eps*) m >= 0 by the definition of eps*; the gain is eps*
times the mass of D, which is k times the seed mass plus the mass of R by
Lemma 7. QED. This is a sufficient condition, applied to the actual bundle:
(i) holds with k = 2, (ii) is the k-uniqueness above, and the two facts
together certify E >= 22.8886... . It is not necessary (a witness may keep no
wall tight), and it does not by itself produce R.

**Parameter range proved, and the first remaining gap.** Proved at this input:
the bundle is feasible with the stated eps* and gain; k = 2 is minimal for
this R; the ceiling is a mass cell. The source labels 163, 232, 270, 434,
625, 1250, 2500, 5000 are NOT promoted to any other N. The gap Lemma 10 does
not fill is the existence of a wall-closing repair block R whose only wall
negatives are covered by kU: this is a nonnegative-integer transportation
feasibility whose supply side is the lower-half refills (the six kappa_33 > 0
cells and their analogues), and whether they can be combined to fill every
lower-half wall while their side-drains cancel to within the seed credit is
the capacity question in Codex's lane. Nothing here shows that supply is
sufficient or insufficient in general; at this finite input it IS sufficient,
by the exhibited R.

## 11. The 132.729535 witness in the signed fold basis: the excluded move is the un-fold

**The expansion.** The folds {Fold(a) : a in Q_N, a > y} are a basis of the
98-dimensional zero-moment space at (10^4, 100), because delta_a = -x_a +
2 sum_{b : floor(b/2) = a} x_b makes the coefficient map triangular. So the
prefix-exchange witness of Section 6 has a unique signed fold expansion,
solved by the descending recurrence the coordinator gave,

    x_q = 2 x_{2q} + 2 x_{2q+1} - delta_q,   q in Q_N, q > y   (missing indices 0).

`signed_fold.py` solves it from the witness's saved exact steps and checks
reconstruction at EVERY cell including the prefix: exact, and sum_a x_a g(a)
equals the witness gain 26545907/200000 = 132.729535. There are 41 nonzero
coefficients, 24 positive and **17 negative**, with |x|_1 = 138.00.

**Corrections (coordinator, 2026-09-08).** An earlier version of this section
over-read the negatives. Four fixes, each material:
- A positive fold DOES deposit above y: +Fold(a) puts +2 at floor(a/2), which
  exceeds y once a > 2y (e.g. Fold(434) contributes +2 at 217). The
  nonnegative family is not barred from cells above y; it is barred from the
  specific SIGNED combinations below.
- A negative coefficient x_a < 0 is a fold-basis coordinate, NOT a net deposit
  at cell a. In this witness delta_113 = delta_128 = delta_151 = 0 even though
  x_113, x_128, x_151 < 0: the recurrence delta_a = -x_a + 2 x_{2a} + 2 x_{2a+1}
  makes the net at a independent of the sign of x_a.
- 66.338409... is Codex's proved UPPER BOUND on the nonnegative-fold family,
  not an established optimum; the 17 negatives have not each been proved
  indispensable.
- "prime cell" below means a cell with positive prime-power mass, m_q > 0,
  which is a statement about the interval (N/(q+1), N/q] containing a prime
  power, not about the label q. Cell 103 has m = log 97 because that interval
  contains the prime 97.

**The 17 negative coefficients.** With those cautions, the negative
coordinates are the fold directions the nonnegative family cannot use (its
optimum is bounded by 66.34); realizing 132.73 needs them, and Section 12
accounts for exactly how much each one is worth. Their cells:

    (y, 2y]:  102, 113, 123, 125, 126, 128, 129, 133, 142, 144, 151, 156, 163, 172   (14, destination floor(a/2) in the prefix top-half)
    (2y, .]:  227, 256, 303   (3, with floor = 113, 128, 151, themselves negative cells)

so the negatives form a two-level halving tree: three tail deposits feed the
band deposits, which feed the prefix top-half. This is what "push a deposit up
into the fake cells" costs in fold coordinates.

**One parameterized signed exchange with proved cancellation.** Pair a source
with its half-destination twin: for k in (y/2, y] with both 2k and 2k+1
attainable,

    X_k = Fold(2k+1) - Fold(2k)  =  -e_{2k+1} + e_{2k} + (kappa(2k+1) - kappa(2k)),

and the half-destination cancels exactly, because floor((2k+1)/2) = floor(2k/2)
= k, so the two +2 e_k terms subtract to zero (proved, not fitted; checked on
all eight attainable twins, destination gone in every case). A_top X_k = 0 by
Lemma 7, and the gain is g(2k+1) - g(2k). This is the atomic prime-to-fake lift
underlying the negative coefficients: it deposits at the fake cell 2k using the
un-fold e_{2k}, funded by the down-fold at 2k+1.

**Concrete capacity argument.** X_k's negative coordinates are the source 2k+1
and the cells where kappa(2k+1) - kappa(2k) < 0; the half-destination k is
cancelled. It is feasible from m iff every negative cell has m_c > 0, and then
its scale is eps* = min over those cells of m_c/(-X_c) -- absence of a
zero-mass withdrawal guarantees SOME positive scale, not the full source mass
(that coincides only when the binding coefficient is 1). At (10^4, 100)
exactly one twin qualifies: X_51 = Fold(103) - Fold(102), whose only negative
cell is 103 (m_103 = log 97 > 0 because the interval (N/104, N/103] holds the
prime 97; coefficient -1; the prefix correction is nonnegative), so eps* =
log 97 and gain (g(103)-g(102)) eps* = log 97 = 4.5747 -- the rough shift of
Section 8 in fold coordinates.

**Proved parameter domain, and the gap.** Proved: for every k in (y/2, y] with
2k, 2k+1 attainable, X_k has zero moments and a cancelled destination, and it
is a feasible witness with scale eps* = min_{X_c<0} m_c/(-X_c) and gain
eps*(g(2k+1)-g(2k)) whenever every negative cell has positive prime-power mass;
at (10^4, 100) X_51 is the only such instance, equal to the rough shift. Not
proved: the other 16 un-folds have a negative cell at a zero-mass position, so
a single X_k is infeasible there and they enter only inside a coordinated
bundle whose zero-mass drains cancel -- the lower-half supply question of the
capacity lane. Source labels are facts at this one input, not a formula in N.

## 12. The h-decomposition of the witness, and the confluence triple

Codex's upper certificate is beta_q = B_q / 1387 on the 52 cells B (listed in
`grouped_signed.py`). With g_a = sum_q Fold(a)_q and

    h_a = -g_a - (F^T beta)_a = -g_a - sum_q Fold(a)_q beta_q,

the reduced-cost identity holds for EVERY signed x with nu = m + Fx >= 0:

    g^T x = beta^T m + sum_a h_a (-x_a)_+ - sum_a h_a (x_a)_+ - beta^T nu,

by (F^T beta)_a = -g_a - h_a. `grouped_signed.py` checks h >= 0 on all 98
folds and the identity on the saved witness:

    132.729535 = 66.338409  (beta^T m, Codex's upper-bound base)
               + 152.056717 (sum over negatives of h_a |x_a|)
               - 58.708394  (sum over positives of h_a x_a)
               - 26.957196  (beta^T nu, the slack against the certificate).

Two consequences. First, an exact upper handle on the WHOLE signed family:
since h >= 0, x_a >= 0 terms and beta^T nu >= 0 only subtract, so

    g^T x <= beta^T m + sum_{x_a < 0} h_a |x_a|

for every feasible x. The excess of any signed witness over the upper-bound
base 66.338 is at most the h-weighted negative mass. Second, the h-weights say which
negatives matter: h_a = 0 at the three cells 113, 163, 303, so those un-folds
carry no gain leverage (pure feasibility bookkeeping); the six largest weighted
contributions h_a |x_a| are at 102 (24.12), 123 (19.32), 126 (19.18), 133
(16.45), 142 (13.79), 144 (13.28). These weights are diagnostic, not the gain
of any single move (correction: a negative coordinate is a fold-basis
coefficient, and delta_113 = delta_128 = delta_151 = 0 despite x < 0 there).

**One grouped signed construction: the confluence triple.** For an even cell b
above y with m_b = 0, let k = b/2 and take

    C(b) = Fold(2b) + Fold(2k+1) - Fold(b),

the double 2b and the odd twin 2k+1 as sources and the un-fold at b. It has
zero moments by Lemma 7 (each fold contributes), and it is more than a twin:
adding the double Fold(2b) is what lifts it past the rough shift. Its measure
withdraws at 2b, at 2k+1, and at the negative entries of the combined prefix
correction kappa(2b) + kappa(2k+1) - kappa(b); the destination deposits +3 at b
and +2 - 2 at the prefix cell k (the +2 from Fold(2k+1) and -2 from -Fold(b)
offset, though the kappa residue at k does NOT fully vanish, so feasibility is
"no zero-mass cell drained", verified, not exact cancellation at k). Scale
eps* = min over withdrawn cells of m_c / (-C(b)_c); gain eps* (g(2b) + g(2k+1)
- g(b)).

At (10^4, 100) the only even zero-mass b whose double and twin both carry mass,
with positive gain units, is b = 102: 2b = 204 = floor(N/49) (m = log 7,
49 = 7^2), twin = 103 = floor(N/97) (m = log 97), gain units g(204) + g(103) -
g(102) = 4 + 3 - 2 = 5, binding cell 204 so eps* = log 7, total gain 5 log 7 =
9.729551. This beats the rough shift log 97 = 4.5747 by adding the double
source, and it is a genuine three-fold group, not a twin, not the whole
witness, and not the rough shift.

**Proved, and the remaining gap.** Proved at this input: the identity and the
excess bound above (h >= 0 verified on all 98 folds), and C(102) as a feasible
signed witness of gain 5 log 7 with every withdrawal on a mass cell. The
confluence rule is prescribed arithmetically (sources 2b and 2k+1, destination
b, weights +1, +1, -1), and its capacity condition is explicit: m_{2b} > 0,
m_{2k+1} > 0, and the prefix residue kappa(2b) + kappa(2k+1) - kappa(b)
nonnegative off the mass cells. What is NOT proved, and the reason 132.73 needs
the full coupled bundle: at (10^4, 100) b = 102 is the ONLY cell meeting the
capacity condition, so the confluence does not by itself compose to a large
witness; its supply (double and twin both massed, residue on mass cells) is the
same lower-half availability question the capacity lane owns, now sharpened to
a condition on the pair (2b, 2k+1). Source labels are facts at this one input,
not a formula in N.

## 7. Reproduce

    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      .venv/bin/python dual_witness.py --N 1000 --y 31 --output out.json      # 12 s
    ... --N 10000 --y 100 ...                                                # 37 s
    .venv/bin/python prefix_witness.py --N 1000 --y 31 --output out.json      # 0.2 s
    ... --N 10000 --y 100 ...                                                # 14 s
    .venv/bin/python fake_mass_witness.py --N 1000 --y 31 --output out.json   # 30 s
    ... --N 10000 --y 100 ...                                                # 100 s
    .venv/bin/python fold_family.py --N 1000 --y 31 --output out.json         # 0.1 s
    ... --N 10000 --y 100 ...;  ... --N 3600 --y 60 ...                      # 0.1 s each

`tests/test_certificate_lp_dual_witness.py` pins the (1000, 31) witness (exact
identities, sign enclosure, the gain interval, the prefix family's zero) and
Construction B's established gain at (1000, 31).
