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

## 1. Every witness is a basis, and its gains are the tight certificate's elevations

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
large and negative) admits one cell. So the natural generalization, "the
Mobius prefix carries the barrier", is refuted at both sizes: the barrier
lives in bases that interleave emptied (elevated) cells below y with
mass-free composite cells above it, and the prefix has neither.

The three-cell relation R_q - R_{q-1} = R_1 for a y-rough q (the rough spike
in T* form: remove m_q from q, add it to q-1 and 1, gain m_q) needs q and q-1
both attainable. For q <= sqrt(N) both are, but at y = sqrt(N) there is no
y-rough q in (y, sqrt N], so it certifies 0 there; it is a positive bound
only for y < sqrt(N) - 1.

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

## 6. Reproduce

    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      .venv/bin/python dual_witness.py --N 1000 --y 31 --output out.json      # 12 s
    ... --N 10000 --y 100 ...                                                # 37 s
    .venv/bin/python prefix_witness.py --N 1000 --y 31 --output out.json      # 0.2 s
    ... --N 10000 --y 100 ...                                                # 14 s

`tests/test_certificate_lp_dual_witness.py` pins the (1000, 31) witness (exact
identities, sign enclosure, the gain interval, the prefix family's zero).
