# Keep the bound controlled by construction

## Disposition after owner redirection

**Paused. No new uniform arithmetic estimate toward RH was established.**
The controlled norm is standard approximation geometry; the tested update
and explicit missing inequality do not make that inequality easier or
prove its required lower bound. A passing algebra review is not a research
advance on RH. Preserve the code and evidence, but do not expand this
numerical ladder or treat the previous run as a solved research goal.
The owner has invited a fresh search beyond the lab's frontier map.
This is an allocation decision, not a refutation of the identities below
or a theorem excluding the broader Nyman-Beurling method.

## Preserved construction

**Candidate: a cross-term-preserving block energy descent.**
The error norm cannot increase. A concrete arithmetic inequality would force
it to zero, but that inequality is not proved. This is not an RH solution.
The five finite shell checks survive two Arb precisions and a small
independent comparison. Independent mathematical challenge accepted the
block algebra and added a residual-matched fallback. See section 7 and
[the review record](ENERGY_REVIEW.md).

## 1. The change of mechanism

The earlier sum-of-absolute-values estimate charges separately for terms
that cancel. Increasing a fixed set of paired primes improves a constant
without removing that loss. This continuation changes the object being
controlled, not the theorem sought: use an established RH-equivalent
squared approximation error, and cancel old and new components *before*
measuring the cost of the new component.

This does not assert a square-root bound on D_N. It changes to a different
criterion with an explicit equivalence to RH. The Nyman-Beurling criterion,
its integer-dilation strengthening, least-squares monotonicity, and Schur
complements are existing mathematics, not discoveries claimed here.
The repo already has a large finite distance ladder. This run is a small
check of a particular quantitative-decrease witness, not another attempt
to infer convergence from extending that ladder.

## 2. Exact setup and controlled bound

Use the Baez-Duarte integer-dilation criterion:

    H = L2(0,infinity), chi = indicator_(0,1),
    e_k(t) = fractional_part(1/(k t)),
    E_N = inf_a ||chi - sum_{k=1..N} a_k e_k||^2.

RH is equivalent to E_N tending to zero. The source is
[Baez-Duarte, math/0202141v2](https://arxiv.org/abs/math/0202141v2).
Its abstract was retrieved directly during this continuation. The exact
Gram entries and their prior validation are recorded in
[the existing source note](../rogue_frontier/nyman_beurling/SOURCES.md).

Nested approximation spaces immediately give the unconditional control

    0 <= E_(2N) <= E_N <= 1.                               (1)

This controls an approximation error, not the old prime-error sum. It
prevents growth; by itself it does not prove convergence to zero.

Write the Gram matrix and target vector for a doubling block as

    G_(2N) = [G  C; C^T  D],     b_(2N) = [b; d],
    b_k = (1-gamma+log k)/k.

The finite basis is linearly independent. One way to see this is to take
the jumps at t=1,1/2,...,1/N in that order: the jump equation at 1/n
involves precisely the coefficients indexed by divisors of n, so it is
triangular with nonzero diagonal. Thus the finite Gram matrices are
positive definite. Define

    a = G^(-1)b,
    S = D - C^T G^(-1)C,
    u = d - C^T a.

S is the Gram matrix of the genuinely new directions after their old-space
components are subtracted. The exact block minimization identity is

    E_(2N) = E_N - u^T S^(-1)u.                            (2)

All cross terms remain present. The subtracted quantity is nonnegative.
This is the cancellation that a separate magnitude estimate would lose.

## 3. An explicit arithmetic witness, not a fitted block optimizer

Before measurements, choose the new-shell coefficients

    v_n = -mu(n) log(2N/n),       N<n<=2N.                 (3)

This is inspired by the familiar smoothed Mobius shape, but it is used
only as a proposed direction. No conditional asymptotic for that shape is
assumed. In particular, the Bettin-Conrey-Farmer result
[arXiv:1211.5191](https://arxiv.org/abs/1211.5191) assumes RH and an extra
bound on inverse zeta derivatives; it cannot prove RH here. Its
conditional status was checked in the source abstract during this run.

For a nonzero v put

    q = v^T u,       h = v^T S v > 0,
    alpha = q/h,     gain_N = q^2/h.                       (4)

The full coefficient update is

    a_new,old = a - alpha G^(-1) C v,
    a_new,shell = alpha v.                                (5)

The first line is essential: old coefficients change to compensate for
what the new shell already shares with the old span. This is not merely
appending an independently bounded tail.

For any real step t, direct expansion gives exactly

    ||chi - approximation(t)||^2 = E_N - 2t q + t^2 h.

At t=alpha this becomes E_N-gain_N, hence

    E_(2N) <= E_N - gain_N <= E_N.                         (6)

If a chosen v were zero, take gain_N=0 and make no update. The all-scale
positive-gain hypothesis below would then fail, not become a division by
zero or an assumed success. At the tested shells v is nonzero. For the
stated dyadic shells N>=4, Bertrand's prime theorem also supplies a prime
strictly between N and 2N, hence a nonzero entry in (3).

## 4. The precise inequality that would finish this route

**Unproved arithmetic target:** there exists a constant kappa>0, independent
of j, such that at every N=4*2^j,

    (v^T u)^2 >= kappa E_N^2 (v^T S v).                   (7)

Everything in (7) is specified by the arithmetic Gram matrix and (3).
It does not allow fitting v to the block optimum. That makes it an actual
witness proposal, not just a new name for the optimized distance.

Here is the complete conditional implication. If (7) holds, (6) gives

    E_(2N) <= E_N(1-kappa E_N).

If any energy is zero, closure is immediate. Otherwise reciprocal
comparison gives

    1/E_(2N) >= 1/E_N + kappa,
    E_(4*2^j) <= 1/(1/E_4 + kappa j) -> 0.               (8)

Monotonicity extends the limit from the dyadic subsequence to all N.
The cited Baez-Duarte criterion then gives RH. This is a conditional
implication with an explicit missing leaf, not a proof of (7).

It would suffice more generally to establish varying positive kappa_j
with divergent sum and the corresponding inequalities in (7). Merely
showing gain_N>0, or choosing kappa after checking a finite range, does not
suffice. In particular, neither Gram positivity nor the general existence
of an optimum supplies the required lower bound for the correlation q.

## 5. What was actually executed

`energy_probe.py` keeps the existing Vasyunin Gram implementation read-only.
At N=4,8,16,32,64 it computes the complete block identity and the explicit
update at 128 and 192 bits. Every algebraic defect contains zero; both
precisions overlap and the higher-precision radii shrink. The independent
small check uses a separately implemented mpmath Gram formula and solve
at N=4; three Gram entries are also compared with cotangent-free
quadrature carrying an analytic tail. Those comparisons are numerical,
not an independent formal derivation of the published formula.

Selected displayed midpoints from `energy_results.json`:

| N | E_N | E_(2N) | gain_N / E_N^2 |
|---:|---:|---:|---:|
| 4 | 0.06512886865990025 | 0.024161421585896684 | 7.795583728844286 |
| 8 | 0.024161421585896684 | 0.017894023476969435 | 7.824975877621609 |
| 16 | 0.017894023476969435 | 0.01405194369952986 | 8.226890880978283 |
| 32 | 0.01405194369952986 | 0.011376040299673658 | 10.977282529430962 |
| 64 | 0.011376040299673658 | 0.00965854927811191 | 9.28099299248604 |

The table's E_(2N) is the fully optimized error. The witness's own error
is E_N-gain_N and is separately recorded; they must not be conflated.
The displayed ratio belongs to the fixed shell witness, not the full block
optimizer. These finite values do not supply an all-scale kappa.

Controls actually run:

- Negating the optimum scalar step gives E_N+3 gain_N, an observed strict
  increase. A broken update cannot pass as descent.
- Dropping the cross-block subtraction from S breaks the exact block
  identity, with a nonzero enclosure defect.
- A rational hidden-component control has energy
  F_j=1/4+3/[4(j+1)]. It decreases at every step but tends to 1/4;
  its normalized decrease tends to zero. The diagnostic explicitly retains
  this example so nonincrease is never classified as convergence.

The control is about the proposed inference from monotonicity, not a
rival satisfying zeta's full arithmetic hypotheses. No claim is made that
Davenport-Heilbronn has been ruled out by this general Hilbert-space fact.

## 6. What remains to prove

The controlled energy and update are established ordinary linear algebra
under the cited finite Gram setup. The numerical witness survived the
stated finite checks. The missing part is an unconditional lower bound on
its correlation with the residual, relative to its Schur-complement cost,
strong enough to make the cumulative decrease diverge as in (8).

The construction is not rejected for having this missing leaf. It is kept
as a concrete proof target with a safe error bound and a tested direction.
No assertion of novelty, an RH proof, or a new unconditional prime-error
estimate is made. No extension to a large numerical ladder is launched.

## 7. Review addition: remove single-direction blindness

A fixed arithmetic direction can be orthogonal to u even when u is
nonzero. The review supplies a complementary direction: take v=u.
Define M_N=u^T u and T_N=tr S. For u nonzero, its exact decrease is

    gain_adaptive = M_N^2/(u^T S u) >= M_N/T_N.             (9)

For u=0, make no update and record zero gain. The inequality follows from
S<=T_N I. Since C^T G^(-1) C is positive semidefinite,

    0<T_N<=tr D
      =(log(2pi)-gamma) sum_{n=N+1..2N}1/n
      <(log(2pi)-gamma) log 2.                            (10)

The last inequality follows by integrating 1/x over [N,2N]. This prices
the denominator uniformly without requiring a lower eigenvalue bound.
The adaptive direction cannot miss a nonzero u by orthogonality. It does
not supply a lower bound for M_N, or exclude u=0 at an untested scale.

The retained construction takes the better exact decrease from the
predeclared Mobius shell and the residual-matched direction. It therefore
cannot be worse than either alone. Numerically, `energy_reviewed.json`
selects the original Mobius shell at all five tested N. The fallback is
not described as a measured speed improvement. If interval arithmetic
cannot distinguish the two gains, the checker stops instead of selecting
by an unverified midpoint comparison.

The uniform lower-bound target can be weakened. Put N_j=4*2^j. From
E_(2N)<=E_N-M_N/T_N and reciprocal comparison,

    1/E_(N_J) >= 1/E_4 + sum_{j<J} M_(N_j)/(T_(N_j)E_(N_j)^2).   (11)

Thus divergence of the normalized sum would suffice. In particular, the
still-unproved bound

    M_(N_j) >= c T_(N_j) E_(N_j)^2/(j+1),   c>0,           (12)

would give E_(N_J)=O(1/log J), which still tends to zero and implies RH
through the cited criterion. Neither (12) nor its infinite cumulative
version is established here. Ordinary gains sum to at most E_4; it is
the normalized reciprocal-energy sum in (11) that must diverge.

Finite normalized trace bounds M_N/(T_N E_N^2) were approximately
4.27969, 0.955435, 0.545640, 0.326999, 0.242701 at the five tested shells.
They weaken with scale over this range, so a fixed positive lower bound
is not inferred. The quantities and direct adaptive error identities were
recomputed at both precisions and compared independently at N=4.

The error after either corrected line update is a projection error onto
the old span plus one orthogonalized direction. Hence the approximation's
function norm is also at most 1. This is not a bound on the coefficient
vector, and it does not imply that the remaining error is zero.

