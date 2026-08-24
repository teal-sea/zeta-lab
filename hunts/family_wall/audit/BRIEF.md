# Brief: refute a barrier claim

You are auditing a mathematical claim that the person who wrote this believes is TRUE and
wants you to attack. Your job is refutation, not confirmation. A refutation is worth far
more than an agreement, so do not soften anything.

Implement everything yourself from the definitions below. Do not look for prior
implementations. Do not trust any number stated here: every constant is a claim to be
recomputed.

## Definitions

Kernel, for real `x`:

    K(x) = ∫_{-1/2}^{1/2} cos(√2 · t) · cos(2π · x · t) dt
    k(x) = K(x) / K(0)
    w(x) = k(x)²

`K` has a closed form as a combination of two sinc terms. Derive it yourself.

For an integer `n ≥ 3` (this is `n` points, so `k = n − 1` gaps), a pressure `p > 0`, and a
vector of nonnegative gaps `g = (g_1, …, g_k)`:

    F_{n,p}(g) = (1/p) · Σ_{i=1..k} g_i
               + Σ_{s=1..n−1} (2/(n−s)) · Σ_{i=1..n−s} w(g_i + g_{i+1} + … + g_{i+s−1})

The inner sum runs over the `n − s` windows of `s` consecutive gaps. Write `S(g) = Σ g_i`
for the total length, and `W(g) = F_{n,p}(g) − S(g)/p` for the pressure-free part, which
does not depend on `p`.

Constant:

    H = 3/2 − (1/√2) · cot(1/√2)

A triple `(c, m, p)` is **admissible** for `n` when `c > 0`, `m` and `p` are integers with
`m ≥ n` and `p > 0`, the cap condition `c · (m − (n−1)) ≤ 1` holds, and the certificate
condition holds:

    c ≤ F_{n,p}(g)   for EVERY g with all g_i ≥ 0

For an admissible triple define

    Φ_n(c, m, p) = (H − (n−1)(m−1)/(p·m)) / (1 − c·(m − (n−1))/m)

The value `0.6818286874638` comes from a separate argument. Treat it here purely as a
target number.

## The claim to attack

> **CLAIM.** The supremum of `Φ_n(c, m, p)` over all `n ≥ 3` and all admissible `(c, m, p)`
> is at most `0.6751676068`, and in particular is strictly below `0.6818286874638`. No
> matter how many points are used, this family cannot reach the target.

The supporting argument has two halves.

### Algebraic half — verify or break each step

1. `Φ_n = (H·m − (n−1)(m−1)/p) / (m − c(m−(n−1)))`
2. the cap `c(m−(n−1)) ≤ 1` makes the denominator `≥ m−1`, so
   `Φ_n ≤ H·m/(m−1) − (n−1)/p`
3. with `m` at its largest useful value `(n−1) + ⌊1/c⌋`, we have `m−1 ≥ 1/c` when `n ≥ 3`,
   so `Φ_n ≤ H + H·c − (n−1)/p`
4. `c` is a floor over ALL nonnegative `g`, so for ANY single witness `g`,
   `c ≤ F_{n,p}(g) = S(g)/p + W(g)`, hence
   `Φ_n ≤ H + H·W(g) + (H·S(g) − (n−1))/p`
5. therefore any witness `g` with `S(g) ≤ (n−1)/H` gives `Φ_n ≤ H·(1 + W(g))` for EVERY `p`

State plainly whether each step is valid, including sign conditions, and any case where a
numerator could be negative or a denominator could vanish or change sign.

### Numerical half

The claim needs, for every `n`, a witness `g` with `S(g) ≤ (n−1)/H` whose energy `W(g)` is
small. Reaching `0.6818286874638` would require `W ≥ 0.0138706` for every admissible
witness simultaneously.

## What would refute the claim — hunt for these

**(a)** A step in 1–5 that is invalid, or valid only under an unstated condition.

**(b)** An `n` for which NO witness `g` exists with `S(g) ≤ (n−1)/H` and
`H(1 + W(g)) ≤ 0.6751676068`. **This is the main target.** Search over arbitrary
nonnegative gap vectors. In particular do not restrict to regular or periodic patterns:
try irregular gaps, clustered gaps, gaps far from any zero of `k`, and whatever else your
own analysis of `w` suggests. Report the `n` with the largest minimum-`W` you find.

**(c)** A concrete admissible triple `(c, m, p)` and an `n` with
`Φ_n(c, m, p) > 0.6751676068`, where you have real evidence that `c` is a genuine floor —
a serious global minimisation of `F_{n,p}` over nonnegative `g` that does not go below `c`.

**(d)** Any reason the supremum over `n` could fail to be controlled as `n → ∞`.

## What to compute and report

1. Your own values of `H` and `K(0)`, to 16 digits.
2. For `n = 7, 8, 9, 10, 12, 14, 16, 20, 30, 56, 100`: the smallest `W(g)` you can find
   subject to `S(g) ≤ (n−1)/H`, the witness attaining it, and the bound `H(1 + W(g))`. Say
   which optimiser you used and how you guarded against local minima.
3. Whether any of those bounds exceeds `0.6818286874638` (breaking the barrier at that `n`)
   or `0.6751676068` (breaking the stated supremum).
4. For `n = 7` and `p = 3000`: the global minimum of `F_{7,3000}` over nonnegative `g`, to
   15 digits, with the minimiser.
5. Your step-by-step verdict on the algebraic half.
6. Interval arithmetic wherever you can manage it. **The witness direction is the unsafe
   one**: an underestimated `W` would make a false barrier look true. If you can bound `W`
   rigorously from above for your witnesses, do it and say so. If not, say that plainly.

## Rules

- Implement from the definitions above only.
- Report every disagreement with a stated number loudly, with your value beside it.
- If you cannot break the claim, say exactly what you tried hardest to break and where the
  argument is most fragile. "I could not refute it" plus a map of the weak points is a
  complete and valuable answer.
- Do not conclude that the claim is correct because it looks correct. Compute.

Write your report to `results/REPORT.md` and leave your scripts in this directory.
