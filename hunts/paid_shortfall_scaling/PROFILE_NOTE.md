# Supplemental profile calculation retained for follow-up

This is an additional proposed refinement from the cap reviewer. It is not a
dependency of `RESULTS.md` or the cutoff-selection algorithm. Its explicit
constant has not received the finite numerical checks or fresh proof review
used for the main results, so it is retained as a candidate argument rather
than promoted by the main run's PASS status.

Let `delta(q)` be any fixed nonnegative profile bounded by `D`. Put

\[
 I_\delta=\sum_{q\ge1}\delta(q)(q^{-1/2}-(q+1)^{-1/2}),
 \qquad J_\delta=\int_0^1\delta(\lfloor t^{-2}\rfloor)\log t\,dt.
\]

Both are absolutely convergent, with `0<=I<=D` and `-D<=J<=0`. The
proposed explicit bound, for integer `N>=8`, is

\[
 \left|S_N-\tfrac12\sqrt N\log N I_\delta-\sqrt N J_\delta\right|
 \le12D N^{1/3}\log N.                              \tag{P}
\]

Argument supplied: extract the square sum as in `RESULTS.md` equation (2).
Write `x=sqrt N`, `Q=floor(N^(1/3))`, and `z=x/sqrt(Q+1)<=N^(1/3)`.
For each of the first Q quotient cells, replace
`L(x/sqrt q)-L(x/sqrt(q+1))` by the integral of `log v` over the same
interval. The factorial remainder gives total error at most
`2DQ(1+log x)`. The remaining square sum and integral have absolute total
at most `2Dz log z+2D`. These terms together are at most
`4D N^(1/3) log N` for `N>=8`. Adding the nonsquare remainder bound with
constant eight gives (P). The substitution `v=xt` evaluates the whole
integral as `x log x I_delta+x J_delta`.

If this argument is retained after its separate checks, every fixed bounded
profile would satisfy `S_N/(sqrt N log N) -> I_delta/2`. The finite bound
would also apply to varying bounded profiles with their corresponding
`I_delta_N,J_delta_N`; it would not turn those changing quantities into a
fixed leading coefficient. When only the attained quotient cells are known,
one may extend that finite profile by zero outside them for that N.

This does not assert that arbitrary coefficient families have bounded
deficits, or that the new balanced-prefix family has a fixed deficit profile.
