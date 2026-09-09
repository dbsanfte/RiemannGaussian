# A bounded common moment with the quadratic zeta source retained

The two arithmetic parts behind the
[positive composite response](zeta-positive-composite-response.md)
now have an exact common response and a proved geometric moment bound
after removing the pole at one. This controls their sum without
discarding either part. A separate exact quadratic identity retains the
nonzero zeta-zero source and all interactions between moment orders.

The common sum's source cancels. Its bound therefore does not supply the
independent inequality required for RH. The quadratic source remains an
open arithmetic estimation problem; there is no new zero exclusion.

## The two arithmetic colours

Let

\[
D(n)=\sum_{p\mid n}\log p-\Lambda(n),\qquad
A(n)=\Lambda(n)+D(n)=\sum_{p\mid n}\log p.
\]

Both `Lambda` and `D` are nonnegative. The new theorems
`zetaMixedPrimeArithmetic_prime_pow` and
`vonMangoldt_mul_zetaMixedPrimeArithmetic` prove

\[
D(p^k)=0\quad(k\ge1),\qquad \Lambda(n)D(n)=0.
\]

Thus the positive parts have disjoint arithmetic support. In particular,
`zetaPrimeDivisorColour_sq` retains the exact signed-colour identity

\[
(\Lambda(n)-D(n))^2=A(n)^2.
\]

The full positive composite coefficient `B=Lambda*D` also vanishes on
every prime power, by `zetaPositiveCompositeArithmetic_prime_pow`. All
convolution and divisor signs remain available in the original exact
identities; no norm was used to obtain these support results.

## Opposite poles and their common analytic response

Put `F=-zeta'/zeta`, and keep the actual proper-prime-power series `E`,
analytic on `Re s>1/2`. The nonnegative mixed-prime series represents

\[
V(s)=\frac{\zeta'(s)}{\zeta(s)}-\zeta'(s)-\zeta(s)E(s).
\]

`LSeriesHasSum_zetaMixedPrimeResponse` proves genuine absolute
convergence to `V` in `Re s>1`. Its exact common sum with the prime arm is

\[
\boxed{F+V=H,\qquad H=-\zeta'-\zeta E.}
\]

`zetaPrimeColourResponse_sum` preserves this pointwise identity, and
`LSeriesHasSum_zetaPrimeDivisorResponse` identifies `H` with the genuinely
convergent series of `A(n)`. `analyticAt_zetaPrimeDivisorResponse` proves
`H` analytic throughout `Re s>1/2` except at one, including every zeta zero
in that half-plane.

At a hypothetical right-half zero of multiplicity `m`, `V` has a simple
pole with coefficient exactly `+m`. These are the new
`meromorphicOrderAt_zetaMixedPrimeResponse` and
`meromorphicTrailingCoeffAt_zetaMixedPrimeResponse` theorems. The prime
response `F` has coefficient `-m`, so the two sources cancel in `H`.
Their arithmetic nonnegativity is fully compatible with this cancellation
in the meromorphic continuation.

The fixed positive composite response is also the exact product

\[
T=FV
\]

where zeta is nonzero, by
`zetaPositiveCompositeResponse_eq_prime_mul_mixed`. The hypothesis is
retained explicitly; the identity is not applied to totalized division
at a zeta zero.

## Removing the complete common pole at one

Write `Z(s)=(s-1)zeta(s)` for the actual entire extension `riemannZeta₁`.
The explicit formula

\[
G(s)=Z(s)-(s-1)Z'(s)-(s-1)Z(s)E(s)
\]

is analytic throughout `Re s>1/2`, including one, and has `G(1)=1`.
`zetaPrimeDivisorRegular_eq` proves

\[
G(s)=(s-1)^2H(s)\quad(s\ne1).
\]

The repaired value at one comes from the explicit analytic formula.
No singular quotient is treated as analytic merely because division is
totalized in Lean.

Define

\[
f_N(s)=M_N\big((\cdot-1)^2F\big)(s),\qquad
v_N(s)=M_N\big((\cdot-1)^2V\big)(s),
\quad M_N(f)=\frac{(-1)^N f^{(N)}}{N!}.
\]

`zetaPrimeColourMoment_sum` proves the full signed equality

\[
f_N(s)+v_N(s)=M_N(G)(s)\qquad(\Re s>1).
\]

For any closed disc with center `s` and radius `0<R<Re s-1/2`, Cauchy's
estimate gives the independent bound

\[
|M_N(G)(s)|\le C/R^N\quad\text{for every }N.
\]

This is `exists_zetaPrimeDivisorRegular_moment_bound`. The proof uses the
actual analytic expression for `G`, with no zero-avoidance assumption.

At the existing center `s_0=3/2+i Im rho`, put `u=s_0-rho>0` and use the
explicit radius `R=(u+1)/2`. Then `q=u/R` lies strictly between zero and
one, and

\[
\boxed{|u^N(f_N(s_0)+v_N(s_0))|\le Cq^N\longrightarrow0.}
\]

The terminal theorems are `exists_zetaPrimeColourMoment_geometric_bound`
and `tendsto_zetaPrimeColourMoment`. The finite constant may depend on
the actual center and radius, but not on `N`; it is not a numerical
zero-location certificate.

The three `hasSum_zetaPoleClearedPrimeMoment`,
`hasSum_zetaPoleClearedMixedMoment`, and `hasSum_zetaPrimeColourMoment`
theorems retain the literal arithmetic series with one common complex
kernel. `exists_zetaPrimeColourArithmetic_geometric_bound` applies the
same bound to that genuine convergent series. No positivity of the
pole-removing kernel is assumed.

## Keeping the quadratic source instead of cancelling it

Let

\[
t_N(s)=M_N\big((\cdot-1)^4T\big)(s).
\]

The complete product rule, proved as
`zetaPoleClearedCompositeMoment_eq_cross`, gives

\[
t_N=\sum_{k=0}^N f_k v_{N-k}.
\]

Substituting the bounded common response only inside this exact form
yields

\[
\boxed{t_N=\sum_{k=0}^N f_k M_{N-k}(G)
              -\sum_{k=0}^N f_k f_{N-k}.}
\]

`zetaPoleClearedCompositeMoment_eq_common_sub_square` keeps every
interaction between moment orders and both sums with their signs.
`hasSum_zetaPoleClearedCompositeMoment` simultaneously retains the
original nonnegative coefficients `B(n)` and the full complex quartic
cofactor kernel.

The source has not been removed from this quadratic response:

\[
\lim_{s\to\rho}(s-\rho)^2(s-1)^4T(s)
=-m^2(\rho-1)^4\ne0.
\]

This punctured limit and its nonzero coefficient are checked by
`tendsto_zetaPoleClearedCompositeSource` and
`zetaPoleClearedCompositeSource_ne_zero`.

The known geometric bounds control the individual common moments
`M_j(G)`. They do not by themselves bound their convolution with the
prime moments, or the surviving prime quadratic form. Obtaining an
independent signed bound for the complete quadratic expression, with
every other pole and the retained source accounted for, is still the
next mathematical obligation. The decaying linear sum cannot be used
as the RH contradiction because its own zero source cancels.

## Verification

Both new modules are imported by the root library. The local gates
include direct warnings-as-errors checks, focused and full builds,
whole-project declaration lint, root-imported module lint and every new
public theorem's axiom audit, plus source and whitespace checks. Work
remains local under the user's commit hold. No literature-priority claim
is made for these identities.
