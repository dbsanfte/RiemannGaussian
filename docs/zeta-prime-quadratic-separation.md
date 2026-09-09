# The remaining zero source lives in a distinct-prime quadratic sum

The complete mixed product in the prime-colour quadratic identity now
has an independent bound at the selected zero's source scale. The
single-prime part of the pure quadratic has a stronger geometric bound.
Consequently every hypothetical zero with real part greater than one
half forces its whole nonzero quadratic source into one literal sum
supported on products `p^a*q^b` with distinct primes and positive exponents.

The signed upper bound for that remaining sum is open. These results
supply no new zero exclusion or zero-count certificate. They narrow the
arithmetic object that would have to furnish a contradiction.

## The actual functions and their different pole orders

Keep the notation from the [prime-colour coupling](zeta-prime-colour-cancellation.md):

\[
F=-\zeta'/\zeta,\quad
H=-\zeta'-\zeta E,\quad
F+V=H,\quad T=FV,
\]

where `E` is the genuine proper-prime-power series, analytic on
`Re s>1/2`, and `T` has the nonnegative coefficients `B=Lambda*D`.
Here `*` between arithmetic functions denotes Dirichlet convolution.
The identity involving `T=FV` retains its nonzero-zeta hypothesis.
Define the two fixed responses

\[
P(s)=(s-1)^4F(s)^2,\qquad M(s)=(s-1)^4F(s)H(s).
\]

`zetaPrimeQuadraticResponse_identity` proves the exact identity

\[
(s-1)^4T(s)=M(s)-P(s)
\]

where zeta is nonzero. At any selected nontrivial zero `rho`, with
actual multiplicity `m`, the prime square has order exactly `-2` and
leading coefficient `(rho-1)^4*m^2`. Theorems
`meromorphicOrderAt_zetaPrimeSquareResponse` and
`meromorphicTrailingCoeffAt_zetaPrimeSquareResponse` prove these facts.
No unknown leading derivative phase remains. For `Re rho>1/2`, `H` is
analytic at `rho`, so `M` has at most a simple pole. This is
`meromorphicOrderAt_zetaPrimeMixedProductResponse_gt`.

Let `s0=3/2+i Im rho`, `u=s0-rho>0`, and use the existing closed disc
of radius `R=(u+1)/2`, so `u<R<1`. The new weight
`zetaPrimeQuadraticWeight` is the actual finite common clearing product
for `P` and `M` on this closed disc, excluding `rho`. It is entire and
nonzero at `rho`. All other poles, including boundary poles and zeros of
higher multiplicity, are handled by the complete divisors. The earlier
Wronskian weight is not silently reused: a derivative-based Wronskian
may lose a pole at a multiple zero where `F` still has one.

## An independent estimate for the whole mixed product

Write `mu_N(f)=(-1)^N f^(N)(s0)/N!`, and set

\[
Q_N=\mu_N(WP),\qquad J_N=\mu_N(WM),\qquad
c=W(\rho)(\rho-1)^4m^2\ne0.
\]

The checked estimates are

\[
\left|\frac{u^{N+2}Q_N}{N+1}-c\right|\le\frac{C_Q}{N+1},\qquad
\left|\frac{u^{N+2}J_N}{N+1}\right|\le\frac{C_J}{N+1}.
\]

The terminal theorems are `exists_zetaPrimeQuadraticMoment_decay_bound`
and `exists_zetaPrimeMixedProductMoment_decay_bound`; both limits are
also proved. The second inequality assumes no upper bound for `Q_N`.
It estimates the whole meromorphic product after the actual clearing.
The finite constants may depend on `rho`; no uniform estimate over
different zeros is claimed.

The exact moment cross terms remain available in
`zetaPrimeQuadraticMoment_eq_full_cross` and
`zetaPrimeMixedProductMoment_eq_full_cross`. With `G=(s-1)^2H` the explicit
analytic common response, these are respectively the complete sums

\[
\sum_{k=0}^N\mu_k\bigl(W(s-1)^2F\bigr)
                 \mu_{N-k}\bigl((s-1)^2F\bigr),\qquad
\sum_{k=0}^N\mu_k\bigl(W(s-1)^2F\bigr)\mu_{N-k}(G).
\]

The estimate does not replace either full sum by separate bounds for
its factors.

## The unchanged arithmetic kernel

Put `A=Lambda+D`, `C2=Lambda*Lambda`, and `R2=Lambda*A`. Lean proves
coefficientwise

\[
R_2=C_2+B,\qquad 0\le C_2\le R_2.
\]

All three arithmetic sums use exactly the same kernel

\[
K_{\rho,N}(n)=n^{-s_0}\sum_{k=0}^N
  \mu_k\bigl(W(s)(s-1)^4\bigr)
  \frac{\log(n)^{N-k}}{(N-k)!}.
\]

The feature at `n=0` follows the existing library convention; each
arithmetic coefficient there is zero. All cofactor derivatives are
retained. `hasSum_zetaPrimeQuadraticMoment`,
`hasSum_zetaPrimeMixedProductMoment`, and
`hasSum_zetaPrimeQuadraticComposite` prove genuine convergence to
`Q_N`, `J_N`, and `J_N-Q_N`, respectively. Their normalized limits are
`c`, `0`, and `-c`.

This explicitly records why raw coefficient domination supplies no
contradiction: `K` is complex and depends on the complete clearing
weight. No theorem asserts positivity through this filter.

## Removing the single-prime part independently

Split `C2(n)` into `Delta(n)`, its prime-power restriction, and `Omega(n)`,
its complement. `zetaPrimeDiagonalCoefficient_le` proves

\[
0\le\Delta(n)\le\log(n)\,E_n,
\]

where `E_n` is the existing proper-prime-power coefficient. Thus the
literal diagonal Dirichlet series converges absolutely and is analytic
on `Re s>1/2`, by `LSeriesSummable_zetaPrimeDiagonal` and
`analyticAt_zetaPrimeDiagonalResponse`.

This remains true after multiplying by the full entire cofactor.
`exists_zetaPrimeDiagonalMoment_geometric_bound` proves, for some
`C>0` and `0<q<1`,

\[
\left|u^{N+2}\sum_n\Delta(n)K_{\rho,N}(n)\right|\le Cq^N.
\]

`zetaDistinctPrimePairCoefficient_support` proves that a nonzero
remaining coefficient requires `n=p^a*q^b` with distinct prime bases
and positive exponents. `hasSum_zetaDistinctPrimePairMoment` retains
the genuine convergent arithmetic sum. The terminal source theorem is

\[
\boxed{\frac{u^{N+2}}{N+1}
  \sum_n\Omega(n)K_{\rho,N}(n)\longrightarrow c\ne0,}
\]

proved by `tendsto_zetaDistinctPrimePair_source` together with
`zetaPrimeQuadraticSource_ne_zero`.

To obtain a contradiction through this quadratic route, an independent
bound for this complete signed distinct-prime sum would have to beat that
source. Further improvements to the already negligible diagonal or mixed
product are unnecessary for that purpose. Absolute coefficient bounds
alone do not use the required correlation. The subsequent
[route audit](zeta-contradiction-route-audit.md) pauses further decomposition
and returns to the simpler existing linear finite band as the reference
target for an independent estimate.

## Exact two-prime coefficients and logarithmic separation

`ZetaPrimePairSeparation.lean` proves that for distinct primes `p,q` and
positive exponents `a,b`,

\[
C_2(p^a q^b)=\Omega(p^a q^b)=2\log p\log q.
\]

The complete divisor-antidiagonal has only two nonzero ordered
contributions, `(p^a,q^b)` and `(q^b,p^a)`. The terminal identities are
`zetaPrimePairArithmetic_two_prime_powers` and
`zetaDistinctPrimePairCoefficient_two_prime_powers`.

The exact product/separation relation is

\[
2ab\,\Omega(p^a q^b)=\log(p^a q^b)^2-
       \bigl(\log(p^a)-\log(q^b)\bigr)^2,
\]

proved by `zetaDistinctPrimePairCoefficient_separation`. Its downstream
bound `zetaDistinctPrimePairCoefficient_product_bound` is
`Omega(p^a*q^b) <= log(p^a*q^b)^2/(2ab)`. The exact nonnegative defect is
retained. These are elementary arithmetic identities, not a proved signed
estimate after the complex kernel is applied, and no novelty is claimed.

## Scope and provenance

These are properties of the actual zeta function and literal arithmetic
coefficients, for every selected right-half zero with its true
multiplicity. They are independent of the earlier finite phase optimiser.
The proofs combine standard Dirichlet convolution, meromorphic orders,
finite pole clearing, and Cauchy estimates with the repository's exact
colour split. No claim of literature novelty is made.

Local source and documentation are kept uncommitted under the user's
standing instruction. The RH goal remains open.
