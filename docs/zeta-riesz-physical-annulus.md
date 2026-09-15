# The actual physical annulus

Lean now independently pays **every actual term above the square of the
physical cutoff**, on `0<u<exp(-2/3)`. Every coefficient at or below the
physical cutoff is exactly zero. The complete source therefore survives
in the smaller interval `X_N<n<X_N^2`, with every previous support cut
retained. A nonzero survivor containing an extreme prime must be an
intermediate/extreme semiprime. The other class has all primes below
`X_N`. **Their joint signed lower bound remains open.**

Open the [physical-annulus theorem chain](https://dbsanfte.github.io/RiemannGaussian/rh-proof/?endpoint=physical-annulus)
for compiled statements, exact source lines, dependency paths and axiom
audits. This is a supporting endpoint; the default whole-carrier frontier
remains unchanged.

## Original physical data and general estimate

The original source coordinate, integer floor and length remain:

\[
u=\tfrac32-\beta,\qquad
D_N=\left\lfloor\frac{u^{-N}}{N+1}\right\rfloor,\qquad
X_N=(D_N+2)^2,\qquad L_N=\log X_N.
\]

For `h≥0` and `0<u<exp(-h)`, Lean proves `L_N≥2hN` eventually.
The general summed tilt with `q>0`, `sigma>1` and
`q+sigma-3/2≤0` gives the rate

\[
r(k,h,q,\sigma)=q^{-1}
 \exp\bigl(2kh(q+\sigma-3/2)-h\bigr).
\]

Every changing finite class `S_N` with `k L_N≤log(n)` satisfies eventually

\[
\left|u^{N+1}\sum_{n\in S_N}C_{L_N}(n)K_{P,N}(3/2+iy,n)\right|
\le r(k,h,q,\sigma)^N\,u\,A(P,q,\sigma).
\]

Here `C` is the actual signed Riesz coefficient, `P` is any fixed complex
polynomial, and `A` retains all its factorial shifts and a genuinely
convergent divisor-majorant mass. The bound is uniform in the ordinate
and finite selection. Its constants and starting order are not numerically
evaluated. No zero or unproved arithmetic cancellation is assumed.

## Two new degree bounds and the broader product bound

Each distinct prime factor at or above `X_N` contributes at least `L_N`
to the same integer's logarithm. This proves the following exact rates:

| Controlled actual class | Source interval | Geometric rate |
| --- | --- | --- |
| At least two primes at or above `X_N` | `0<u<exp(-2/3)` | `(8/3)*exp(-95/96)<1` |
| At least three primes at or above `X_N` | `0<u<exp(-9/16)` | `(27/8)*exp(-2533/2048)<1` |
| Every label `n≥X_N^2`, irrespective of prime count | `0<u<exp(-2/3)` | `(8/3)*exp(-95/96)<1` |

The first two estimates and their adaptive deletion are proved in
[`ZetaRieszLowerDegreeBounds`](../RiemannGaussian/ZetaRieszLowerDegreeBounds.lean)
and [`ZetaRieszLowerDegreeDeletion`](../RiemannGaussian/ZetaRieszLowerDegreeDeletion.lean).
The full-product estimate is
[`tendsto_above_physical_square`](../RiemannGaussian/ZetaRieszPhysicalProductBounds.lean).
It reaches labels that have fewer than two extreme primes as well.

For `n≤X_N`, the Riesz profile is saturated: every nonunit composite
profile is zero. Prime and nonsquarefree labels are already deleted,
and the unit's logarithm is zero. Thus the lower prefix vanishes
**exactly**, before a norm or limit is taken.

## The two surviving classes

[`tendsto_degree_sub_annulus`](../RiemannGaussian/ZetaRieszPhysicalAnnulus.lean)
pays the entire additional deletion independently and retains the
previous residual outside `u<exp(-2/3)`. At every exposed right-half zero,
`tendsto_normalizedAnnulus` retains the limit `-m_rho`, and the real sum
still has its original coefficient, positive factorial envelope and
`cos(gamma log(n))` phase.

Inside `X_N<n<X_N^2`, an extreme prime `p≥X_N` forces its entire cofactor
`a` below `X_N`. A composite cofactor has zero saturated profile, and a
unit cofactor is a deleted prime label. Hence a nonzero coefficient forces
`a` prime, with the exact expression

\[
C_{L_N}(pa)=-\frac{\log(pa)\log a}{L_N}.
\]

Once the actual physical cutoff exceeds `N^2`, the earlier semiprime
deletion also forces `N^2<a<X_N≤p`. This yields the compiled
`annulus_support_dichotomy`: either all prime factors of `n` lie below
`X_N`, or `n` is precisely such an intermediate/extreme semiprime.
The physical-head comparison is already proved eventual for every
`0<u<1`. The [intermediate-prime support theorem](../RiemannGaussian/ZetaRieszIntermediatePrimeSupport.lean)
also forces an actual prime between `N^2` and `X_N` in every nonzero
survivor. These statements keep the original integer labels and do not
replace the carrier by a multiply counted prime-pair sum.

## Remaining obligation

The two classes retain their full product phases and their common physical
boundary. Separate estimates may lose the correlation between them.
Their **joint** real response needs a cofinal floor at least `-c`, for
some `c<1`. Such a floor contradicts the negative multiplicity limit;
`rh_of_exposed_annulus_floors` proves the conditional implication to
Mathlib RH and keeps that floor as an explicit open premise.

At larger `u`, the previous degree restrictions and composite-cofactor
fallback cases remain. All earlier smooth-factor restrictions keep their
own proved parameter ranges. This slice proves no RH result, new zero-free
region, numerical zero bound or historical novelty. Ordinary CI does not
run the optional exhaustive numerical certificate.
