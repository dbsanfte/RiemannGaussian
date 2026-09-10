# Small-product decay and the surviving factor geometry

The original rough squarefree sum now has an independent geometric bound
on every product through the cube of its divisor cutoff. Above that cube,
every nonzero coefficient either admits two factors beyond the cutoff or
is an unbalanced semiprime. These remaining sectors retain the full signed
source **together**. Their independent one-sided bound remains open; this
slice excludes no additional zeta zero.

## The original coefficient recovers local cancellation

Write `A_{D,S}(n)` for `zetaRoughSquarefreeCoefficient D S n`, with `S` any
finite prime set. The earlier [unit-divisor comparison](zeta-rough-squarefree-unit-divisor.md)
approximates its full filtered sum by minus the logarithmic composite
weight. That approximation is a bound on the complete sum and cannot be
restricted to an arbitrary sector without another proof.

Return instead to the original coefficient. If `p` is prime and
`1 < m <= D < p`, complete divisor fibres give the exact identity

\[
c_D(pm)=-\Lambda(m).
\]

There is no `log(p)` term. If `m` is squarefree and `pm` avoids `S`, then

\[
A_{D,S}(pm)=
\begin{cases}
-\log m,&m\text{ prime},\\
0,&m\text{ composite}.
\end{cases}
\]

Selected-prime overlaps also have zero coefficient. Thus the whole
small-composite-cofactor sector vanishes pointwise, before applying any
kernel or source identity; the other coefficients in this sector have
norm at most `log(D)`. The coprimality follows from the sizes themselves.
These are formal consequences of the existing divisor identities, not a
claim of a new general identity in number theory.

The entry points in [ZetaRoughSquarefreeFactorGeometry.lean](../RiemannGaussian/ZetaRoughSquarefreeFactorGeometry.lean)
are `zetaMoebiusLogTailCoefficient_large_prime_small_cofactor`,
`zetaRoughSquarefreeCoefficient_large_prime_composite_zero`, and
`sum_zetaRoughSquarefreeCoefficient_remove_small_composite`.

## An independent bound for the entire smaller-product region

Let `M(n)=zetaMoebiusLogMajorant n`, and use the original full polynomial
kernel

\[
K_{P,N}(s,n)=\left(\sum_k P_k\frac{\log(n)^{N+k}}{(N+k)!}\right)n^{-s}.
\]

For **any** coefficient family with `|a(n)| <= M(n)`, any real ordinate
`y`, and any finite subset `T` of `n <= X`, Lean proves

\[
\left|\sum_{n\in T}a(n)K_{P,N}(3/2+iy,n)\right|
\le 2^{-N}X^2 C(P),
\quad
C(P)=\left(\sum_k |P_k|2^{-k}\right)
\sum_{n\ge0}M(n)n^{-3/2}.
\]

The majorant has zero weight at `n=0`; the displayed mass uses that
convention. Its convergence is proved. A positive exponential tilt gives
the bound, with no prime cancellation or hypothetical-zero limit used.

For `1/2 < u < 1`, set `q=u^(-1/4)` and `D_N=floor(q^N)`. Substituting
`X=D_N^3` and retaining the original normalization yields

\[
\boxed{\left|u^{N+1}\sum_{n\in T_N}a_N(n)K_{P,N}(3/2+iy,n)\right|
\le C(P)(3/4)^N,\qquad T_N\subseteq[0,D_N^3].}
\]

The coefficients and subsets may change arbitrarily with `N` under the
stated domination and support conditions. The geometric ratio follows
from `u*q^6/2=1/(2*sqrt(u)) < 3/4`.

This is not necessarily an additional support reduction at every zero
parameter. When the cubic cutoff is below the existing logarithmic
window's lower endpoint, the window mask already makes this sector zero.
The new estimate covers the overlap as well; the factorization theorem
applies to the surviving larger products in either case.

See `norm_normalized_sum_zetaArithmetic_cubic_product_le` and
`tendsto_normalized_sum_zetaArithmetic_cubic_product` in
[ZetaArithmeticSmallProduct.lean](../RiemannGaussian/ZetaArithmeticSmallProduct.lean).

## What survives above the cube

For every integer `n>D^3`, the finite factorization theorem proves:
either `n=ab` with `a>D` and `b>D`, or `n=pm` with `p` prime and `m<=D`.
For a nonzero original squarefree composite coefficient, the latter
cofactor must itself be prime, by the exact cancellation above.

The name `zetaBalancedFactorization` means only **both factors exceed
`D`**. It does not assert comparable factors. Squarefreeness supplies
coprime squarefree factors. No overlap information is erased.

For a hypothetical right-half zero, use the unchanged `P_rho`,
`u=3/2-Re(rho)`, actual prime sieve, and physical window mask. In
[ZetaRoughSquarefreeFactorSource.lean](../RiemannGaussian/ZetaRoughSquarefreeFactorSource.lean),
let `S_N`, `B_N`, and `U_N` denote the **already normalized** small-product,
two-factor, and unbalanced contributions. Lean proves the exact complex
partition and the source limit

\[
\text{original finite sum}=S_N+B_N+U_N,\qquad
|S_N|\le C(P_\rho)(3/4)^N,\qquad B_N+U_N\longrightarrow-m_\rho.
\]

`zetaRightHalfRoughSquarefreeUnbalancedProduct_support` gives the complete
actual support of `U_N`: `n=pq>D_N^3`, both primes exceed the quadratic
prime cutoff, `q<=D_N<p`, the original logarithmic window holds, and the
window coefficient is exactly `-log(q)`.

`abs_zetaRightHalfRoughSquarefreeFactorSource_sub_reflection_le` also keeps
the finite comparison to the original signed reflection `W_N`:

\[
\left|-\tfrac12\Re(B_N+U_N)-u^{N+1}W_N\right|
\le\tfrac12\bigl(C(P_\rho)(3/4)^N+E_{\rm window}(N)+E_{\rm Fourier}(N)\bigr).
\]

Both pre-existing errors tend to zero. No new error assumption is imposed.

The outstanding arithmetic task is a one-sided estimate on **the coupled
sum**. For example, any fixed `epsilon>0` with
`Re(B_N+U_N) >= -1+epsilon` on a cofinal subsequence contradicts the source,
since `m_rho>=1`. This conditional interface is
`false_of_cofinal_zetaRightHalfRoughSquarefreeFactor_bound`; its arithmetic
hypothesis has not been proved. Separate norm decay for both sectors would
be stronger than necessary and could lose useful cancellation.

## Validation scope

These modules are imported by the main library and locally validated with
warnings as errors, whole-project declaration lint, standard-axiom audits,
and generated-status checks. The all-height edge margin remains `1/(10 log(|t|+2))`; RH is open.
