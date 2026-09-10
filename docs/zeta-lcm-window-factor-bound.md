# Keeping both factor scales in the actual arithmetic response

Lean proves a stronger independent upper bound for every large
mixed-prime factor's genuine arithmetic response. The common-divisor
relation retains a factor-size saving that the preceding uniform bound
discarded. This saving applies to every positive integer, including
arbitrary repeated prime factors. In the actual physical window it
supports a larger budget for arbitrary finite complex coefficient
families. The collective signed bound required for RH remains open.

## The exact information retained

For a positive head divisor `d` and positive selected factor `P`, set
`L=lcm(d,P)` and `g=gcd(d,P)`. The identity `L*g=d*P` gives

\[
e^{-s\log L}e^{-s\log g}=e^{-s\log d}e^{-s\log P},\qquad
\log L-\log d=\log P-\log g.
\]

Both complex phases and the entire logarithmic companion remain in the
actual response. At `Re(s)>=1/2`, the intersection's companion norm
bound retains

\[
L^{-1/2}=\frac{\sqrt g}{\sqrt d\sqrt P}.
\]

The previous estimate retained the divisor scale and then removed the
factor scale. The new estimate keeps both until summing over common
divisors. For each positive common divisor `g`, the exact progression
sum has cutoff `floor(D/g)`, and

\[
\sum_{\substack{1\le d\le D\\g\mid d}}d^{-1/2}
=g^{-1/2}\sum_{1\le a\le\lfloor D/g\rfloor}a^{-1/2}
\le\frac{2\sqrt D}{g}.
\]

Consequently, with

\[
A(P)=P^{-1/2}\sum_{g\mid P}g^{-1/2},
\]

Lean proves

\[
\sum_{1\le d\le D}\operatorname{lcm}(d,P)^{-1/2}
\le2\sqrt D\,A(P).
\]

`A(P)` is exactly multiplicative on coprime products. For two distinct
primes its correction is bounded by `4/sqrt(p*q)`. The bound below
handles all positive integers without selecting a prime pattern.

## Pairing divisors gives a uniform factor saving

Pair each divisor of `P` with `P/d`. At least one partner is at most
`floor(sqrt(P))`; the reciprocal-square-root weight of the larger
partner is no greater than that of the smaller one. Thus

\[
\sum_{d\mid P}d^{-1/2}
\le2\sum_{1\le d\le\lfloor\sqrt P\rfloor}d^{-1/2}
\le4P^{1/4},\qquad A(P)\le4P^{-1/4}.
\]

This is an elementary sufficient bound, with no optimality claim.
In particular,

\[
D^2\le P\quad\Longrightarrow\quad\sqrt D\,A(P)\le4.
\]

Compiled entry points in
[NatLcmSqrtMass.lean](../RiemannGaussian/NatLcmSqrtMass.lean):

- `sum_Icc_dvd_inv_sqrt_eq`
- `inv_sqrt_lcm_eq`
- `sum_Icc_inv_sqrt_lcm_le`
- `lcmSqrtFactorMass_mul`
- `sum_divisors_inv_sqrt_le_four_mul_fourthRoot`
- `sqrt_mul_lcmSqrtFactorMass_le_four`

## The full signed arithmetic response inherits the saving

The actual response is an entire multiplier of `-zeta'` plus its
logarithmic companion multiplying `zeta`. The two multipliers now have
bounds `2*sqrt(D)*A(P)` and `2*sqrt(D)*A(P)*log(P)`, respectively.
The existing Cauchy argument transfers these bounds to every moment
order and polynomial filter, with one constant for each fixed ordinate
`|y|>1`.

Retain the better of this estimate and the earlier uniform estimate:

\[
\kappa(P)=\min\{3,(1+\log P)A(P)\}.
\]

For every finite complex family of positive mixed-prime factors, the
genuine convergent arithmetic sum satisfies

\[
\left|\sum_{P\in S}w_P\sum_n c_{D,P}(n)k_{p,N}(3/2+iy,n)\right|
\le C_y\sqrt D\,\|p\|_1\sum_{P\in S}|w_P|\kappa(P).
\]

Here `c_{D,P}(n)` is the literal Möbius-tail coefficient on multiples of
`P`. Each inner sum includes **all multiples of its factor**, with full
signs and phases; it is not an isolated coefficient at index `P`.
The factors may have arbitrary prime valuations and may overlap.

For `P>=D^2`, the complete filtered response is bounded by
`C_y*(1+log(P))*norm(p)_1`. Its earlier `sqrt(D)` growth is removed.

Compiled entry points in
[ZetaMoebiusLcmBound.lean](../RiemannGaussian/ZetaMoebiusLcmBound.lean):

- `zetaPrimeFeature_lcm_mul_gcd`
- `zetaMultipleLogOffset_eq_log_factor_sub_gcd`
- `norm_zetaMoebiusMultipleMultipliers_le_lcm`
- `exists_zetaMoebiusMultipleFamily_lcm_bound`
- `exists_zetaMoebiusMultipleFilter_large_factor_bound`

## The actual window supports a larger family budget

For any hypothetical right-half zero `rho`, keep
`u=3/2-Re(rho)` and `D_N=floor(q^N)`, where `q=u^(-1/4)`.
Every positive factor in `2*N/5<=log(P)<=8*N`, for `N>=1`, exceeds
`D_N^2`. This geometric separation was proved for the actual window,
so it is available here without an additional arithmetic assumption.

Every finite complex family of mixed-prime factors in that window obeys

\[
\left|\sum_{P\in S_N}w_{N,P}\sum_n c_{D_N,P}(n)k_{p,N}(3/2+i\operatorname{Im}\rho,n)\right|
\le C_\rho(1+8N)\sum_{P\in S_N}|w_{N,P}|.
\]

If its actual coefficient mass is at most `D_N^3*sqrt(D_N)`, then

\[
u^{N+1}\left|\sum_{P\in S_N}w_{N,P}\sum_n c_{D_N,P}(n)k_{p,N}(3/2+i\operatorname{Im}\rho,n)\right|
\le C_\rho(1+8N)(u^{1/8})^N\longrightarrow0.
\]

Lean checks the whole rate identity
`u*sqrt(q)*q^3=u^(1/8)` and proves that the linear prefactor still tends
to zero against this strict geometric decay. This improves the
implemented cubic coefficient budget for factors in the physical window.
No prime pattern or choice of complex coefficients is required.

Compiled entry points in
[ZetaMoebiusWindowFactorDecay.lean](../RiemannGaussian/ZetaMoebiusWindowFactorDecay.lean):

- `exists_zetaRightHalfWindowFactorFamily_bound`
- `exists_zetaRightHalfWindowFactorFamily_budget_bound`
- `tendsto_zetaRightHalfWindowFactorAllowance`
- `tendsto_zetaRightHalfWindowFactorFamily`

The budget is an explicit hypothesis on arbitrary families, not a proved
budget for a representation of the entire surviving source. In particular,
the result does not delete the union of every factor in the window:
overlap coefficients and their intersection factors would have to be
accounted for. The new bound preserves that distinction.

The remaining goal is still one independent strict upper bound on the
complete signed work below half the analytic multiplicity. The next
estimate must use the full collection's coupling, or identify it exactly
with a family whose cost fits a proved budget. The existing
[averaged Fourier source and its full error](zeta-averaged-symbol-window.md)
remain unchanged. The [all-height zero-free edge region](zeta-completion-reserve-zero-free.md)
is unchanged, and no additional zeros are excluded by this slice.

The next [complete prime-pattern sieve](zeta-quadratic-prime-sieve.md)
uses the multiplicative factor cost to pay for an actual simultaneous
union, including every overlap. It permits all selected primes through
a quadratic cutoff and transports the full signed source to the
remaining coefficients. Their independent upper bound is still open.
