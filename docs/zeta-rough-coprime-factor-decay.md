# Uniform decay for complete coprime-factor families

Lean now bounds the **full finite-prefix response**, uniformly for moving
factors that divide the actual rough physical support. This includes factors
throughout the physical divisor range, beyond the earlier condition
`P^2<=D_N`. Arbitrary finite complex families with total coefficient mass
at most `D_N^2` have independently vanishing normalized response.

These are complete coprime-factor sectors, including all their multiples.
The exact weighted coverage identity retains overlaps and extra multiples.
No family within the proved budget is yet shown to represent the complete
surviving rough squarefree sum. Its signed bound remains open, and no
additional zero is excluded.

All entry points below are in namespace `RiemannGaussian.RoughCoprimeFactor`
in [ZetaRoughCoprimeFactorDecay.lean](../RiemannGaussian/ZetaRoughCoprimeFactorDecay.lean).

## The prime structure controls the actual complexity

Use the unchanged parameters

\[
u=3/2-\Re\rho\in(1/2,1),\quad q=u^{-1/4},\quad
D_N=\lfloor q^N\rfloor,\quad R_N=\lfloor N\log(q)/8\rfloor^2.
\]

For every divisor `P` of an integer with nonzero actual rough-window
coefficient, squarefreeness and the complete prime exclusions give

\[
\tau(P)=2^{\omega(P)},\qquad
\omega(P)\log R_N\le\log P\le8N.
\]

Here `tau` counts divisors and `omega` counts distinct prime factors.
The original complete response estimate charges

\[
\mathcal C(P)=\tau(P)^2(1+2\log P).
\]

`actual_complexity_le` proves the uniform bound, once `R_N>1`,

\[
\boxed{\mathcal C(P)\le(1+16N)
 \exp\!\left(\frac{16\log2}{\log R_N}N\right).}
\]

Because the rounded prime cutoff tends to infinity, for every fixed `b>1`
the right side is eventually at most `(1+16N)*b^N`, simultaneously for
**all** such `P`. This is `eventually_actual_complexity_le`; neither the
factor nor its host integer is fixed before the limiting argument.
The result uses elementary prime factorization, without a prime-distribution
or Möbius-cancellation assumption and without a mathematical-priority claim.

## The bound reaches complete response families

Write `F_{D,P,N}` for the existing `zetaMoebiusFactorFilter`, evaluated at
the original centre `3/2+i*Im(rho)` with the unchanged pole-jet polynomial.
For mixed-prime `P` it is the genuinely convergent series

\[
F_{D,P,N}=\sum_n
 \mathbf1_{P\mid n,\ (P,n/P)=1}\,c_D(n)K_N(n),
\]

where `c_D` is the original signed Möbius logarithmic tail coefficient and
`K_N` retains every complex moment coefficient and physical phase.

The earlier full-response bound is
`norm(F_{D,P,N})<=C_rho*D*C(P)`, with its constant independent of `P,D,N`.
The new complexity estimate turns it into a bound for an arbitrary finite
family `S_N` and complex weights `w_N(P)`:

\[
\boxed{
\left|u^{N+1}\sum_{P\in S_N}w_N(P)F_{D_N,P,N}\right|
\le C_\rho(1+16N)\bigl(u^{1/8}\bigr)^N\longrightarrow0,
}
\]

provided each factor divides some nonzero actual rough-window coefficient
and the explicitly charged mass satisfies

\[
\sum_{P\in S_N}|w_N(P)|\le D_N^2.
\]

There is one eventual threshold for all eligible families. The proof uses
`b=sqrt(q)` in the complexity estimate and the exact identity
`u*sqrt(q)*q^3=u^(1/8)<1`. Lean names this rate `zetaMoebiusCubicRate u`.
The factors can move anywhere in the eligible divisor range; no inequality
`P^2<=D_N` is needed.

The entry points are `exists_actual_factor_family_budget_bound`,
`tendsto_actual_factor_family`, and
`tendsto_actual_factor_family_arithmetic`. The last identifies the result
with the literal sector series, with positivity, mixed-prime eligibility,
absolute convergence and every original cutoff accounted for.

## What the weighted family actually covers

The public function `coverage` keeps the complete overlap information:

\[
\chi_{S,w}(n)=\sum_{P\in S}
 w(P)\mathbf1_{P\mid n,\ (P,n/P)=1}.
\]

`sum_sectorCoefficient_eq_coverage` and `hasSum_coverage` prove exactly

\[
\sum_{P\in S}w(P)F_{D,P,N}
=\sum_n c_D(n)\chi_{S,w}(n)K_N(n).
\]

The terminal theorem `tendsto_actual_coverage` gives independent decay of
this genuine original arithmetic sum for every eligible moving family
within the mass budget. It retains all complex phases and signed overlaps.

To apply it to the remaining RH target, the coverage would have to match
the desired rough squarefree mask, or differ by an independently controlled
signed error. Restricting each sector to the physical window or to squarefree
rough multiples is not free: the complete-series estimate can use terms
outside those restrictions. Summing one factor for each physical integer
also does not establish the required `D_N^2` mass budget.

There is an exact obstruction to compressing the semiprime part with these
mixed-prime sectors. `coverage_semiprime` proves, for every such family,

\[
\chi_{S,w}(pq)=
\begin{cases}w(pq),&pq\in S,\\0,&pq\notin S,\end{cases}
\]

because a mixed-prime divisor of `pq` must be `pq` itself. Hence
`card_semiprimes_le_mass_of_coverage_one` proves that exact coverage of any
finite set `T` of semiprimes requires

\[
|T|\le\sum_{P\in S}|w(P)|.
\]

This applies to every coefficient choice in this representation. It does
not rule out an approximation with an independently controlled signed
error, a different representation, or cancellation between the large-product
sectors. No asymptotic count of the actual semiprime set is proved here.

This sharpens the [Euler-channel component bound](zeta-coprime-euler-phase.md)
by controlling the full prefix complexity for the stated family class.
It does not remove the [coupled large-product source](zeta-rough-squarefree-factor-source.md).
The [global unit-divisor comparison](zeta-rough-squarefree-unit-divisor.md)
still identifies the remaining full-sum obstruction with logarithmically
weighted rough squarefree composites. The ordinary-prime correction must
remain explicit when completing that sum.

## Validation scope

The module is imported by the main library. The slice is checked locally
with warnings as errors, focused and full builds, whole-root declaration
linters, all public theorem axiom audits, a tracked-and-untracked source
scan, project lint and deterministic generated-status checks. The all-height
edge margin remains `1/(10 log(|t|+2))`; RH is open.
