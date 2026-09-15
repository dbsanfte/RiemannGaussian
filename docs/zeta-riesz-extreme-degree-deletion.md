# Bounding the physical-cutoff prime degrees

Lean now independently bounds and removes the complete actual class with
at least four prime factors at or above the physical cutoff, on
`0 < u < exp(-1/2)`. This includes degrees four and five inside the
[previously narrowed window](zeta-riesz-unfiltered-narrow-carrier.md).
The whole remaining carrier retains its negative multiplicity source.
Its independent signed lower bound remains open.

## Actual arithmetic data

The source coordinate and physical cutoff have not changed:

\[
u=\tfrac32-\beta,\qquad
D_N=\left\lfloor\frac{u^{-N}}{N+1}\right\rfloor,\qquad
X_N=(D_N+2)^2,\qquad L_N=\log X_N.
\]

Let `E_N(n)` be the distinct prime factors `p` of `n` satisfying `X_N ≤ p`.
For squarefree `n`, Lean proves

\[
|E_N(n)|L_N\le\log n.
\]

For every fixed `0<u<1`, the actual length eventually exceeds `cN` for
some `c>0`. Thus the narrowed support `log(n) ≤ 8N log(2)` permits only
finitely many extreme prime degrees, with a bound depending on `u`.
Moreover, sufficiently high degrees have independent **unnormalized**
geometric decay, uniformly over all changing finite selections.

## The stronger four-prime bound

Write the actual response over a finite set `S_N` as

\[
T_N(S_N)=\sum_{n\in S_N} C_{L_N}(n)K_{P,N}(3/2+i y,n).
\]

Here `C` is the original signed squarefree Riesz coefficient and `K` is
the complete factorial kernel for an arbitrary fixed complex polynomial
`P`. If every selected label has at least four extreme prime factors,
then, for `0<u<exp(-1/2)`, Lean proves eventually

\[
\left|u^{N+1}T_N(S_N)\right|
\le \left(4e^{-23/16}\right)^N
\,u\,A(P,1/4,65/64),\qquad 0<4e^{-23/16}<1.
\]

The tilt cost `A` retains every coefficient and factorial shift of `P`
and a genuinely convergent divisor-majorant mass. The bound is uniform
in `y` and the finite selection, with the original damped floor and
physical length. No hypothetical zero or unproved prime cancellation is
used. Its constants and starting order are not numerically evaluated.

The proof uses `L_N ≥ N` eventually, hence `log(n) ≥ 4N`, before
applying the existing general summed tilt. Keeping the source factor
`u^(N+1)` inside that estimate supplies the additional saving.

| Compiled result | Role |
| --- | --- |
| [`extreme_prime_log_budget`](../RiemannGaussian/ZetaRieszExtremePrimeCount.lean) | Exact prime-factor budget at the actual physical length. |
| [`exists_global_extreme_class_decay`](../RiemannGaussian/ZetaRieszExtremeDegreeBounds.lean) | For every fixed `0<u<1`, some high-degree class decays without source normalization. |
| [`eventually_norm_four_extreme_sum_le`](../RiemannGaussian/ZetaRieszFourExtremeBound.lean) | Explicit source-normalized bound for every changing finite four-or-more-prime class. |
| [`tendsto_narrow_sub_fourResidual`](../RiemannGaussian/ZetaRieszFourExtremeDeletion.lean) | Removes that actual class while retaining every earlier support cut. |
| [`tendsto_normalizedFourResidual`](../RiemannGaussian/ZetaRieszFourExtremeDeletion.lean) | The whole reduced carrier still tends to `-m_rho` at exposed zeros. |
| [`rh_of_exposed_fourResidual_floors`](../RiemannGaussian/ZetaRieszFourExtremeDeletion.lean) | Conditional Mathlib RH closure; the whole cofinal floor is an open premise. |

## What remains

On `1/2<u<exp(-1/2)`, each surviving nonzero label eventually has at
least two primes above `N^2` but at most three primes at or above `X_N`.
These are different thresholds. Intermediate primes `N^2<p<X_N` may
still be numerous and retain their full product phase and coupling to
the smooth cofactor. The earlier boundary-divisor identities remain
available; no phase-selected completion is licensed by this bound.

Outside the new interval the previous residual is unchanged. All older
component deletions retain their own parameter ranges, including the
condition `2u^2<1` on the complete smooth-factor restriction. The exact
real response is still the original signed coefficient times the
nonnegative factorial envelope times `cos(gamma log(n))`.

A cofinal floor at least `-c` with `c<1` for this **whole** remaining
response would contradict its negative multiplicity limit. Source
transport, exposed-zero selection and the resulting implication to
Mathlib RH are proved. The independent arithmetic floor is not proved.
This slice claims no RH proof, zero-free enlargement, numerical zero
bound or historical novelty.

The [supporting explorer](https://dbsanfte.github.io/RiemannGaussian/rh-proof/?endpoint=extreme-degree-deletion)
provides compiled statements, exact source lines, dependency paths and
transitive axiom audits. The default whole-carrier frontier stays unchanged.
