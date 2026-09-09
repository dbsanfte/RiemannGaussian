# Pole jets and the moving Möbius tail

Cancelling the complete pole of the finite Möbius convolution now gives an
independent bound uniform in the moment order. The divisor cutoff can grow
exponentially while the normalized head tends to zero at a proved geometric
rate. The full contribution of any hypothetical right-half zero survives
in an explicit, convergent signed sum over composite products beyond that
cutoff.

This connects the actual local zero divisor and its polynomial filter to
the repository's finite Möbius prefixes. The remaining independent signed
estimate is open. There is no new zero exclusion or RH proof, and novelty
relative to the mathematical literature has not been established.

The subsequent [distinct-prime tail result](zeta-moebius-distinct-prime-tail.md)
independently bounds every prime-power contribution, uniformly in the
moving cutoff, at the same geometric error rate. The full remaining
source is carried by integers with at least two distinct prime factors.

## Why the full pole matters

Write

\[
M_D(s)=\sum_{1\le d\le D}\mu(d)d^{-s},\qquad
\zeta_0(s)=\zeta(s)-\frac1{s-1},
\]

where the removable value makes `zeta₀` entire. The finite convolution head
is `M_D(s)(-zeta'(s))`. Its pole has order two. The exact decomposition is

\[
M_D(s)(-\zeta'(s))
=G_D(s)+\frac{M_D(1)}{(s-1)^2}+\frac{M_D'(1)}{s-1},
\]

with the entire regular part

\[
G_D(s)=-M_D(s)\zeta_0'(s)
 +\frac{M_D(s)-M_D(1)-M_D'(1)(s-1)}{(s-1)^2}.
\]

Lean defines the last quotient by two analytic divided differences, so
its value at one is also justified. The exact decomposition and entire
extension are `zetaMoebiusHead_mul_neg_deriv_eq` and
`differentiable_zetaMoebiusHeadRegular`.

For signed factorial moments

\[
\mathcal M_n f(s)=\frac{(-1)^n}{n!}f^{(n)}(s),\qquad
\mathcal F_{P,N}(f;s)=\sum_k p_k\mathcal M_{N+k}f(s),
\]

the double pole contributes

\[
b^{N+2}\bigl((N+1)P(b)+bP'(b)\bigr),\qquad b=(s-1)^{-1}.
\]

`zetaMomentSequenceFilter_doublePole` proves this for every polynomial,
mode, and moment order. Both `P(b)=0` and `P'(b)=0` remove the complete pole
jet. A filter cancelling only the value leaves a derivative contribution.

Let `rho=beta+i gamma` be a nontrivial zero with `beta>1/2`, put
`u=3/2-beta` and `s₀=3/2+i gamma`, and let `P_rho` be the existing exact
local-divisor isolator. Define the promoted filter by

\[
\widetilde P_\rho(X)=
\frac{X-(s_0-1)^{-1}}{u^{-1}-(s_0-1)^{-1}}P_\rho(X).
\]

The denominator is nonzero. This exact factor kills the full pole jet
and preserves the selected source. Theorems
`zetaRightHalfPoleJetFilter_pole_jet` and
`tendsto_zetaRightHalfPoleJetFilter` discharge these facts for every such
zero, including its analytic multiplicity.

## The independent bound

A Cauchy circle of radius one or two around `s₀` stays at least one half
away from the pole. On the chosen circle the real part is at least minus
one, so the elementary coefficient bound `|mu(d)| <= 1` gives
`|M_D(s)| <= (D+1)^2`. Compactness bounds the entire `zeta₀'` there.
Cauchy's estimates then give

\[
|\mathcal M_n G_D(s_0)|\le C_\gamma(D+1)^2
\quad\text{for every }D,n.
\]

Consequently every polynomial killing the full pole jet satisfies

\[
|\mathcal F_{P,N}(M_D(-\zeta');s_0)|
\le C_\gamma(D+1)^2\sum_k|p_k|.
\]

These are `exists_zetaMoebiusHeadRegular_moment_bound` and
`exists_zetaMoebiusHeadFilter_bound`. They assume no Möbius cancellation
estimate and are uniform in both cutoff and moment order. The constant
depends on the ordinate; no uniform bound in height is asserted.

Choose the exact cutoff

\[
q=u^{-1/4}>1,\qquad D_N=\lfloor q^N\rfloor.
\]

Since `u q² = sqrt(u) < 1`, the theorem
`exists_zetaRightHalfPoleJetHead_bound` proves

\[
\boxed{
|u^{N+1}\mathcal F_{\widetilde P_\rho,N}(M_{D_N}(-\zeta');s_0)|
\le C_\rho(\sqrt u)^N.
}
\]

The constant is positive and independent of `N`. The floor is retained
exactly and `tendsto_zetaRightHalfPoleJetCutoff` proves `D_N` is cofinal.
The result removes a growing divisor head, not just a fixed finite prefix.

## The remaining arithmetic object

The actual tail coefficient is

\[
A_D(n)=\sum_{dk=n\atop d>D}\mu(d)\log k.
\]

For `Re s>1`, its Dirichlet series converges absolutely to

\[
T_D(s)=\left(\zeta(s)^{-1}-M_D(s)\right)(-\zeta'(s)).
\]

`LSeriesHasSum_zetaMoebiusLogTail` proves the convergence and value using
the literal Möbius tail and Dirichlet convolution. Higher moments give
the convergent arithmetic filter

\[
\mathcal T_{P,D,N}(s)=
\sum_{n\ge1}A_D(n)n^{-s}
 \sum_k p_k\frac{(\log n)^{N+k}}{(N+k)!}.
\]

`hasSum_zetaMoebiusLogTailFilter` verifies this exact signed series. The
underlying theorem `hasSum_signedTaylorMoment_LSeries` applies to arbitrary
Dirichlet coefficients in their half-plane of absolute convergence.

There are exact support restrictions:

* `A_D(n)=0` if `n < 2(D+1)`.
* For `D>=1`, `A_D(p)=0` for every prime `p`.

The first uses the vanishing `log 1` contribution and the strict divisor
cutoff. The second uses the two factorizations of a prime. These are
`zetaMoebiusLogTailCoefficient_eq_zero_of_lt` and
`zetaMoebiusLogTailCoefficient_prime`; they retain all surviving signs.

The exact head-tail identity and the independent head estimate give

\[
\boxed{
u^{N+1}\mathcal T_{\widetilde P_\rho,D_N,N}(s_0)
\longrightarrow -m(\rho).
}
\]

`tendsto_zetaRightHalfPoleJetTail_compositeSum` states this directly for
the literal convergent sum restricted to composites `n>=2(D_N+1)`.
`exists_zetaRightHalfPoleJetTail_error_bound` bounds the cost of replacing
the complete prime filter by this composite sum by `C_rho (sqrt u)^N`.

## What this gives the RH argument

Any hypothetical right-half zero forces its full multiplicity signal
into this moving large-divisor composite convolution. The finite head
cannot supply that signal. This identifies a specific signed bilinear
arithmetic quantity for the next estimate, with its replacement error
already bounded independently.

The theorem `zetaRightHalfPoleJetTail_eventually_negative` proves

\[
\Re\mathcal T_{\widetilde P_\rho,D_N,N}(s_0)
<-\frac{m(\rho)}{2u^{N+1}}
\quad\text{eventually}.
\]

An independent opposite inequality for arbitrarily large `N` would
contradict this selected zero. That inequality is not proved. Composite
support alone supplies no sign or cancellation bound, and the filter's
complex coefficients and the phase `n^(-i gamma)` must stay coupled in
the next arithmetic argument. The constants and asymptotic onset are
pointwise in the selected zero, with no effective uniform onset claimed.

## Local verification

The five modules are imported by `RiemannGaussian.lean`. Verification
includes direct warnings-as-errors checks, a focused and full build,
whole-project declaration lint, source and whitespace checks, and a
root-imported audit of every new public theorem's axioms. Only the
standard logical axioms `propext`, `Classical.choice`, and `Quot.sound`
are permitted. Changes remain local under the user's commit hold.
