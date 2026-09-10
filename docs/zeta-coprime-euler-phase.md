# Prime-phase gains and uniform control of the coprime Euler channels

Lean now controls both original finite coprime Euler channels uniformly
over the actual rough physical support and the whole analytic contour.
The value multiplier tends to **one**, while its logarithmic companion
tends to **zero**. A separate theorem charges the full coefficient mass
when these errors are used in a weighted family. The independent signed
bound for the complete arithmetic response remains open; no additional
zero is excluded.

All new entry points are in namespace `RiemannGaussian.CoprimeEulerPhase`
in [ZetaCoprimeEulerPhase.lean](../RiemannGaussian/ZetaCoprimeEulerPhase.lean).
The [coupled large-product source](zeta-rough-squarefree-factor-source.md)
is unchanged.

## What prime structure contributes before taking a norm

The repository's original multiplier is

\[
E_P(s)=\sum_{d\mid P}\mu(d)d^{-s}.
\]

For every squarefree `P`, `coprimeEuler_eq_product` identifies it exactly
with the complete prime product `prod_{p|P}(1-p^{-s})`. No intersection
term is discarded. Put `w_p=exp(-Re(s)*log(p))`. The exact square identity is

\[
|1-p^{-s}|^2=(1+w_p)^2-2w_p(1+\cos(\Im(s)\log p)).
\]

Define the nonnegative gain

\[
g_p(s)=\frac{w_p(1+\cos(\Im(s)\log p))}{(1+w_p)^2}.
\]

`norm_coprimeEuler_le_with_phase` retains all these gains:

\[
|E_P(s)|\le\prod_{p\mid P}(1+w_p)
\exp\left(-\sum_{p\mid P}g_p(s)\right).
\]

Two distinct primes cannot simultaneously have cosine `-1` at the same
ordinate. Otherwise their logarithms would satisfy a positive integer
relation, forcing equal positive powers of distinct primes. Lean derives
the contradiction from prime factorization. Thus `pair_phaseGain_pos`
proves a strict joint gain everywhere, and compactness gives a positive
uniform gain on any fixed compact complex region.

`exists_uniform_coprimeEuler_gain` applies this gain to every squarefree
`P` containing a specified pair. Its constant depends on that pair and
the compact region. It is not a constant uniform over moving primes.
These arguments make no mathematical-priority claim.

## The scale on the actual surviving support

For the original hypothetical right-half zero, use the unchanged
quadratic prime cutoff

\[
c_\rho=\log(q_\rho)/8>0,\quad A_N=\lfloor c_\rho N\rfloor,
\quad R_N=A_N^2.
\]

If the actual rough-window coefficient at `n` is nonzero and `P` divides
`n`, then `P` is squarefree, every prime dividing `P` exceeds `R_N`, and
`log(P)<=log(n)<=8N`. Consequently, for `Re(s)>=sigma>=0` and `R_N>=1`,

\[
\sum_{p\mid P}p^{-\Re s}
\le b_{\rho,\sigma}(N):=
\frac{8N}{\log2}\exp(-\sigma\log R_N).
\]

This is `actual_factor_feature_mass_le`. The proof retains the exact
prime-factor logarithmic mass and bounds its cardinality by
`log(P)/log(2)`. For every fixed `sigma>1/2`, `tendsto_roughEulerBudget`
proves `b_{rho,sigma}(N)->0`, with the floor included. Its quantitative
step, once `A_N>=1`, is

\[
b_{\rho,\sigma}(N)
\le\frac{16}{c_\rho\log2} A_N^{-(2\sigma-1)}.
\]

All product cross terms are then controlled by

\[
|E_P(s)-1|\le\exp(b_{\rho,\sigma}(N))-1.
\]

This holds simultaneously for every eligible `n`, every divisor `P`,
and every argument in the stated right half-plane. In particular, no
favourable contour point is selected.

The phase gains also satisfy `sum_{p|P} g_p(s)<=2*b_{rho,sigma}(N)`.
`eventually_actual_factor_phaseGain_lt` proves their uniform convergence
to zero over these moving factors. The fixed-pair positivity theorem
therefore does not supply a fixed source-scale reserve on the actual
rough factors.

## The logarithmic channel is included

The original logarithmic multiplier is

\[
L_P(s)=\sum_{d\mid P}\mu(d)\log(d)d^{-s}=-E_P'(s).
\]

`hasDerivAt_coprimeEuler` proves this exact derivative relation. For the
original circle centred at `3/2+i*Im(rho)` and any fixed radius `r<1`,
put `delta=(1-r)/2` and `sigma=3/2-(1+r)/2=1-r/2>1/2`.
Cauchy's derivative estimate on the slightly larger circle controls
the logarithmic channel too. The joint result is

\[
\boxed{
|E_P(s)-1|+|L_P(s)|\le
\eta_{\rho,r}(N):=
(1+1/\delta)\bigl(\exp(b_{\rho,\sigma}(N))-1\bigr)
\longrightarrow0.
}
\]

The bound applies throughout the full closed disc, for every divisor of
every nonzero actual rough-window coefficient. Its entry points are
`actual_cauchy_factor_Euler_channels_le` and
`tendsto_roughEulerChannelAllowance`. These are independent bounds for
the literal multipliers; the multiplicity-source limit is not used.

## What still has to be paid in the complete response

`norm_weighted_actual_Euler_channels_le` makes the accumulation cost
explicit. For any finite complex family with eligible divisors and
contour arguments,

\[
\left|\sum_i c_i(E_{P_i}(s_i)-1)\right|
+\left|\sum_i c_iL_{P_i}(s_i)\right|
\le\eta_{\rho,r}(N)\sum_i|c_i|.
\]

The finite-prefix multipliers and family weights may grow. The subsequent
[rough coprime-factor family theorem](zeta-rough-coprime-factor-decay.md)
controls the complete prefix complexity uniformly and proves decay for
eligible complete-sector families with coefficient mass through `D_N^2`.
Representing the actual survivor with controlled coverage and restrictions
remains necessary. Neither the full coupled arithmetic
sum nor the prime-avoidance Euler product over all selected small primes
is bounded by this result. The controlled factors here are the finite
coprime multipliers belonging to divisors of the surviving physical
integers.

The required cofinal one-sided bound for the coupled large-product sum
remains open. The all-height zero-free edge margin remains
`1/(10 log(|t|+2))`.

## Verification and research scope

The module is imported by the main library and locally checked with
warnings as errors, full declaration lint, standard-axiom audits and
generated-status checks.

The research check also examined the
[Gonek–Hughes–Keating hybrid product](https://arxiv.org/pdf/math/0511182):
its unconditional representation retains a separate product over zeros,
so replacing that product by a statistical model would not provide the
required pointwise bound. Gonek's
[finite Euler-product approximation results](https://arxiv.org/pdf/0704.3448)
explicitly distinguish RH-dependent approximation statements and their
converses. Neither paper is used as an unproved Lean premise or as a
replacement for the remaining arithmetic inequality.
