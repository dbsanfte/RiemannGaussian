# All extensions that remain in the core

[`ZetaRieszCoreExtensions`](../RiemannGaussian/ZetaRieszCoreExtensions.lean)
strengthens the [small-factor audit](zeta-riesz-small-descendants.md).
Every selected squarefree extension of a balanced triple that remains in
the original core has vanishing mass **relative to its base atom**.
There is no polynomial upper cutoff on the inserted prime. This is a
bound on an actual arithmetic component, not an independent floor for
the whole signed carrier.

Let `m=p*q*r` be a product of three distinct actual primes, with

\[
2N\le\log m,\qquad
\log p,\log q,\log r\le67N/100,\qquad
137N/100\le L\le7N/5.
\]

Take any finite set `D` of nonunit extensions `a` such that `m*a` is
squarefree and `log(m*a)<=203N/100`. Further physical, count and support
conditions can remain in `D`. The original allocation remains in
`residualCoefficient`; the height is arbitrary and the phase is never
frozen or replaced by a prime-density phase.

## Exact cancellation and a quantitative prime bound

`core_extension_geometry` forces `log(a)<=3N/100`. Consequently all
three pair cutoffs saturate: `log(p*q*a)<=L`, and similarly for the
other pairs, while `L<=log(m)`. The previously proved exact insertion
identity gives

\[
\mathcal R_L(ma)=
\begin{cases}\log a,&a\text{ prime},\\0,&a\text{ composite}.\end{cases}
\]

Every composite extension therefore vanishes, with no bound on its
prime count. For the remaining ordinary primes, `prime_log_mass_le`
proves from Chebyshev's elementary upper bound and finite summation by
parts that

\[
\sum_{a\in D,\ a\text{ prime},\ \log a\le x}
\frac{\log a}{a}\le\log4\,(1+x),\qquad x\ge0.
\]

The original factorial kernel supplies more than its reciprocal bound.
If `delta*N <= log(a) <= 3N/100`, then
`norm_kernel_extension_geometric` proves

\[
\|K_N(ma)\|\le
e^{-\delta^2N/24}a^{-1}\|K_N(m)\|.
\]

This follows from its exact multiplicative transport and an elementary
quadratic upper bound for `log(1+x)`. It retains the factorial curvature
instead of replacing it by its tangent bound.

Write `E_N` for the selected extension sum with its literal residual
coefficients and complex kernels. Splitting at `log(a)=delta*N` gives

\[
\|E_N\|\le2\log4\,[1+\delta N+
(1+3N/100)e^{-\delta^2N/24}]\,\|K_N(m)\|.
\]

For the base atom `B_N`, the existing allocation estimate eventually
gives `1-boundedShare>=1/2`, hence `||B_N||>=N||K_N(m)||/4`.
`relative_extensions_split` then proves the explicit bound

\[
\boxed{\ \|E_N\|\le b_N(\delta)\|B_N\|,\qquad
b_N(\delta)=12\left[\frac1N+\delta+
\left(\frac1N+\frac3{100}\right)e^{-\delta^2N/24}\right].\ }
\]

For any `epsilon>0`, take `delta=epsilon/48`. The budget tends to
`epsilon/4`. `eventually_extensions_relative_small` proves that the
relative mass is eventually at most `epsilon`, uniformly over all the
displayed choices, even moving heights and selected sets.

For a finite check, `split_budget_lt_thousandth` proves
`b_N(1/50000)<1/1000` for `N>=10^12`.
`dyadic_split_budget_lt` supplies that budget from index `j=32` on the
unchanged original schedule. **The chamber and allocation hypotheses
are still required at the chosen index.** Their eventual availability
does not assert that all hold already at `j=32`.

The actual prime boxes in the earlier phase audits eventually satisfy
this sharper `67N/100` chamber
(`eventually_prime_boxes_in_core_chamber`). No model logarithms are
substituted for primes in these theorems.

## What this says about the joint floor

`joint_signed_bounds` retains any signed complement `W` verbatim:

\[
\Re(W+B_N)-\epsilon\|B_N\|
\le\Re(W+B_N+E_N)
\le\Re(W+B_N)+\epsilon\|B_N\|.
\]

If `Re(B_N)<=-||B_N||/2`, then `joint_negative_block` gives an upper
bound `Re(W)+(epsilon-1/2)||B_N||`. Even the complete set of extensions
remaining inside the core cannot itself neutralize that base atom's
fixed negative phase fraction.

This does **not** give source-normalized decay: the population of base
triples can still have growing absolute mass. Nor does it control
cancellation between different large-prime configurations, phase sectors
or radial regions. The independent joint `-79/1000-o(1)` floor remains
open. No new carrier or zero exclusion is claimed.

## Optional density diagnostic

The [probe](../scripts/probe_riesz_core_extensions.py) and its
[output](riesz-core-extensions-probe.json) retain the exact factorial
ratio and moving length on the equal-logarithm model base `log(m)=2N`.
They replace the inserted-prime measure by its ordinary density and
omit allocation and additional masks. They are **not** a prime-sum
transport, a certified quadrature or a source-scale bound.

The modeled relative mass is about `0.0464,0.0423,0.0303,0.0160` for
`N=1024,4096,16384,65536`. Its apparent `N^(-1/2)` scale motivated
retaining factorial curvature. The Lean theorem proves relative
vanishing using actual Chebyshev bounds; it does not claim that sharper
model rate. This optional probe is outside routine CI.
