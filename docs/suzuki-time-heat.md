# Exact signed time heat and its completion boundary

The arithmetic target remains a one-sided subpolynomial lower bound for
the exact Suzuki potential, over all sufficiently large cutoffs. This
slice supplies a time-heat bridge and an independent boundary estimate;
it does not prove that arithmetic bound or a new zero exclusion.

## The actual signal and its contour

Write `S(u)` for `suzukiChebyshevLogAverageLaplaceSignal u` and
`F(z)` for its proved completed-xi Laplace continuation. At positive time,
`S(u)` is the exponential main term minus the complete prime hinge sum.
For `tau > 0`, define

\[
H_\tau S(a)=\frac1{\sqrt{4\pi\tau}}
  \int_0^\infty S(u)e^{-(a-u)^2/(4\tau)}\,du.
\]

`integral_suzukiTimeHeatResponse_vertical` proves, for every real center
`a` and every `sigma > 1/2`,

\[
2\pi H_\tau S(a)=\int_{\mathbb R}
 e^{az+\tau z^2}F(z)\,dy,\qquad z=\sigma+iy.
\]

Both integrals are absolutely convergent. The generic theorem
`integral_gaussianLaplace_vertical_eq_timeHeat` first proves Fubini for any
complex signal integrable after exponential damping, over its original
sigma-finite measure. It is not restricted to a weight family. The Suzuki
application discharges that integrability using the literal arithmetic
Laplace transform. No contour is moved through zeros in this theorem.

## The support-completion error is controlled

Let `J(u)` be `suzukiLegendreSignal u`, and retain its exact slope `c` and
intercept `C`. The normalized full-line heat of `J(u)-cu-C` is

\[
H_\tau S(a)+E_\tau(a),\qquad
E_\tau(a)=\frac1{\sqrt{4\pi\tau}}
 \int_{-\infty}^0 4e^{u/2}e^{-(a-u)^2/(4\tau)}\,du.
\]

This is `centeredSuzukiLegendre_timeHeat_eq`, with full integrability in
`integrable_centeredSuzukiLegendre_timeGaussian`. Before estimating the
boundary, the exact signed identity is retained.
`suzukiTimeHeatBoundary_bounds` proves unconditionally that

\[
0\le E_\tau(a)\le 4e^{-a^2/(4\tau)}\qquad(a\ge0).
\]

For every eventually positive schedule with `tau(a)/a -> 0`, the boundary
is eventually at most `4 exp(-a/4)` and tends to zero. The terminal theorem
is `tendsto_suzukiTimeHeatBoundary_zero_of_sublinear`.
`tendsto_suzukiTimeHeatBoundary_div_source_zero` further proves that this
actual error divided by the magnitude of any hypothetical right-half-zero
source tends to zero, for every such schedule. This estimate controls only
completion across time zero, not the remaining prime arithmetic.

## Which widths preserve the zero source?

For an actual zero `rho`, write `z_rho = rho-1/2 = delta+i*gamma` and let
`m` be its analytic multiplicity. At `z_rho != 0`, the heat response has
the exact local residue

\[
R_\rho(a,\tau)=e^{a z_\rho+\tau z_\rho^2}\frac{m}{z_\rho^2}.
\]

`tendsto_suzukiTimeHeatResponse_zero_residue` proves the local pole limit;
`suzukiTimeHeatZeroSource_ne_zero` proves the residue cannot vanish at a
finite width. Its exact magnitude is

\[
|R_\rho(a,\tau)|=
 \frac{m}{|z_\rho|^2}e^{a\delta+\tau(\delta^2-\gamma^2)}.
\]

Thus linear width `tau=kappa*a` changes the source's exponential rate to
`delta+kappa*(delta^2-gamma^2)`. It can suppress the source itself.
In contrast, `tendsto_log_norm_suzukiTimeHeatZeroSource_div_time` proves

\[
\frac{\log|R_\rho(a,\tau(a))|}{a}\longrightarrow\delta
\]

for every sublinear schedule `tau(a)/a -> 0`. For a right-half zero,
`z_rho != 0` follows already from `delta > 0`.

These statements concern each exact residue. They do not show that the
complete signed contour grows at that rate, bound interference between
zeros, justify an infinite residue expansion, or recover a pointwise floor
from a heat average. Those steps require further arguments.

## Remaining target

The time-heat identity can now be used without a missing support correction
or an untracked loss in an individual zero's source exponent. The central
open problem is still an independent bound for the complete signed
arithmetic response, strong enough to yield the unsmoothed potential's
subpolynomial lower allowance. The subsequent
[positive-delay recovery theorem](suzuki-controlled-recovery.md) now
controls recovery times independently. Passing from those endpoints to a
subpolynomial allowance on balanced minima remains a separate step, as
does the independent arithmetic depth bound. The existing `o(sqrt(N))`
estimate does not close this gap.
