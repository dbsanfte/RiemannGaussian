# Controlled recovery of the actual Suzuki signal

Lean proves an unconditional recovery-time estimate for the literal signal
`S = suzukiChebyshevLogAverageLaplaceSignal`:

\[
\forall a\text{ sufficiently large},\quad
\exists u\in[a,4096a],\qquad S(u)>0.
\]

The terminal theorem is
`eventually_exists_pos_suzukiSignal_between_time_multiples` in
[`SuzukiControlledRecovery.lean`](../RiemannGaussian/SuzukiControlledRecovery.lean).
The integer-scale version places a positive value in `[n/32,64*n]` for
every sufficiently large natural `n`. The thresholds are existential;
the interval factors are exact, deliberately loose constants. Time is
logarithmic in the physical prime cutoff.

This controls how long recovery can take. It does not bound the depths of
the intervening negative excursions or exclude any additional zeta zero.

The [variable-damping extension](suzuki-relative-recovery.md) now replaces
4096 by every fixed `K > 1`, with a threshold that may depend on `K`.
It also removes the fixed factor from the balanced-cell exponent transfer.
The original unit-damping proof below remains available at its stated scope.

## Exact positive delay cancellation

For any nonreal complex node `p = delta + i*gamma`, put

\[
h_p=\frac{\pi}{|\gamma|},\qquad w_p=e^{\delta h_p},\qquad
A_p f(t)=\frac{f(t)+w_p f(t-h_p)}{1+w_p}.
\]

The positive weights make this a convex average. Its full complex Laplace
multiplier is

\[
K_p(z)=\frac{1+w_p e^{-zh_p}}{1+w_p},\qquad K_p(p)=0.
\]

[`PositiveDelayAveraging.lean`](../RiemannGaussian/PositiveDelayAveraging.lean)
proves exact cancellation, entire analyticity, causal support preservation,
Laplace integrability, and the exact transform for every finite node list.
It also proves that some original value within the finite backward delay
span is at least the averaged value. No numerical coefficients are selected.

The shifted actual zeros `p_rho = rho-1/2` are nonreal by the repository's
eta-measure theorem. Take any finite list containing the genuine zero
window through height `T >= 5/4`. Every required cancellation assumption
is discharged by that finite window. Extra delay factors are permitted.

## A bound for the complete signed moments

Let `f_L` be the delayed average of the causal extension of `S`, and let
`K_L` be its full multiplier. The actual completed Laplace continuation
`F` obeys

\[
\int_{\mathbb R} f_L(t)e^{-zt}\,dt=K_L(z)F(z)
\qquad(\Re z>1/2).
\]

The genuine finite principal-part decomposition, multiplied by `K_L`,
has an analytic numerator `Q` on the selected slab. At each removed pole,
the product is the entire divided difference of `K_L` times the actual
zero multiplicity. This retains the exact arithmetic response and
justifies removal at the divisor, rather than simply omitting its terms.

The disk of radius `5/4` around `1` lies in the regularized slab and
contains the origin. The existing double-pole moment theorem therefore
gives a constant `C_L > 0` such that, for every natural `n`,

\[
\left|M_{L,n}+c(n+1)\right|\le C_L,
\qquad
M_{L,n}=\int_{\mathbb R} f_L(t)\frac{t^n e^{-t}}{n!}\,dt,
\]

where `c = suzukiArchimedeanSlopeConstant < 0`. The linear coefficient
is independent of the delay family; the error constant may depend on it.
This is `exists_suzukiPositiveDelayGammaMoment_uniform_error` in
[`SuzukiPositiveDelayMoments.lean`](../RiemannGaussian/SuzukiPositiveDelayMoments.lean).
`exists_suzukiZeroWindowDelayGammaMoment_uniform_error` supplies an exact
zero-window list and discharges the covering premise.

[`SignedLaplaceMoments.lean`](../RiemannGaussian/SignedLaplaceMoments.lean)
justifies every derivative under the signed integral from actual
exponential integrability. The complex moment identity is retained before
the real bound is taken. In particular, `M_{L,n}` tends to positive infinity.

## Independent localization of the moment

For a causal real signal `f` with

\[
B_f=\int_{\mathbb R}|f(t)e^{-3t/4}|\,dt<\infty,
\]

[`GammaMomentRecovery.lean`](../RiemannGaussian/GammaMomentRecovery.lean)
proves that nonpositivity throughout `[n/16,64*n]` forces

\[
\int_{\mathbb R}f(t)\frac{t^ne^{-t}}{n!}\,dt
\le
B_f\left[\left(\frac{e^{1/4}}4\right)^n
+\left(8e^{-8}\right)^n\right].
\]

Both geometric ratios are proved strictly below one. This estimate uses
the exponential-series inequality on the two time tails, preserving the
signed middle integral until its assumed nonpositivity is used. It needs
no pointwise growth hypothesis and no normalization or concentration
assumption about an abstract probability model.

For `f_L`, the actual weighted integral is finite. Its moments diverge, so
there must be a positive delayed value in each sufficiently late central
interval. Positive delay averaging transfers it to the original `S`.
The finite backward span is absorbed into the interval constants.

## What this supplies to the arithmetic frontier

The exact Legendre signal is `J(u)=S(u)+c*u+C`, with the retained
Archimedean intercept `C`. The companion terminal theorem
`eventually_exists_suzukiLegendre_recovery_between_time_multiples` proves

\[
\exists u\in[a,4096a],\qquad J(u)>4096ca+C
\]

at every sufficiently large start time. Thus the recovery level is only
linear in logarithmic time, and its time is controlled independently.
This supplies the recovery-time input for trapping deep excursions
between endpoints and passing to actual balanced-cell minima. The
[subsequent localized criterion](suzuki-balanced-subpolynomial.md) now
completes that transfer for a growing subpolynomial allowance, with the
finite head, affine correction, and entropy error included.

The independent arithmetic depth bound is still open. The delay filter
deliberately removes selected zero modes to establish recovery, so its
moment estimate must not be represented as bounding the original zero
source or as the required RH contradiction. The source-preserving heat
identities and the exact signed prime interactions remain available for
the depth argument.
