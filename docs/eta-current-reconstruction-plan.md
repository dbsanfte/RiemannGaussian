# Completed eta current reconstruction and the weighted arithmetic estimate

The user authorized the full objective on 2026-09-06: **reconstruct the
original leading current and prove the uniform weighted arithmetic
estimate**. The objective remains active until both parts are proved and
verified. The completed [signed endpoint package](eta-signed-endpoint-theorem-plan.md)
provides the actual support, gap, phase, Gaussian, and mixed-matrix inputs.

## Actual target and current status

Write `J_rho(N)` for the existing, unchanged
`pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N`. Its literal kernel is the
completed head at analytic multiplicity one and the completed adjacent-moment
kernel otherwise. In the head branch the physical first time is the shifted
coordinate plus `pairedEtaLogTailCutoff(N+1)`.

The arithmetic target is a bound for

\[
 S_\rho(K)=\sum_{N<K}(2N+1)|J_\rho(N)|
\]

uniform in the upper cutoff `K`, for every actual nontrivial zeta zero.
Any allowed dependence on the zero, analytic multiplicity, and completion
factors must be explicit. This must establish the existing universal
first-absolute-moment summability statement, whose equivalence to RH is
already proved in `EtaEnergyLeadingFluxKernel.lean`. Neither that arithmetic
bound nor RH is currently proved. Reconstruction alone does not complete
the objective.

| Obligation | Evidence | Status |
| --- | --- | --- |
| Integrate the ordered return over the entire actual gap | `integrable_leadingCurrent_gapReturn_prod`, `pairedEtaLeadingCurrentIntegratedGapReturn_eq_prod`, and `pairedEtaLeadingCurrentIntegratedTwoTransition_eq_neg_gapReturn` in [EtaIntegratedGapReturn.lean](../RiemannGaussian/EtaIntegratedGapReturn.lean). | Proved for nonnegative tilts with positive sum, positive widths, and measurable phases. |
| Normalize the actual return and reconstruct the original current | Positive gap mass and dominated broad-heat limit in [EtaBroadGapReturn.lean](../RiemannGaussian/EtaBroadGapReturn.lean); `pairedEtaLeadingCurrent_gapReturn_reconstruction` in [EtaLeadingCurrentReconstruction.lean](../RiemannGaussian/EtaLeadingCurrentReconstruction.lean). | Proved as iterated limits at every fixed zero and cutoff. |
| Quantify the dependence of reconstruction on the arithmetic cutoff | Exact multiplier and signed defect in [EtaGapReturnMultiplier.lean](../RiemannGaussian/EtaGapReturnMultiplier.lean); `pairedEtaLeadingCurrentNormalizedGapReturn_error_le` and its small-tilt bound in [EtaCurrentReconstructionError.lean](../RiemannGaussian/EtaCurrentReconstructionError.lean). | Proved with the actual absolute kernel mass and physical endpoint retained. |
| Control the completed absolute kernel masses across cutoffs | The actual measure bounds in [EtaFiniteCurrentMeasureBounds.lean](../RiemannGaussian/EtaFiniteCurrentMeasureBounds.lean), completed envelopes in [EtaCurrentKernelEnvelope.lean](../RiemannGaussian/EtaCurrentKernelEnvelope.lean), and `pairedEtaLeadingCurrentAbsoluteKernelMass_le` in [EtaCurrentKernelMass.lean](../RiemannGaussian/EtaCurrentKernelMass.lean). | Proved with an explicit completion-dependent constant and logarithmic-over-cutoff bound. |
| Choose simultaneous heat and tilt parameters with summable weighted reconstruction error | `pairedEtaLeadingCurrentScheduledGapReturn_weighted_error_le` in [EtaCurrentReconstructionSchedule.lean](../RiemannGaussian/EtaCurrentReconstructionSchedule.lean) and the summability and finite-prefix stability theorems in [EtaCurrentWeightedReconstruction.lean](../RiemannGaussian/EtaCurrentWeightedReconstruction.lean). | Proved with a schedule independent of the zero and a finite completion- and multiplicity-dependent error budget. |
| Compare the actual continuous gap return with composed Gaussian heat | Full-line composition in [EtaTiltedHeatComposition.lean](../RiemannGaussian/EtaTiltedHeatComposition.lean) and `pairedEtaLeadingCurrentIntegratedGapReturn_eq_composed_sub_corrections` in [EtaCurrentFullHeatComparison.lean](../RiemannGaussian/EtaCurrentFullHeatComparison.lean). | Proved with both support and nonpositive-time corrections; all three-time integrals converge even at zero tilt. No cancellation estimate follows from the identity alone. |
| Reconstruct at zero tilt with controlled actual-gap normalization | Arithmetic balance in [EtaDecreasingGapMass.lean](../RiemannGaussian/EtaDecreasingGapMass.lean), Gaussian mass and translation bounds in [EtaGaussianGapMass.lean](../RiemannGaussian/EtaGaussianGapMass.lean), exact multiplier in [EtaZeroTiltGapMultiplier.lean](../RiemannGaussian/EtaZeroTiltGapMultiplier.lean), and the two completed branches in [EtaZeroTiltCurrentReconstruction.lean](../RiemannGaussian/EtaZeroTiltCurrentReconstruction.lean). | Proved using the entire actual gap, without extending the positive-tilt Laplace normalization to zero. |
| Preserve the weighted frontier with zero tilt and quadratic width | `summable_oddEndpoint_mul_norm_pairedEtaLeadingCurrentZeroTiltScheduledReturn_error` and `pairedEtaLeadingCurrentZeroTiltScheduledReturn_firstMoment_stability` in [EtaZeroTiltWeightedReconstruction.lean](../RiemannGaussian/EtaZeroTiltWeightedReconstruction.lean). | Proved at width `2(N+1)²`, with explicit finite error budget and no exponential tilt amplification. |
| Evaluate the literal colour primitive and broad Gaussian gap term | `pairedEtaLogColourPrimitive_wallis_error_le` in [EtaLogColourPrimitive.lean](../RiemannGaussian/EtaLogColourPrimitive.lean), the exact signed remainder in [EtaGaussianColourRemainder.lean](../RiemannGaussian/EtaGaussianColourRemainder.lean), and `pairedEtaGaussianGapMass_wallis_expansion_error_le` in [EtaGaussianGapExpansion.lean](../RiemannGaussian/EtaGaussianGapExpansion.lean). | Proved with the evaluated Wallis constant, exponential primitive error `9 exp(−t)`, and uniform remainder `2(1+c)³/h³`. |
| Identify the first broad-heat coefficient of the original current | The normalized expansion in [EtaZeroTiltFirstCorrection.lean](../RiemannGaussian/EtaZeroTiltFirstCorrection.lean) and `pairedEtaLeadingCurrentZeroTiltGapReturn_midpoint_error_le_arithmetic` in [EtaCurrentMidpointCorrection.lean](../RiemannGaussian/EtaCurrentMidpointCorrection.lean). | Proved in both actual multiplicity branches, retaining an exact signed defect and an explicit inverse-square-width error. Arithmetic cancellation of the midpoint coefficient remains open. |
| Evaluate the midpoint coefficient in finite eta arithmetic | The complex integral identity in [EtaCurrentFiniteMomentPair.lean](../RiemannGaussian/EtaCurrentFiniteMomentPair.lean), the repeated-zero formula in [EtaCurrentAdjacentMidpoint.lean](../RiemannGaussian/EtaCurrentAdjacentMidpoint.lean), and the translated head formula in [EtaCurrentHeadMidpoint.lean](../RiemannGaussian/EtaCurrentHeadMidpoint.lean). | Proved with both physical cutoff origins, all centered orders, and complex channel orientation retained. |
| Apply completed reflection and the actual zero-tail bounds to the midpoint | Both branch decompositions in [EtaCurrentMidpointReflection.lean](../RiemannGaussian/EtaCurrentMidpointReflection.lean), finite moment bounds in [EtaCurrentMomentBounds.lean](../RiemannGaussian/EtaCurrentMomentBounds.lean), and `abs_pairedEtaLeadingCurrentMidpointMoment_le_arithmetic` in [EtaCurrentMidpointBounds.lean](../RiemannGaussian/EtaCurrentMidpointBounds.lean). | Proved with an explicit additional endpoint decay factor. The finite reflection defect times the nonzero leading moment is retained; no vanishing or original-current weighted bound follows. |
| Preserve the weighted frontier at linear heat width | `pairedEtaLeadingCurrentLinearHeatReturn_weighted_error_le` in [EtaCurrentLinearHeatSchedule.lean](../RiemannGaussian/EtaCurrentLinearHeatSchedule.lean), and summability and finite-prefix stability in [EtaCurrentLinearHeatReconstruction.lean](../RiemannGaussian/EtaCurrentLinearHeatReconstruction.lean). | Proved at width `2(N+1)`, with separate summable midpoint and remaining-defect majorants and an explicit finite total error budget. No bound on the return's own weighted moment is proved. |
| Prove a signed arithmetic estimate controlling `S_rho(K)` uniformly in `K` | Must preserve completion factors, multiplicity, the head branch, and the correlations needed before taking absolute values. | Open; this is the remaining conjecture-strength objective. |

## Checked reconstruction

Let `G_(sigma,h,tau,k,phi,psi)(t,u,w)` be the existing ordered complex
gap-return core. Its exact identity with two actual commutators has a
negative sign. Before specializing any phase, the new bound is

\[
 |G(t,u,w)|\le
 \frac{e^{-(\sigma+\tau)w/2}}{A(h)A(k)},\qquad
 A(h)=2\sqrt\pi\sqrt2h,
\]

for nonnegative physical endpoint times and tilts, and positive widths.
The literal current is integrable on its finite measure, and the exponential
is integrable on the entire gap when `sigma+tau>0`. Their product proves
genuine three-time integrability. Fubini connects the integrated existing
pairing to the literal current-gap product integral. The negative ordered
two-transition identity survives this integration.

For equal tilts `a>0`, equal widths `h`, and zero probe phases, define

\[
 M(a)=\int_{\mathrm{gap}}e^{-aw}\,dw>0,\qquad
 R_{\rho,N}(a,h)=\frac{8\pi h^2}{M(a)}
 \int_{\mathrm{gap}}\mathrm{GapReturnPairing}_{\rho,N}(a,h,a,h,0,0;w)\,dw.
\]

`pairedEtaLeadingCurrentNormalizedGapReturn` is exactly this normalization of
the existing pairing. Positivity of `M(a)` uses the actual first nonempty gap
interval, and `A(h)^2=8*pi*h^2` is separately proved. Removing the two Gaussian
amplitudes gives the exact profile

\[
 e^{-a(t+u)/2}e^{-aw}
 \exp\left[-\frac{(w-t)^2+(u-w)^2}{8h^2}\right].
\]

It is dominated by `exp(-a*w)` and tends to the same expression without the
Gaussian. Dominated convergence on the actual current-gap product proves

\[
 R_{\rho,N}(a,h)\longrightarrow
 T_{\rho,N}(a)=\int J_{\rho,N}(t,u)e^{-a(t+u)/2}\,d\mu_{\rho,N}(t,u)
 \quad(h\to\infty).
\]

A second dominated-convergence argument proves

\[
 T_{\rho,N}(a)\longrightarrow J_\rho(N)\quad(a\to0^+).
\]

The Lean endpoint is the existing `pairedEtaTopPrefixFiniteEnergyLeadingFlux`,
using the proved exhaustive multiplicity formulas. The completed current is
never replaced by its positive envelope. The raw ordered phase kernel remains
available upstream; only the reconstruction specialization sets the added
probe phases to zero. The ordinate phase inside the completed current remains.

## Checked quantitative error

The new scalar multiplier is the exact gap-time average

\[
 Q_{a,h}(t,u)=\frac1{M(a)}\int_{\mathrm{gap}}e^{-aw}
  \exp\left[-\frac{(w-t)^2+(u-w)^2}{8h^2}\right]\,dw.
\]

It is measurable, genuinely integrable, and between zero and one. Its exact
signed difference from one is retained as an integral before bounding it.
Let `M₂(a)=integral_gap w² exp(-aw) dw`. Lean proves

\[
 0\le M_2(a)\le 2/a^3,\qquad
 |Q_{a,h}(t,u)-1|\le\frac{M_2(a)/M(a)+t^2+u^2}{h^2}.
\]

For `0<a≤1`, monotonicity of the actual gap mass gives
`M₂(a)/M(a) ≤ 2/(M(1)a³)`, with `M(1)>0` proved earlier.
Fubini now identifies the normalized return exactly with the original
current integral against `exp(-a(t+u)/2)*Q`. Consequently its signed error
is the integral of the original current times that multiplier minus one.

The two physical times are proved to lie in `[0,L_N]`, where
`L_N=pairedEtaLogTailCutoff(N+2)=log(2N+5)`, also for the translated head.
Writing `B_rho(N)` for the actual selected kernel's integral of absolute
value, `pairedEtaLeadingCurrentNormalizedGapReturn_error_le` proves

\[
 \|R_{\rho,N}(a,h)-J_\rho(N)\|
 \le B_\rho(N)\left[aL_N+
   \frac{M_2(a)/M(a)+2L_N^2}{h^2}\right].
\]

The small-tilt corollary replaces the moment ratio by `2/(M(1)a³)`.
The factor `B_rho(N)` is finite by the existing genuine kernel integrability.
Its arithmetic growth is now bounded as described below; it has not been
assumed summable across cutoffs. The reconstruction estimate controls the
error of replacing the current by its exact return. The separate weighted
arithmetic target remains unchanged.

## Checked completed kernel mass

Write `sigma=Re rho`, `tau=1-sigma`, and let `W_rho` and `W_partner` be the
existing completed Laplace weights. Every actual zero has `0<sigma,tau<1`.
The finite eta measures are now proved dominated by the full positive-time
Lebesgue measure, giving exponential masses at most `1/sigma`. Their product
has mass at most `1/sigma²`. On the distinct translated head, the first mass
is instead at most the actual cutoff increment `delta_(N+1)`.

The actual head kernel is bounded by twice the sum of its two completed
exponentials at the restored physical coordinate. The adjacent kernel keeps
`2(m-1)delta_(N+1)`, and its centered powers are at most `(1+L_N)^(2m)`.
The phases and signed completion difference remain in the original kernels;
these absolute envelopes are used only downstream to control reconstruction.

Defining the explicit constant

\[
 C_\rho=2m\left[\frac{W_{\mathrm{partner}}}{(1-\Re\rho)^2}
                   +\frac{W_\rho}{(\Re\rho)^2}\right],
\]

`pairedEtaLeadingCurrentAbsoluteKernelMass_le_increment` first retains the
actual increment in `B_rho(N) ≤ C_rho delta_(N+1) (1+L_N)^(2m)`.
The all-cutoff estimate `delta_(N+1) ≤ 1/(N+1)` then proves

\[
 B_\rho(N)\le\frac{C_\rho(1+\log(2N+5))^{2m}}{N+1}.
\]

`pairedEtaLeadingCurrentNormalizedGapReturn_error_le_arithmetic` substitutes
this bound into the small-tilt reconstruction estimate. Every constant in
that result is an actual proved mass, completion weight, zero coordinate,
or analytic multiplicity. No mass bound is left as an antecedent.

## Checked simultaneous weighted reconstruction

Set `x_N=N+1`, `b_N=1+log(2N+5)`, and choose

\[
 a_N=x_N^{-2},\qquad h_N=x_N^4,\qquad
 D_\rho=C_\rho\bigl(3+2/M(1)\bigr).
\]

Every scheduled tilt is positive and at most one, and every width is
positive. The schedule has no dependence on the zero or multiplicity.
The scalar scale estimate proves

\[
 a_NL_N+\frac{2/(M(1)a_N^3)+2L_N^2}{h_N^2}
 \le \bigl(3+2/M(1)\bigr)\frac{b_N^2}{x_N^2}.
\]

Thus the actual scheduled return `R_N=R_(rho,N)(a_N,h_N)` satisfies

\[
 \|R_N-J_\rho(N)\|\le D_\rho\frac{b_N^{2m+2}}{x_N^3},\qquad
 (2N+1)\|R_N-J_\rho(N)\|
 \le 2D_\rho\frac{b_N^{2m+2}}{x_N^2}.
\]

These are the two terminal bounds in
[EtaCurrentReconstructionSchedule.lean](../RiemannGaussian/EtaCurrentReconstructionSchedule.lean).
The proof of `summable_pairedEtaCurrent_logPower_div_sq` compares each fixed
logarithmic power with a square root eventually and then uses the convergent
`3/2` power series. Consequently
`summable_oddEndpoint_mul_norm_pairedEtaLeadingCurrentScheduledGapReturn_error`
proves the required weighted norm-error series converges for every actual
nontrivial zero. The complex weighted error series is also summable, with
its signed difference retained.

Define the genuinely finite error budget

\[
 E_\rho=2D_\rho\sum_{N\ge0}\frac{b_N^{2m+2}}{x_N^2}.
\]

Lean proves that every finite weighted error sum is at most `E_rho`.
The reverse triangle inequality then gives, for every terminal cutoff `K`,

\[
 \left|\sum_{N<K}(2N+1)\|R_N\|-S_\rho(K)\right|\le E_\rho.
\]

The declaration is
`pairedEtaLeadingCurrentScheduledGapReturn_firstMoment_stability` in
[EtaCurrentWeightedReconstruction.lean](../RiemannGaussian/EtaCurrentWeightedReconstruction.lean).
This controls the difference between the two moments uniformly; it does not
bound either moment itself. All completion weights, the actual head branch,
and analytic multiplicity entered through the previously checked mass bound.
No arithmetic cancellation premise was used.

## Checked continuous composition and the exact corrections

Let `K_h` be the existing normalized Gaussian `etaNormalizedHeatKernel h`.
Before imposing any intermediate-time restriction, two equal-width
half-tilted transitions have the positive envelope

\[
 F_{a,h}(t,u,w)=e^{-a(t+w)/2}K_{\sqrt2h}(w-t)
                e^{-a(w+u)/2}K_{\sqrt2h}(u-w).
\]

The exact pointwise factorization is

\[
 F_{a,h}(t,u,w)=
 e^{a^2h^2-a(t+u)}K_{2h}(u-t)
 K_h\!\left(w-\left[\tfrac{t+u}{2}-2ah^2\right]\right).
\]

Consequently its full-line `w` integral is
`exp(a²h²-a(t+u))*K_(2h)(u-t)`. With a common probe phase, the intermediate
phase cancels exactly, leaving `exp(i(phi(t)-phi(u)))`. Arbitrary ordered
probe phases remain in the source kernel and in the subsequent signed
decomposition; only the evaluated composition specializes them to one phase.

For `a≥0`, `h>0`, and nonnegative endpoint times, the full-line slice mass
is at most `exp(a²h²)/(4*sqrt(pi)*h)`. Fubini and this bound prove genuine
three-time integrability against the original integrable current. This
includes **zero tilt** and both actual multiplicity carriers, with the
translated head coordinate restored. Restriction of the intermediate measure
then proves integrability on eta support, eta gap, and nonpositive time.

The measure identity is exactly

\[
 dw=d\mu_{\eta}(w)+d\mu_{\mathrm{gap}}(w)
       +\mathbf1_{(-\infty,0]}(w)\,dw.
\]

Thus `pairedEtaLeadingCurrentIntegratedGapReturn_eq_composed_sub_corrections`
proves that the actual completed gap return equals the explicitly composed
broader Gaussian pairing minus the support return minus the nonpositive-time
correction. Every term retains the original signed completed kernel. The
decomposition does not assert that either correction is negligible.

The checked theorem
`pairedEtaCurrentReconstructionSchedule_fullLine_amplification` evaluates the
full-line envelope factor on the existing reconstruction schedule as
`exp((N+1)^4)`. This is not a lower bound on the signed pairing; it shows why
discarding the signed correction balance does not produce the desired
estimate. The new zero-tilt integrability removes this amplification at the
kernel-composition level, but the old Laplace-mass normalization applies only
at positive tilt. A separate actual-gap Gaussian normalization and weighted
error bound are now proved below.

## Checked zero-tilt reconstruction

For a nonnegative decreasing function integrable on positive time,
consecutive logarithmic unit intervals carry decreasing mass. Summing the
actual alternating support and gap intervals gives

\[
 \int_{\mathrm{gap}}f\le\int_{\eta}f
 \le\int_0^{\log2}f+\int_{\mathrm{gap}}f.
\]

The theorem `pairedEta_decreasing_gap_mass_bounds` retains genuine
integrability and bounds the first interval by `log(2)*f(0)`. For `h>0`, define
`g_h(c)=integral_gap K_h(w-c) dw`. The Gaussian specialization proves

\[
 \frac14-\frac{\log2}{4\sqrt\pi h}\le g_h(0)\le\frac14,
 \qquad g_h(0)\ge\frac18\quad(h\ge2).
\]

Every translated mass is positive and at most one. Its shift estimate is

\[
 |g_h(c)-g_h(0)|\le\frac{3c}{2\sqrt\pi h}\qquad(c\ge0).
\]

The proof compares the absolute Gaussian translation error with
`K_h(w-c)+K_h(w)-2K_h(w+c)` on positive time. Its integral is exactly
three times `integral_0^c K_h`. Domination of the actual gap measure by
positive-time volume then proves the bound; the gap is never assumed
translation invariant or replaced by a density model.

Normalize the existing zero-tilt full-gap return by
`A_h=4*sqrt(pi)*h/g_h(0)`. Lean proves `0<A_h<=32*sqrt(pi)*h` for `h>=2`.
The exact normalized slice is

\[
 Q_h(t,u)=e^{-(u-t)^2/(16h^2)}\frac{g_h((t+u)/2)}{g_h(0)}.
\]

`integral_fullTwoHeat_zero_phase_gap_normalized` connects this formula to
the existing two-transition kernel. Its multiplier is positive, at most
eight, and jointly measurable. For physical endpoints in `[0,L]`,
`pairedEtaZeroTiltGapMultiplier_window_error_le` proves

\[
 |Q_h(t,u)-1|\le\frac{13(1+L)^2}{h}.
\]

Fubini retains the exact signed current integral against `Q_h-1`.
`pairedEtaLeadingCurrentZeroTiltGapReturn_error_le` applies the bound to
both unchanged multiplicity carriers, including the restored head time.
Only the added probe phases are zero; the original ordinate phase and
completion difference remain inside the current.

Set `h_N=2(N+1)²` and write `R_N^0` for this normalized return. The actual
mass bound above now gives

\[
 \|R_N^0-J_\rho(N)\|\le\frac{13C_\rho}{2}
 \frac{b_N^{2m+2}}{(N+1)^3},\qquad
 (2N+1)\|R_N^0-J_\rho(N)\|\le13C_\rho
 \frac{b_N^{2m+2}}{(N+1)^2}.
\]

The existing logarithmic-series theorem proves summability of the weighted
norm errors and the signed complex errors. With the finite budget
`E_rho^0=13*C_rho*sum_N b_N^(2m+2)/(N+1)^2`, Lean proves

\[
 \left|\sum_{N<K}(2N+1)\|R_N^0\|-S_\rho(K)\right|\le E_\rho^0
 \quad\text{for every }K.
\]

This removes the previous tilt-amplification obstruction while retaining
the entire arithmetic gap. It bounds the reconstruction error, not either
first absolute moment. A norm bound on the positive multiplier alone still
gives only the insufficient absolute kernel-mass scale; a new use of the
zero equation and signed completion symmetry is needed.

## Checked Wallis expansion and the actual midpoint correction

Write `ell=log(pi/2)` and let `chi` be the literal eta support indicator.
The actual signed primitive and its remainder are

\[
 A(t)=\int_0^t(2\chi(w)-1)\,dw,\qquad B(t)=A(t)-\ell.
\]

Complete support/gap pairs give exactly `A(log(2n+1))=log(W_n)` for
Mathlib's finite Wallis product. Its two product bounds, together with the
final partial pair, prove `|B(t)| <= 9 exp(-t)` for every `t>=0`.
This uses the actual interval colour at every real time.

For `K_h(r)=exp(-r²/(4h²))/(2 sqrt(pi) h)`, define the signed correction

\[
 C_h(c)=\int_0^\infty B(w)K'_h(w-c)\,dw.
\]

Absolute continuity of the primitive, genuine integrability, and a proved
vanishing endpoint justify integration by parts and give the exact identity

\[
 g_h(c)=\frac14+\frac12\int_0^c K_h(w)\,dw
             -\frac{\ell K_h(c)}2+\frac{C_h(c)}2,
 \qquad |C_h(c)|\le\frac{9(1+c)}{4\sqrt\pi h^3}.
\]

For every `h>0`, `c>=0`, the resulting expansion is

\[
 \left|g_h(c)-\frac14-\frac{c-\ell}{4\sqrt\pi h}\right|
 \le \frac{2(1+c)^3}{h^3}.
\]

Normalization by `g_h(0)` cancels the Wallis constant at first order.
For `h>=2`, the actual ratio has error at most `18(1+c)^3/h²` after
subtracting `1+c/(sqrt(pi)h)`. Including the displacement Gaussian gives

\[
 \left|Q_h(t,u)-1-\frac{(t+u)/2}{\sqrt\pi h}\right|
 \le \frac{19(1+L)^3}{h^2}\quad(0\le t,u\le L).
\]

Let `f_rho,N` be the original selected signed kernel, with its actual
measure, and set

\[
 M_\rho(N)=\int f_{\rho,N}(p)\frac{T(p)+p_2}{2}\,d\mu_{\rho,N}(p).
\]

Here `T(p)=p_1+L_(N+1)` in the simple-zero head and `T(p)=p_1` in the
adjacent-moment branch. Both midpoint integrals are proved integrable.
The exact signed current defect is still an integral against
`Q_h-1-midpoint/(sqrt(pi)h)` before its norm is bounded. The terminal
arithmetic error theorem proves

\[
 \left\|R^0_{\rho,N}(h)-J_\rho(N)
             -\frac{M_\rho(N)}{\sqrt\pi h}\right\|
 \le \frac{19C_\rho(1+L_N)^{2m+3}}{(N+1)h^2}.
\]

The coefficient is the unchanged signed current's physical midpoint
moment. Its finite arithmetic evaluation and a zero-tail gain are now
proved below. An improved reconstruction remainder alone does not give
the uniform weighted bound for `J_rho`.

## Checked midpoint arithmetic, reflection, and endpoint gain

Put `c_rho=pairedEtaXiCompletionFactor(rho)*rho`, and write
`A_rho,k(n)=c_rho*P_k(rho,n)` for the existing centered finite eta moment
with its actual completion factor. The complex pair is

\[
 \Gamma_{k,l}(n)=A_{\rho^*,k}(n)\overline{A_{\rho^*,l}(n)}
                    -\overline{A_{\rho,k}(n)}A_{\rho,l}(n).
\]

The two parity factors cancel exactly in this product, leaving the
original conjugate channel's orientation intact. Genuine integration on
the actual finite product measure evaluates this complex pair. Multiplying
its kernel by the physical midpoint raises either centered order. For
`m>=2`, the checked identity for the unchanged current is

\[
 M_\rho(N)=L_NJ_\rho(N)+(m-1)\delta_{N+1}
   \Re\!\left(\Gamma_{m-1,m-1}(N+2)+\Gamma_{m-2,m}(N+2)\right).
\]

For the simple-zero head let
`H_rho,k(N)=-c_rho*Head_k(rho,N+1)`, with the actual shifted-head moment.
Write `Gamma^H_(k,l)` for the signed complex pair of `H_k` and
`A_l(N+2)` in the same orientation. If `a_N=pairedEtaLogTailCutoff(N+1)`,
the checked simple-zero formula is

\[
 M_\rho(N)=\frac{a_N+L_N}{2}J_\rho(N)
              +\Re\Gamma^H_{1,0}(N)+\Re\Gamma^H_{0,1}(N).
\]

Both the old head origin and the successor prefix center are necessary.
Each product integral has its own genuine integrability proof.

The leading full moment `D_rho=c_rho*P_m(rho)` is proved nonzero.
Completed reflection gives `D_partner=(-1)^m*conj(D_rho)`. Let
`T_rho,k(n)` denote the actual completed centered tail. The exact identity
`A_rho,m(n)=D_rho-T_rho,m(n)` then evaluates the order-`m` pair as

\[
 \Gamma_{k,m}(n)=(-1)^m\Delta_k(n)D_\rho
  -\left(A_{\rho^*,k}(n)\overline{T_{\rho^*,m}(n)}
          -\overline{A_{\rho,k}(n)}T_{\rho,m}(n)\right),
 \quad
 \Delta_k(n)=A_{\rho^*,k}(n)-(-1)^m\overline{A_{\rho,k}(n)}.
\]

The actual head has the same identity with `A_k` replaced by `H_k` and
the successor tail retained. Thus completed symmetry identifies a finite
defect multiplying a nonzero moment; it does not establish that this
defect, or its real pairing in `M`, vanishes.

There is nevertheless a proved arithmetic gain from the existing zero
equation below multiplicity. Define the explicit finite constant

\[
 Q_\rho=|c_\rho|+|D_\rho|
                 +\frac{|c_\rho|\,m!}{(\Re\rho)^{m+1}},
 \qquad d_\rho(N)=(2N+3)^{-\Re\rho}.
\]

At every cutoff, the checked moment bounds give
`|A_rho,k(N+2)|<=Q_rho*d_rho(N)` for `k<m` and
`|A_rho,k(N+2)|<=Q_rho` for `k<=m`. Every actual shifted head order also
satisfies `|H_rho,k(N)|<=Q_rho*delta_(N+1)*d_rho(N)`. Applying these
only after the exact signed identities proves

\[
 |M_\rho(N)|\le\frac{2m(1+L_N)}{N+1}
   \left(Q_{\rho^*}^{\,2}(2N+3)^{-(1-\sigma)}
          +Q_\rho^{\,2}(2N+3)^{-\sigma}\right),\qquad\sigma=\Re\rho.
\]

This removes the growing centered-monomial envelope and retains a
strictly positive endpoint decay exponent in both actual branches. It
bounds the midpoint coefficient; it is not the uniform first absolute
moment estimate for the original current. No new cancellation of the
finite reflection defect has been established.

## Checked linear-width weighted reconstruction

Set `x_N=N+1`, `b_N=1+L_N`, and let `E_rho(N)` denote the two-channel
endpoint envelope in the preceding midpoint bound. The unchanged actual
zero-tilt gap return is now evaluated at `h_N=2x_N`; write it as `R_N` and
retain its signed midpoint term `T_N=M_rho(N)/(sqrt(pi)*h_N)`.
[EtaCurrentLinearHeatSchedule.lean](../RiemannGaussian/EtaCurrentLinearHeatSchedule.lean)
proves, for every actual zero and cutoff,

\[
 (2N+1)|T_N|\le\frac{2m}{\sqrt\pi}\frac{b_NE_\rho(N)}{x_N},
 \qquad
 (2N+1)\|R_N-J_N-T_N\|
 \le\frac{19}{2}C_\rho\frac{b_N^{2m+3}}{x_N^2}.
\]

The general logarithmic series theorem
`summable_pairedEtaCurrent_logPower_div_rpow` in
[EtaCurrentEndpointSeries.lean](../RiemannGaussian/EtaCurrentEndpointSeries.lean)
proves summability of `b_N^k/x_N^p` for every fixed `k` and `p>1`.
The actual zero coordinates supply the strict margins `p=1+Re(rho)`
and `p=1+(1-Re(rho))` needed for the midpoint term. Consequently

\[
 F_\rho(N)=\frac{19}{2}C_\rho\frac{b_N^{2m+3}}{x_N^2}
       +\frac{2m}{\sqrt\pi}\frac{b_NE_\rho(N)}{x_N}
\]

is a proved summable majorant of `(2N+1)*norm(R_N-J_N)`.
[EtaCurrentLinearHeatReconstruction.lean](../RiemannGaussian/EtaCurrentLinearHeatReconstruction.lean)
retains both the norm-summable and signed complex weighted error series.
The explicit finite budget `E_linear(rho)=sum_N F_rho(N)` bounds every
finite error sum. Its terminal theorem
`pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_stability` gives

\[
 \left|\sum_{N<K}(2N+1)\|R_N\|
       -\sum_{N<K}(2N+1)|J_N|\right|\le E_{\mathrm{linear}}(\rho)
 \quad\text{for every }K.
\]

This improves the checked reconstruction width from quadratic to linear
while preserving both original completed carriers. It does not bound
either first absolute moment itself. That independent arithmetic estimate
remains the full goal's unresolved part.

## Next mathematical obligations

1. Establish arithmetic cancellation on the retained current or return
   family sufficient to control `S_rho(K)`. Bounds for a positive heat Gram
   or a norm of a single phase channel do not establish the required signed
   completed-current bound. The small-width signed endpoint theorem and the
   broad-width reconstruction concern different regimes; a use of one to
   bound the other requires a proved intervening identity and estimate.
2. Use the proved uniform reconstruction stability to transport a proved
   return bound to the original current, without another exchange of an
   uncontrolled limit and weighted series.
3. Only after that bound is discharged, prove the existing first-moment
   summability statement and use its existing equivalence to derive
   `RiemannHypothesis`. Audit the terminal theorem, all transitive axioms,
   full library, generated status, and exact-commit CI before any completion
   claim.

## Assessment of the combined research direction

The most concrete combination is literal eta interval geometry, complex
phase probes, ordered Gaussian support/gap returns, and the completed
arithmetic current. It now preserves the first absolute-moment frontier up
to the proved finite error budget above. This is a stronger application
interface than fixed-cutoff reconstruction alone. Priority for the combined
mathematics has not been established.

The operator-theoretic theme itself has substantial prior work. Suzuki's
[2026 paper on the Weil form](https://arxiv.org/html/2606.09096v1) relates
continuous screw kernels to finite-interval operators, proves continuity
of the lowest eigenvalue, and gives a small-interval asymptotic. Its proposed
limiting spectral identification remains conjectural. The repository's
candidate contribution should therefore be judged at the level of the
specific eta arithmetic and completed signed estimates.

The next work builds on the checked two-transition comparison and seeks a
quantitative comparison between heat scales with the completion channels
retained. The table distinguishes the completed identity from proposed
estimates and longer-path targets. None of the open targets is a premise
to add to Lean:

| Step | Existing input | Concrete target and acceptance condition |
| --- | --- | --- |
| Compare ordered heat compositions on the actual domain | The exact continuous composition, full three-time integrability, and zero-tilt weighted reconstruction above. | The normalization and reconstruction error are now controlled with linear width. The next estimate must preserve cancellation of the signed completed current against the composed term and both corrections. |
| Keep all support/gap paths | The actual two-transition decomposition above, the finite two-stage identity in [ProjectionHeatLeakage](../RiemannGaussian/Hybrid/ProjectionHeatLeakage.lean), and ordered cubic paths in [EtaSpectralHeatCubicPaths](../RiemannGaussian/Hybrid/EtaSpectralHeatCubicPaths.lean). | For any longer-path comparison, prove its identities on the actual continuous eta measure and pair every path with both completed current branches. Include every omitted-time and compression term with its sign. The existing finite matrix algebra alone is insufficient. |
| Test a quantitative scale comparison | The signed two-endpoint heat law, full mixed phase matrix, and the new reconstruction error budget. | Derive an estimate for the actual signed return with cutoff, phase-family size, moving tilt, multiplicity, and accumulated path error explicit. A sufficient endpoint would be a summable majorant for `(2N+1)‖R_N‖`; the exact target is a bound on its partial sums uniform in `K`. |

The decisive test is whether the zero condition and completion symmetry
supply a new cancellation in that comparison. Positive Gram bounds, a
fixed-size matrix limit, or discarding path signs cannot provide it by
themselves. In particular, fixed moving-tilt asymptotics do not control a
fixed off-axis zero: their tilt parameter grows with the logarithmic scale.
If no estimate survives these dependencies, the next result should state
the obstruction precisely rather than rename it as another RH criterion.

### Next estimates on the retained signed arithmetic

The exact branch formulas, completed reflection defect, endpoint gain,
and linear-width summability are now proved. None proves cancellation
of the retained defect. The next targets are **proposed work**, not
assumptions to add to the proof chain.

1. Use the retained finite reflection defect and signed tail pairs to
   seek an independent estimate of the return itself. Any use of the
   mixed phase matrix must identify the actual finite eta feature vector
   and control its dimension, scale, and compression errors. The above
   midpoint estimate alone cannot bound `S_rho(K)`.
2. Preserve the unchanged final target: partial sums of
   `(2N+1)*|J_rho(N)|` bounded uniformly in `K` for every actual zero.
   That bound would imply RH through the already checked equivalence;
   it is not an auxiliary estimate already supplied by this package.

Broader claims of novelty require comparison with the literature.
Gaussian expansions, moment raising, and operator positivity are
established techniques; the contribution checked here is their explicit
combination on the original completed eta carriers.

No reconstruction or summability premise has been introduced as an axiom.
The goal remains open because the uniform weighted arithmetic estimate is
not yet established. No `13/18` certificate or RH proof is claimed.
