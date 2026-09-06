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
| Estimate the retained signed arithmetic against explicit endpoint terms | Complex prefix and pair errors in [EtaCurrentEulerMoments.lean](../RiemannGaussian/EtaCurrentEulerMoments.lean) and [EtaCurrentEulerPairs.lean](../RiemannGaussian/EtaCurrentEulerPairs.lean); elementary head and positive adjacent coefficients in [EtaCurrentEulerArithmetic.lean](../RiemannGaussian/EtaCurrentEulerArithmetic.lean); `pairedEtaLeadingCurrentLinearHeatReturn_euler_error_sum_le` in [EtaCurrentEulerEstimate.lean](../RiemannGaussian/EtaCurrentEulerEstimate.lean). | Proved with summable weighted error in both actual branches. The endpoint expression itself still requires an independent weighted bound. The repeated-zero contribution has no cutoff Fourier oscillation. |
| Bound the original return's weighted moment as the cutoff grows | The two-factor estimate in [EtaCurrentArithmeticEnvelope.lean](../RiemannGaussian/EtaCurrentArithmeticEnvelope.lean), the finite power-sum comparison in [EtaCurrentPowerSum.lean](../RiemannGaussian/EtaCurrentPowerSum.lean), and `pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_growth_le` in [EtaCurrentReturnGrowth.lean](../RiemannGaussian/EtaCurrentReturnGrowth.lean). | Proved with explicit growth `C_rho*(K+1)^abs(2*Re(rho)-1)` and exact treatment of the critical line. The exponent is below one, and the cutoff-normalized moment tends to zero. A cutoff-independent bound remains open. |
| Couple actual completed eta tails across multiplicatively divided cutoffs | `sum_moebius_mul_pairedEtaCorePartialSum_add_endpoint` in [EtaMoebiusFinitePrefix.lean](../RiemannGaussian/EtaMoebiusFinitePrefix.lean) and `pairedEtaCompletedMoebiusTailAggregate_eq_source` in [EtaMoebiusCompletedTail.lean](../RiemannGaussian/EtaMoebiusCompletedTail.lean). | Proved at every actual zero and every integer cutoff at least two, with all odd endpoint corrections and complex Möbius weights. The resulting linear constraint has no proved quadratic-current bound yet. |
| Bound both complete parity aggregates and their signed block sums | Exact halved-cutoff identities in [EtaMoebiusParityRecurrence.lean](../RiemannGaussian/EtaMoebiusParityRecurrence.lean), `norm_pairedEtaCompletedMoebiusOddAggregate_le` in [EtaMoebiusParityBound.lean](../RiemannGaussian/EtaMoebiusParityBound.lean), and `norm_pairedEtaSignedCompletedMoebiusParityBlock_le` in [EtaMoebiusParityBlocks.lean](../RiemannGaussian/EtaMoebiusParityBlocks.lean). | Proved uniformly in the physical cutoff, with every divisor and both completion channels retained. These are norms of block sums; a bound for the original weighted absolute return does not follow yet. |
| Recover the original simple-zero current from the parity aggregates | `pairedEtaFiniteCompletedMoment_zero_eq_oddInverse` in [EtaMoebiusParityInverse.lean](../RiemannGaussian/EtaMoebiusParityInverse.lean) and `pairedEtaLeadingCurrent_eq_oddInverse_head` in [EtaCurrentMoebiusInverse.lean](../RiemannGaussian/EtaCurrentMoebiusInverse.lean). | The exact inverse weights, divided cutoffs, and both signed head channels are proved. Their absolute weight mass has matching positive-power bounds in [EtaMoebiusInverseWeights.lean](../RiemannGaussian/EtaMoebiusInverseWeights.lean), so termwise norms do not supply a uniform transfer. |
| Sum equal-cutoff inverse phases and retain cancellation with the complementary cutoffs | Complex midpoint control in [EtaOddPowerQuadrature.lean](../RiemannGaussian/EtaOddPowerQuadrature.lean), the nonzero Mellin coefficient in [EtaOddPowerMellin.lean](../RiemannGaussian/EtaOddPowerMellin.lean), and `norm_pairedEtaCompletedOddInverseBottom_add_main_le` in [EtaMoebiusGroupedInverse.lean](../RiemannGaussian/EtaMoebiusGroupedInverse.lean). | The full top inverse block grows after its phases are summed. The complementary block has the opposite explicit complex main term with a decaying error. Their sum is the actual zeroth completed moment; the weighted signed-current bound remains open. |
| Obtain an independent arithmetic exclusion and transport it to the original return | `one_le_etaPrimeProduct_zero_gap` in [EtaZetaPrimeProduct.lean](../RiemannGaussian/EtaZetaPrimeProduct.lean), `nontrivialZetaZero_mem_etaPrimeProduct_strip`, and `pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_le_etaPrimeProduct` in [EtaPrimeProductZeroMargin.lean](../RiemannGaussian/EtaPrimeProductZeroMargin.lean). | Every actual zero lies between the explicit positive margins `delta(Im rho)` and `1-delta(Im rho)`. The original return is bounded by `C_rho*(K+1)^(1-2*delta(Im rho))`. The exponent remains positive; the uniform weighted goal remains open. |
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

## Checked signed Euler endpoint estimate

The direct arithmetic test now uses the quantitative Euler theorem for
the actual centered eta tails. Define the explicit complex terms

\[
 a_{\rho,k}=\frac{k!}{2\rho^{k+1}},\qquad
 U_{\rho,k}(N)=-c_\rho e^{-\rho L_N}a_{\rho,k},\qquad
 D_{\rho,k}=|c_\rho|\frac{k!(|\rho|+\sigma/2+1)}{(\sigma/2)^k}.
\]

For every `k<m`, the original finite completed moment satisfies the
exact phased identity

\[
 A_{\rho,k}(N+2)-U_{\rho,k}(N)
 =-c_\rho e^{-\rho L_N}
   \bigl(\widetilde T_{\rho,k}(N+2)-a_{\rho,k}\bigr),
\]

where the shifted tail is the genuine eta integral. The compiled theorem
`norm_pairedEtaFiniteCompletedMoment_sub_euler_le` bounds this error by
`D_rho,k*d_rho(N)/(N+1)`. The endpoint phase is retained before its norm
is taken. The signed pair comparison keeps the partner product error
minus the conjugate original product error, and each product keeps both
error positions. All comparison constants are explicit in
[EtaCurrentEulerPairs.lean](../RiemannGaussian/EtaCurrentEulerPairs.lean).

The new expression `J_E(rho,N)=pairedEtaCurrentEulerExpression rho N`
substitutes these `U` terms in the two original current formulas. In the
simple-zero branch it retains the actual order-zero head, which Lean now
evaluates exactly:

\[
 H_{\rho,0}(N)=\operatorname{Completion}(\rho)
   \left(e^{-\rho\log(2N+4)}-e^{-\rho\log(2N+3)}\right).
\]

In the repeated-zero branch, `k=m-2`, Lean proves

\[
 J_E(\rho,N)=2(m-1)\delta_{N+1}
   \left(P_{\rho^*,k}e^{-2(1-\sigma)L_N}
         -P_{\rho,k}e^{-2\sigma L_N}\right),
\]

where each coefficient is strictly positive:

\[
 P_{\rho,k}=|c_\rho|^2\Re(a_{\rho,k}\overline{a_{\rho,k+1}}),
 \qquad
 \Re(a_{\rho,k}\overline{a_{\rho,k+1}})
 =\frac{(k+1)\sigma}{|\rho|^2}|a_{\rho,k}|^2>0.
\]

These are the compiled theorems
`pairedEtaCurrentEulerMoment_mul_conj`,
`pairedEtaCurrentEulerAdjacentCoefficient_pos`, and
`pairedEtaCurrentEulerExpression_eq_adjacent_endpoints`. The first
identity cancels the common endpoint Fourier phase at the complex level;
the remaining coefficients retain their dependence on the actual zero.

The explicit function `B_rho(N)=pairedEtaCurrentEulerErrorEnvelope rho N`
is proved summable. Its head branch is
`Q_partner*D_partner,0*d_partner(N)/(N+1) + Q_rho*D_rho,0*d_rho(N)/(N+1)`.
Its repeated-zero branch is `(m-1)` times the corresponding sum with
pair constants `D_rho,k*Q_rho + |c_rho|*|a_rho,k|*D_rho,k+1`.
The final estimates, valid at every cutoff, are

\[
 (2N+1)|J_\rho(N)-J_E(\rho,N)|\le4B_\rho(N),
\]
\[
 (2N+1)\|R_N-J_E(\rho,N)\|\le F_\rho(N)+4B_\rho(N).
\]

Both error series are proved summable. The terminal theorem
`pairedEtaLeadingCurrentLinearHeatReturn_euler_error_sum_le` bounds every
finite return error sum by the same genuine finite total
`sum_N (F_rho(N)+4B_rho(N))`.

This supplies an arithmetic estimate on the original current and return,
beyond heat reconstruction alone. It also identifies a specific limit of
the proposed phase approach: the repeated-zero leading expression itself
has no cutoff Fourier oscillation left to average away. Our assessment is
that controlling only oscillatory errors cannot finish the argument;
an independent arithmetic constraint must also control this surviving
completed endpoint contribution. No bound on its first absolute moment
has been proved, and no zero-location conclusion follows from the error
estimate alone.

## Checked growth bound for the actual weighted return moment

The direct current estimate now retains both lower-order zero-tail decays.
Write `d_rho(N)=(2N+3)^(-Re(rho))` as above. The two finite moments in
the repeated-zero leading pair are both below multiplicity. In the
simple-zero branch the actual head and successor order-zero prefix each
retain one endpoint decay. Consequently
`pairedEtaLeadingCurrent_weighted_le_doubleDecay` proves

\[
 (2N+1)|J_\rho(N)|\le4m\left(
 Q_{\rho^*}^2d_{\rho^*}(N)^2+Q_\rho^2d_\rho(N)^2\right).
\]

This is a bound on the original current itself. The exact complex signed
pairs and endpoint identities remain available upstream of this norm
estimate. At `Re(rho)=1/2`, the compiled theorem
`pairedEtaLeadingCurrent_eq_zero_of_re_eq_half` proves the original real
current zero at every cutoff in both multiplicity branches.

Set `e_rho=abs(2*Re(rho)-1)` and
`A_rho=4m*(Q_partner^2+Q_rho^2)`. Reflection preserves `e_rho`, and
the actual critical-strip hypotheses give `0<=e_rho<1`. Both endpoint
powers are at most `(N+1)^(e_rho-1)`.
The finite integral comparison `sum_range_nat_add_one_rpow_le` proves

\[
 \sum_{N<K}(N+1)^r\le\frac{(K+1)^{r+1}}{r+1},\qquad -1<r\le0.
\]

For an actual off-critical zero, `e_rho>0` is proved before division.
The current and return therefore satisfy the explicit bounds

\[
 \sum_{N<K}(2N+1)|J_\rho(N)|
 \le\frac{A_\rho}{e_\rho}(K+1)^{e_\rho},
\]
\[
 S_R(\rho,K):=\sum_{N<K}(2N+1)\|R_N\|
 \le E_{\mathrm{linear}}(\rho)
      +\frac{A_\rho}{e_\rho}(K+1)^{e_\rho}.
\]

At a critical-line zero, exact current cancellation instead gives
`S_R(rho,K)<=E_linear(rho)`. Define the explicit finite constant

\[
 C_\rho=E_{\mathrm{linear}}(\rho)+
 \begin{cases}0,&\Re\rho=1/2,\\ A_\rho/e_\rho,&\Re\rho\ne1/2.\end{cases}
\]

The terminal theorem
`pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_growth_le` proves
`S_R(rho,K)<=C_rho*(K+1)^e_rho` for every actual zero and cutoff.
The same module proves
`pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_div_cutoff_tendsto_zero`:

\[
 \frac{S_R(\rho,K)}{K+1}\longrightarrow0.
\]

This is a proved sublinear bound for the original weighted return moment,
including all absolute values, completion constants, and multiplicity.
The exponent still depends on the actual zero's unknown horizontal
position. It supplies no new zero-location constraint. The original goal
requires a bound on `S_R(rho,K)` independent of `K`, without dividing by
the cutoff. That requirement is unchanged and remains open.

## Checked common principal endpoints in both multiplicity branches

The simple-zero head's remaining local phase now has an explicit
summable weighted correction. The compiled modules are
[EtaCurrentHeadHalfWidth](../RiemannGaussian/EtaCurrentHeadHalfWidth.lean),
[EtaCurrentHalfStepHead](../RiemannGaussian/EtaCurrentHalfStepHead.lean),
[EtaCurrentHalfStepPairs](../RiemannGaussian/EtaCurrentHalfStepPairs.lean),
and [EtaCurrentPrincipalEndpoints](../RiemannGaussian/EtaCurrentPrincipalEndpoints.lean).

Write `q=2N+3`, `x=N+1`, `a=log(q)`, `L=log(q+2)`,
`delta=log((q+2)/q)`, and `w=log((q+1)/q)`. The exact interval identity
`pairedEtaShiftedLogHeadWidth_sub_half_step_eq` gives

\[
 w-\delta/2=\tfrac12\log\left(1+\frac1{q(q+2)}\right),
 \qquad 0\le w-\delta/2\le\frac1{2x^2}.
\]

For `c_rho=pairedEtaXiCompletionFactor(rho)*rho`, put
`K_rho=norm(rho)*exp(norm(rho))` and
`D_head(rho)=norm(c_rho)*(2*K_rho+1)`. The original completed head
`H_rho(N)` is compared with

\[
 H^{1/2}_\rho(N)=-c_\rho e^{-\rho L}\delta/2
               =\delta\rho U_{\rho,0}(N).
\]

`pairedEtaHeadCompletedMoment_sub_halfStep` retains its exact complex
defect, with the integral variation, unequal support/gap widths, and
endpoint translation separately visible. The compiled theorem
`norm_pairedEtaHeadCompletedMoment_sub_halfStep_le` proves

\[
 \|H_\rho(N)-H^{1/2}_\rho(N)\|
 \le D_{\mathrm{head}}(\rho)d_\rho(N)/x^2.
\]

Define `C_head(rho)=D_head(rho)*pairedEtaCurrentEulerMomentAmplitude(rho,0)`
and the explicitly summable envelope

\[
 B_{\mathrm{head}}(\rho,N)=
 \frac{C_{\mathrm{head}}(\rho^*)d_{\rho^*}(N)
       +C_{\mathrm{head}}(\rho)d_\rho(N)}{x}.
\]

Both signed complex product defects are retained in
`pairedEtaCurrentEulerHeadPair_sub_halfStep`; their real-current error
with the original odd weight is at most `4*B_head(rho,N)`.
The half-step product's common endpoint phase cancels exactly in
`pairedEtaCurrentHalfStepHead_mul_conj_euler`. Its simple coefficient is

\[
 A_{\mathrm{simple}}(\rho)=
 2\sigma\|c_\rho\|^2|a_{\rho,0}|^2>0.
\]

The multiplicity-selected coefficient is

\[
 A_\rho=\begin{cases}
 A_{\mathrm{simple}}(\rho),&m=1,\\
 2(m-1)P_{\rho,m-2},&m\ge2,
 \end{cases}
\]

where `P` is the previously evaluated completed adjacent Euler
coefficient. `pairedEtaCurrentPrincipalCoefficient_pos` proves
`A_rho>0` in both actual branches. Reflection preserves the multiplicity.
The resulting common principal expression is

\[
 J_{\mathrm{principal}}(\rho,N)=\delta_{N+1}
 \left[A_{\rho^*}e^{-2(1-\sigma)L_N}
       -A_\rho e^{-2\sigma L_N}\right].
\]

It equals the repeated-zero Euler expression exactly and the simple
half-step expression exactly. The original current has odd-weighted
error at most `4*B_Euler+4*B_head`. The **unchanged** actual linear-width
return has odd-weighted norm error at most

\[
 F_{\mathrm{principal}}(\rho,N)=
 F_{\mathrm{heat}}(\rho,N)+4B_{\mathrm{Euler}}(\rho,N)
                         +4B_{\mathrm{head}}(\rho,N),
\]

whose series is proved summable. The terminal theorem
`pairedEtaLeadingCurrentLinearHeatReturn_principal_firstMoment_stability`
proves, at every cutoff `K`,

\[
 \left|S_R(\rho,K)-
 \sum_{N<K}(2N+1)|J_{\mathrm{principal}}(\rho,N)|\right|
 \le\sum_{N\ge0}F_{\mathrm{principal}}(\rho,N)<\infty.
\]

The sum's finiteness is the named summability theorem, not an inference
from Lean's totalized `tsum`. This completes the simple-head phase
comparison on the original return. It leaves two positive leading
coefficients and complementary horizontal powers. The next quantitative
test is whether that explicit term forces the previously allowed
displacement-power growth off the critical line. No cutoff-independent
bound for the principal term, original current, or original return has
been proved here.

## Checked sharp growth under the off-critical hypothesis

The quantitative test above is now proved in
[EtaCurrentPrincipalDominance](../RiemannGaussian/EtaCurrentPrincipalDominance.lean),
[EtaCurrentPrincipalLowerBound](../RiemannGaussian/EtaCurrentPrincipalLowerBound.lean),
and [EtaCurrentReturnSharpGrowth](../RiemannGaussian/EtaCurrentReturnSharpGrowth.lean).
It applies to the unchanged actual linear-width Gaussian return. Its
off-critical hypothesis is explicit; it supplies no assertion that such
a zero exists or a contradiction excluding one.

Let `e=abs(2*Re(rho)-1)`. The coefficient `A_dom` is `A_rho` when
`Re(rho)<=1/2` and `A_partner` otherwise; `A_fast` is the other coefficient.
Both are strictly positive. The exact signed factorization
`pairedEtaCurrentPrincipalEndpoint_eq_dominant_factor` retains the side
sign `s_rho=-1` on the left of the critical line and `+1` on the right:

\[
 J_{\mathrm{principal}}(\rho,N)=s_\rho\delta_{N+1}
 e^{(e-1)L_N}\left(A_{\mathrm{dom}}-A_{\mathrm{fast}}e^{-2eL_N}\right).
\]

For an actual off-critical zero, `0<e<1` is proved and
`A_fast*exp(-2eL_N)` tends to zero. Eventually the bracket is at least
`A_dom/2`. The literal cutoff geometry also gives

\[
 (2N+1)\delta_{N+1}\ge\frac25,
 \qquad e^{(e-1)L_N}\ge5^{e-1}(N+1)^{e-1}.
\]

Consequently `pairedEtaCurrentPrincipalEndpoint_weighted_lower_eventually`
proves the eventual bound

\[
 (2N+1)|J_{\mathrm{principal}}(\rho,N)|
 \ge c_{\mathrm{floor}}(\rho)(N+1)^{e-1},
 \qquad c_{\mathrm{floor}}(\rho)=\frac{A_{\mathrm{dom}}}{5}5^{e-1}>0.
\]

The finite power-sum lower comparison is

\[
 \frac{(K+1)^e-1}{e}\le\sum_{N<K}(N+1)^{e-1}.
\]

For a finite cutoff `N0` beyond which dominance holds, define the
explicit allowance

\[
 D_\rho(N_0)=\sum_{N\ge0}F_{\mathrm{principal}}(\rho,N)
 +\frac{c_{\mathrm{floor}}(\rho)}e
 +\sum_{N<N_0}c_{\mathrm{floor}}(\rho)(N+1)^{e-1}.
\]

The infinite error sum is already proved summable, and all terms are
nonnegative. The compiled theorem
`pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_lower_with_offset`
constructs such a finite `N0` and proves, at **every** terminal cutoff,

\[
 S_R(\rho,K)\ge
 \frac{c_{\mathrm{floor}}(\rho)}e(K+1)^e-D_\rho(N_0).
\]

It uses the exact first-absolute-moment stability bound; it does not
replace the original return by a model without accounting for the error.
The terminal theorem
`pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_power_bounds_eventually`
therefore proves

\[
 \frac{c_{\mathrm{floor}}(\rho)}{2e}(K+1)^e
 \le S_R(\rho,K)\le C_\rho(K+1)^e
 \quad\text{eventually}.
\]

`pairedEtaCurrentReturnGrowthLowerCoefficient_pos` supplies the strictly
positive lower coefficient. The same module proves
`pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_tendsto_atTop_of_re_ne_half`:
the actual weighted first absolute moment tends to infinity under the
off-critical hypothesis.

The previous growth exponent is thus sharp for the unchanged return at
any hypothetical off-critical zero. A further approximation whose
weighted norm error has a fixed finite sum cannot remove this positive
power growth. The original goal therefore needs an independent
arithmetic argument excluding the surviving off-critical contribution.
The new lower bound does not provide that argument, improve a zero
proportion, or locate an additional zeta zero.

## Checked finite Möbius constraint on the original completed tails

The sharp growth result rules out progress through a smaller summable
local error alone. The next arithmetic input now couples different
prefixes through their actual multiplicative indices. The compiled
modules are [EtaMoebiusDivisor](../RiemannGaussian/EtaMoebiusDivisor.lean),
[EtaMoebiusFinitePrefix](../RiemannGaussian/EtaMoebiusFinitePrefix.lean),
and [EtaMoebiusCompletedTail](../RiemannGaussian/EtaMoebiusCompletedTail.lean).

Let `a(n)=1` for odd `n` and `-1` for even `n`. Mathlib's classical
Möbius inversion theorem gives the exact finite coefficient identity

\[
 \sum_{dk=n}\mu(d)a(k)=\mathbf1_{n=1}-2\mathbf1_{n=2}
 \qquad(n\ge1).
\]

`sum_moebius_mul_pairedEtaDirichletTerm` retains both complex powers
`d^(-s)` and `k^(-s)`, using their exact natural-product identity.
`sum_Icc_divisorsAntidiagonal_eq_sum_divided_prefix` gives a finite
bijection from the divisor fibers to pairs with `1<=d<=M` and
`1<=k<=floor(M/d)`. There is no infinite rearrangement.
Writing `E_m(s)=sum_(1<=k<=m) a(k)k^(-s)`, the resulting identity is

\[
 \sum_{d\le M}\mu(d)d^{-s}E_{\lfloor M/d\rfloor}(s)
 =1-2\,2^{-s},\qquad M\ge2.
\]

Every such prefix is proved to equal the repository's original
`pairedEtaCorePartialSum(m/2,s)` plus `m^(-s)` when `m` is odd.
That endpoint term cannot be omitted. For an actual zero `rho`, let
`X_rho=pairedEtaXiCompletionFactor(rho)` and

\[
 B_\rho(m)=X_\rho\mathbf1_{m\text{ odd}}m^{-\rho}.
\]

The original zeroth completed moment is exactly
`X_rho*pairedEtaCorePartialSum(N,rho)`.
Since the actual multiplicity is positive, its zeroth order is below
the multiplicity and it is the negative genuine completed tail
`-T_rho(N,0)`. Thus the compiled terminal theorem
`pairedEtaCompletedMoebiusTailAggregate_eq_source` proves

\[
 \sum_{d\le M}\mu(d)d^{-\rho}
 \left[-T_\rho\!\left(\left\lfloor
       \frac{\lfloor M/d\rfloor}{2}\right\rfloor,0\right)
       +B_\rho(\lfloor M/d\rfloor)\right]
 =X_\rho(1-2\,2^{-\rho}),\qquad M\ge2.
\]

`pairedEtaCompletedMoebiusSource_ne_zero` proves the right-hand side
nonzero using the actual critical-strip hypotheses. Its norm is therefore
a fixed positive value, independent of `M`, for the complete **signed
linear aggregate**. This is not the original current's weighted first
absolute moment. No quadratic estimate or cancellation of that current
is inferred from this identity.

Möbius inversion itself is classical. The new project interface is its
exact application to the existing completed eta moments, with divided
cutoffs, complex phases, and unpaired endpoints retained. More general
dilation methods are part of the classical
[Nyman–Beurling/Müntz framework](https://arxiv.org/abs/math/0505453);
that connection does not supply the missing approximation or norm estimate.
No priority claim is made here.

The quadratic test below now propagates these simultaneous linear
constraints through the actual completed moment pairs, accounting for
all cross-cutoff terms. Their transfer to the original current and its
Gaussian returns is still open. Taking absolute values before exploiting
the Möbius phases loses the arithmetic cancellation that this identity
has preserved.

## Checked quadratic estimate and surviving cross-cutoff correlations

The compiled modules are
[EtaMoebiusTermBounds](../RiemannGaussian/EtaMoebiusTermBounds.lean) and
[EtaMoebiusQuadratic](../RiemannGaussian/EtaMoebiusQuadratic.lean).
Write `sigma=Re(rho)` and retain each exact completed term as

\[
 F_{\rho,M}(d)=\mu(d)d^{-\rho}
 \left[-T_\rho\!\left(\left\lfloor
       \frac{\lfloor M/d\rfloor}{2}\right\rfloor,0\right)
       +B_\rho(\lfloor M/d\rfloor)\right].
\]

`pairedEtaCompletedMoebiusTerm_eq_completed_prefix` identifies it with
`mu(d)*d^(-rho)*X_rho*E_floor(M/d)(rho)` exactly. No endpoint or phase
has been removed. At every actual zero,
`norm_pairedEtaUnpairedDirichletPrefix_le` proves

\[
 |E_m(\rho)|\le (|\rho|/\sigma+1)m^{-\sigma},\qquad m\ge1.
\]

The original zero-tail bound controls the paired part. The odd endpoint
contributes the additional `1` to the coefficient. For every
`1<=d<=M`, the integer division estimate
`half_le_mul_nat_div` gives `M/2<=d*floor(M/d)`. Keeping the full complex
term before applying its norm yields the compiled bound
`norm_pairedEtaCompletedMoebiusTerm_le`:

\[
 |F_{\rho,M}(d)|\le C_\rho M^{-\sigma},\qquad
 C_\rho=|X_\rho|(|\rho|/\sigma+1)2^\sigma>0.
\]

This coefficient is explicit and independent of both `M` and `d`.
`pairedEtaCompletedMoebiusDiagonal_le` then proves, for every `M>=1`,

\[
 0\le D_\rho(M):=\sum_{d\le M}|F_{\rho,M}(d)|^2
 \le C_\rho^2 M^{1-2\sigma}.
\]

This is a genuine quadratic estimate for the original completed divisor
terms. It does not bound the current's weighted absolute moment.
The complete complex kernel is retained as
`F_rho,M(d)*conj(F_rho,M(e))`. Define its off-diagonal sum by

\[
 O_\rho(M)=\sum_{d\le M}\sum_{\substack{e\le M\\e\ne d}}
 F_{\rho,M}(d)\overline{F_{\rho,M}(e)}.
\]

`pairedEtaCompletedMoebiusOffDiagonal_eq_source_sub_diagonal`
proves the exact complex identity

\[
 O_\rho(M)=|C_{\mu,\rho}|^2-D_\rho(M),\qquad
 C_{\mu,\rho}=X_\rho(1-2\,2^{-\rho})\ne0,\quad M\ge2.
\]

Consequently,
`norm_pairedEtaCompletedMoebiusOffDiagonal_sub_source_le` proves

\[
 \left|O_\rho(M)-|C_{\mu,\rho}|^2\right|
 \le C_\rho^2M^{1-2\sigma}.
\]

The reflected signed kernel uses the existing
`etaSignedCompletedPair(F_partner(d), F_partner(e), F_rho(d), F_rho(e))`.
`sum_offDiagonal_pairedEtaSignedCompletedMoebiusPairKernel`
retains both original completion channels and their exact orientation:
its sum over distinct divisors is the signed source pair minus
`D_partner(M)-D_rho(M)`. The subtraction of the diagonal is an identity,
not permission to omit it or its off-diagonal complement.

At a hypothetical actual zero with `sigma>1/2`, the proved exponent is
negative. The terminal theorem
`pairedEtaCompletedMoebiusOffDiagonal_tendsto_source_of_half_lt_re`
therefore gives

\[
 D_\rho(M)\longrightarrow0,
 \qquad O_\rho(M)\longrightarrow |C_{\mu,\rho}|^2>0.
\]

`pairedEtaCompletedMoebiusOffDiagonal_re_lower_eventually` additionally
proves that the real part is eventually at least
`|C_mu,rho|^2/2`. The distinct-divisor correlations carry a fixed positive
amount even though the positive diagonal energy vanishes. A quadratic
argument must therefore retain and estimate these correlations. Smallness
of the individual terms or their squared-norm sum does not make the
complete pair sum small.

This test provides an explicit arithmetic rate and identifies the terms
that prevent a diagonal reduction. It does not exclude an off-critical
zero. No new zero-location bound, uniform bound for the original return,
or RH theorem follows from this slice. Priority for the auxiliary estimate
has not been established.

## Checked dyadic cancellation in the actual completed correlations

The next arithmetic estimate is now compiled in
[EtaMoebiusEndpointPhase](../RiemannGaussian/EtaMoebiusEndpointPhase.lean),
[EtaMoebiusDyadicPhase](../RiemannGaussian/EtaMoebiusDyadicPhase.lean), and
[EtaMoebiusDyadicCorrelation](../RiemannGaussian/EtaMoebiusDyadicCorrelation.lean).
It applies to the original **zeroth** completed Möbius terms. It uses the
arithmetic parity of their actual divided cutoffs to cancel an entire
odd/even divisor interaction over a full period.

Write

\[
 q(m)=2\lfloor m/2\rfloor+1,
 \qquad
 \widehat F_{\rho,M}(d)=(d\,q(\lfloor M/d\rfloor))^\rho F_{\rho,M}(d),
 \qquad
 V_{\rho,M}(d)=\frac{\mu(d)X_\rho}{2}a(\lfloor M/d\rfloor).
\]

The normalization is the **complex power of each literal divisor times
its paired odd endpoint**. It is not an implicit common cutoff or a
replacement of the original current. The theorem
`pairedEtaCompletedMoebiusEndpointPair_eq_physical_kernel` retains both
such powers multiplying the original complex pair kernel.

`pairedEtaUnpairedDirichletPrefix_endpoint_phase_error` proves the exact
complex identity

\[
 q(m)^\rho E_m(\rho)-a(m)/2
 =-\left(G_{\rho,\lfloor m/2\rfloor}+1/2\right),
\]

where `G` is the repository's original normalized finite eta-gap error.
This uses the actual zero equation and retains the unpaired odd term.
The proved Euler gap estimate and `|mu(d)|<=1` give

\[
 |\widehat F_{\rho,M}(d)-V_{\rho,M}(d)|
 \le \frac{H_\rho}{q(\lfloor M/d\rfloor)}
 \le \frac{2H_\rho d}{M},\qquad M,d\ge1,
 \qquad H_\rho=|X_\rho|\,|\rho|\,|\rho+1|.
\]

The terminal bound for this step is
`norm_pairedEtaCompletedMoebiusEndpointPhase_sub_parity_cutoff_le`.
The divisor dependence is explicit. The coefficient `H_rho` is finite
and independent of both the divisor and the cutoff.

Let `d` be odd and `e=2k` be any positive even divisor. A shift by `d*e`
adds the even number `e` to `floor(M/d)` and the odd number `d` to
`floor(M/e)`. The first parity phase is preserved and the second changes
sign. Consequently,
`sum_pairedEtaCompletedMoebiusParityPair_period_eq_zero` proves, for
every starting integer `A`,

\[
 \sum_{0\le r<2de}V_{\rho,A+r}(d)\overline{V_{\rho,A+r}(e)}=0.
\]

Both completion and Möbius coefficients remain in this exact complex
identity. The proof does not average absolute values of the leading terms.
The actual pair error is then split at both complex positions before
taking its norm. Define

\[
 \mathcal E_\rho(d,e,A)=
 \frac{H_\rho|X_\rho|(d+e)}{A}
 +\frac{4H_\rho^2de}{A^2}.
\]

`norm_pairedEtaCompletedMoebiusDyadicCorrelation_le` proves

\[
 \left|\frac1{2de}\sum_{0\le r<2de}
   \widehat F_{\rho,A+r}(d)\overline{\widehat F_{\rho,A+r}(e)}\right|
 \le \mathcal E_\rho(d,e,A),\qquad A\ge1.
\]

This controls the actual completed terms, including their finite-tail
error. The quadratic error term `de/A^2` is retained. For each fixed pair
of divisors the right side tends to zero, giving the compiled limit
`pairedEtaCompletedMoebiusDyadicCorrelation_tendsto_zero` at every
actual zero, without a critical-line hypothesis.

The original `etaSignedCompletedPair` orientation is carried through the
same period average. Its exact channel identity is the partner average
minus the conjugate original average. The terminal theorem
`norm_pairedEtaSignedCompletedMoebiusDyadicCorrelation_le` bounds its
norm by

\[
 \mathcal E_{\rho^*}(d,e,A)+\mathcal E_\rho(d,e,A).
\]

`pairedEtaSignedCompletedMoebiusDyadicCorrelation_tendsto_zero`
proves the corresponding signed limit with both actual completion
channels. No multiplicity-one assumption is used; the carrier here is
still the zeroth completed moment, not all higher centered orders.

The arithmetic cancellation is a new checked estimate on an existing
carrier. Its present limits matter to the full goal: the normalizers
depend on the divisor, the period length is `2*d*e`, and the error grows
with both divisor sizes. A fixed-pair period average does not control the
growing divisor family at a single cutoff or the original weighted
absolute-return sum. The same-parity interactions, higher centered
orders, and simple-zero head must still be handled in any transfer to
that target. No zero-location bound or RH theorem is claimed here.

As a research check, the related Nyman–Beurling asymptotic of
[Bettin–Conrey–Farmer](https://arxiv.org/abs/1211.5191) assumes RH and an
additional derivative-moment estimate. It supplies no unconditional
bound for this goal. The estimate above instead uses the repository's
proved Euler error and a finite parity identity; no external analytic
premise was added. Priority for the combined auxiliary mathematics has
not been established.

### Global parity recurrences and uniform block bounds

The growing zeroth-order divisor family is now controlled at each physical
cutoff by an exact recurrence, rather than by summing fixed-pair error
bounds. The source object is unchanged:

\[
 F_{\rho,M}(d)=\mu(d)d^{-\rho}X_\rho
 E_{\lfloor M/d\rfloor}(\rho),\qquad
 O_\rho(M)=\sum_{\substack{1\le d\le M\\d\text{ odd}}}F_{\rho,M}(d),
 \quad E_\rho(M)=\sum_{\substack{1\le d\le M\\d\text{ even}}}F_{\rho,M}(d).
\]

Here the unpaired prefix in the first expression is still exactly the
negative actual completed tail plus its possible odd endpoint, with the
original completion factor. The symbol `E_rho(M)` in the last expression
denotes the even aggregate, not that prefix. Put
`r_rho = 2^(-rho)` and `C_rho = X_rho*(1-2*r_rho)`.

`pairedEtaCompletedMoebiusEvenAggregate_eq_half_odd` and
`pairedEtaCompletedMoebiusOddAggregate_recurrence` prove the exact
complex identities

\[
 E_\rho(M)=-r_\rho O_\rho(\lfloor M/2\rfloor),\qquad
 O_\rho(M)=C_\rho+r_\rho O_\rho(\lfloor M/2\rfloor)\quad(M\ge2).
\]

The initial values are `O_rho(0)=0` and `O_rho(1)=X_rho`. The proof uses
the checked coefficient identity
`mu(2*d) = if Odd d then -mu(d) else 0` and a bijection of the entire
even divisor set with the halved cutoff. All endpoints and complex phases
survive these steps. The full finite Möbius source identity supplies the
second recurrence.

Since `a_rho = |r_rho| = 2^(-Re rho) < 1`, define the explicit finite
constant

\[
 B_\rho=|X_\rho|+\frac{|C_\rho|}{1-a_\rho}.
\]

The terminal theorems `norm_pairedEtaCompletedMoebiusOddAggregate_le`
and `norm_pairedEtaCompletedMoebiusEvenAggregate_le` prove, for every
natural cutoff including zero,

\[
 |O_\rho(M)|\le B_\rho,\qquad |E_\rho(M)|\le a_\rho B_\rho.
\]

Strong induction on the cutoff applies the strict contraction at its
halved argument. There is no divisor-dependent normalizer, period average,
or restriction to a fixed divisor family in these bounds.

For parity labels `p,q`, let `A_rho(M,p)` be the appropriate odd or even
aggregate and `b_rho(p)` its above bound. The literal block retains
every pair at the common physical cutoff:

\[
 Q_\rho(M;p,q)=\sum_{d\in I_p(M)}\sum_{e\in I_q(M)}
 F_{\rho,M}(d)\overline{F_{\rho,M}(e)}.
\]

`pairedEtaCompletedMoebiusParityBlock_eq_pair` identifies this with
`A_rho(M,p)*conj(A_rho(M,q))` before applying any norm. The theorem
`norm_pairedEtaCompletedMoebiusParityBlock_le` bounds all four block
sums by `b_rho(p)*b_rho(q)`, including the same-parity interactions.
For the original signed reflected kernel,
`pairedEtaSignedCompletedMoebiusParityBlock_eq_channels` retains the
partner block minus the conjugate original block. The terminal estimate
`norm_pairedEtaSignedCompletedMoebiusParityBlock_le` gives

\[
 |Q^{\mathrm{signed}}_\rho(M;p,q)|\le
 b_{\rho^*}(p)b_{\rho^*}(q)+b_\rho(p)b_\rho(q).
\]

These are uniform bounds on the **sums of the full blocks**, not sums of
the absolute values of their entries or bounds for arbitrary
divisor-dependent feature vectors. They also do not sum over physical
cutoffs with the original current's weights. They hold throughout
`0 < Re rho < 1`, so the estimate itself does not exclude an off-critical
zero. The existing conditional power-growth theorem for the original
return remains compatible with them. A proved estimate recovering the
original current from the retained divisor data is still missing,
including the higher centered moments and the simple-zero head. The
contraction and finite inversion are classical arithmetic; no priority
claim is made for their application here.

### Exact inverse to the original current and its weight cost

The first transfer identity is now proved, with its missing estimate
distinguished from the identity. Classical odd-divisor inversion gives
`sum_pairedEtaCompletedOddInverseTerm`:

\[
 X_\rho E_M(\rho)=\sum_{\substack{1\le d\le M\\d\text{ odd}}}
 d^{-\rho}O_\rho(\lfloor M/d\rfloor).
\]

The prefix `E_M` in this formula is the original unpaired Dirichlet
prefix. The proof checks the odd-restricted Möbius convolution, retains
the exact complex product powers, and regroups only finite divisor
fibers. It includes cutoff zero with its actual zero initial value.
At an even endpoint, `pairedEtaFiniteCompletedMoment_zero_eq_oddInverse`
therefore gives the original completed moment

\[
 A_\rho(N,0)=\sum_{\substack{1\le d\le2N\\d\text{ odd}}}
 d^{-\rho}O_\rho(\lfloor2N/d\rfloor).
\]

For the head current put `M=2*(N+2)` and define, just for this display,
`B_rho(N,d)=d^(-rho)*O_rho(floor(M/d))`. Before taking its real part,
`pairedEtaHeadCompletedMomentPair_zero_eq_oddInverse` retains the
complex signed sum

\[
 \sum_{\substack{1\le d\le M\\d\text{ odd}}}
 \operatorname{etaSignedCompletedPair}
   (H_{\rho^*}(N,0),B_{\rho^*}(N,d),H_\rho(N,0),B_\rho(N,d)).
\]

`pairedEtaLeadingCurrent_eq_oddInverse_head` proves that twice the real
part of this sum is exactly `J_rho(N)` when the actual multiplicity is
one. The original shifted head coordinate, successor prefix cutoff,
completion factors, and conjugation orientation all remain unchanged.
This is a proved connection to the original current in that branch,
not a bound for its weighted absolute moment. Higher centered orders
are not covered by this zeroth-order inverse.

Taking norms term by term introduces the literal weight mass

\[
 W_\rho(M)=\sum_{\substack{1\le d\le M\\d\text{ odd}}}|d^{-\rho}|.
\]

`norm_completed_pairedEtaUnpairedDirichletPrefix_le_oddInverseWeightMass`
proves the resulting bound `|X_rho E_M(rho)| <= B_rho W_rho(M)` using the
previous uniform odd-aggregate constant. The exact index count and the
finite integral comparison now give

\[
 \frac{M^{1-\sigma}}2\le W_\rho(M)\le
 \frac{(M+1)^{1-\sigma}}{1-\sigma}\qquad(M\ge1),
 \quad \sigma=\Re\rho.
\]

The compiled endpoints are `pairedEtaOddInverseWeightMass_lower`,
`pairedEtaOddInverseWeightMass_upper`, and
`pairedEtaOddInverseWeightMass_tendsto_atTop`. In particular, the weight
cost diverges at **every** actual zero, including the critical line.
This diagnoses the loss in this particular triangle estimate. It does
not prove that the inverse operator norm diverges after grouping equal
divided cutoffs, nor that the original signed current diverges. No
cancellation in the richer inverse sum has been ruled out.

The next estimate must therefore act on that weighted signed sum before
absolute values, with an accumulated cutoff bound strong enough for the
original `S_rho(K)`. Merely inserting the uniform aggregate constant
under a sum of inverse-weight norms cannot give it. The inversion and
power comparison are classical; no novelty priority is claimed.

### Grouped inverse Mellin phases and actual cross-cutoff cancellation

The next test sums the inverse weights with a common divided cutoff
before taking any norm. It therefore goes beyond the previous sum of
individual weight norms. At physical cutoff `4*K`, all odd indices in
`2*K < d <= 4*K` have divided cutoff one. The complete power sum is

\[
 G_\rho(K)=\sum_{0\le k<K}(2K+2k+1)^{-\rho},\qquad
 b_\rho=\frac{2^{1-\rho}-1}{2(1-\rho)}.
\]

`norm_pairedEtaOddTopPowerSum_sub_half_integral_le` compares this
literal midpoint sum with half its complex power integral. The proof
uses an explicit positive-axis derivative bound, checks interval
integrability, and joins every adjacent interval exactly. The theorem
`half_integral_cpow_eq_pairedEtaOddTopPowerMain` evaluates that integral
without discarding its phase. Consequently
`norm_pairedEtaOddTopPowerSum_sub_main_le` proves

\[
 \left|G_\rho(K)-(2K)^{1-\rho}b_\rho\right|
 \le \frac{|\rho|}{2}(2K)^{-\sigma},\qquad K\ge1,
 \quad\sigma=\Re\rho.
\]

The coefficient retains its ordinate dependence. It is nonzero throughout
the open critical strip: `pairedEtaOddTopPowerCoefficient_ne_zero` uses
`|2^(1-rho)|=2^(1-sigma)>1`. The lower estimate
`pairedEtaOddTopPowerSum_norm_lower_of_cutoff` gives

\[
 |G_\rho(K)|\ge\frac{|b_\rho|}{2}(2K)^{1-\sigma}
 \quad\text{if }K\ge1\text{ and }|\rho|\le2K|b_\rho|.
\]

`pairedEtaOddTopPowerSum_norm_tendsto_atTop` therefore proves that
this **whole grouped coefficient**, not only its termwise absolute
majorant, is unbounded. No inverse operator norm is introduced here.

For the actual completed inverse define its two retained pieces

\[
 T_\rho(K)=\sum_{\substack{2K<d\le4K\\d\text{ odd}}}
 d^{-\rho}O_\rho(\lfloor4K/d\rfloor),\qquad
 B_\rho(K)=\sum_{\substack{1\le d\le2K\\d\text{ odd}}}
 d^{-\rho}O_\rho(\lfloor4K/d\rfloor).
\]

The symbols `B_rho(K)` and `b_rho` here denote the bottom inverse block
and Mellin coefficient, respectively, not the earlier uniform parity
constant. `pairedEtaCompletedOddInverseTop_eq_powerSum` gives the exact
complex equality `T_rho(K)=X_rho*G_rho(K)`. The finite partition theorem
`pairedEtaCompletedOddInverseBottom_add_top` retains
`B_rho(K)+T_rho(K)=A_rho(2*K,0)`.

With `L_rho(K)=X_rho*(2*K)^(1-rho)*b_rho`, the terminal estimates are

\[
 |T_\rho(K)-L_\rho(K)|
 \le |X_\rho|\frac{|\rho|}{2}(2K)^{-\sigma},
\]
\[
 |B_\rho(K)+L_\rho(K)|
 \le |X_\rho|\left[
 (|\rho|/\sigma+1)(4K)^{-\sigma}
 +\frac{|\rho|}{2}(2K)^{-\sigma}\right].
\]

These are `norm_pairedEtaCompletedOddInverseTop_sub_main_le` and
`norm_pairedEtaCompletedOddInverseBottom_add_main_le`. The latter
uses the actual zero-prefix decay only after retaining the exact sum
of the two inverse blocks. The theorem
`pairedEtaCompletedOddInverseTop_norm_tendsto_atTop` proves that the
top completed piece itself is unbounded. Its growing phase is canceled
by the other divided cutoffs, with the explicit decaying error above.

Thus grouping equal cutoffs does not justify bounding each grouped
inverse piece separately by a cutoff-independent constant. The new
constraint preserves the cancellation across different cutoffs that
such a transfer would lose. It is still a zeroth-moment statement,
valid separately in both completion channels, and does not establish
the original signed current's uniform weighted absolute moment. The
existing conditional off-critical power growth remains compatible with
all these identities. Midpoint quadrature and Mellin integration are
classical; no priority claim is made for this application.

### Independent prime positivity and an explicit zero margin

The preceding inverse identities are compatible with off-critical power
growth. A new arithmetic input comes from the classical three-four-one
Euler-product inequality, already proved in pinned Mathlib as
`DirichletCharacter.norm_LFunction_product_ge_one`. Its specialization
`one_le_riemannZeta_three_four_one` preserves the actual zeta values:

\[
 1\le |\zeta(1+x)|^3|\zeta(1+x+i\gamma)|^4
       |\zeta(1+x+2i\gamma)|,\qquad x>0.
\]

No positivity of a difference of heat Grams is inferred. Instead, the
literal eta support bound supplies the needed analytic upper estimates.
Write `Z1(s)=riemannZeta₁(s)` for Mathlib's entire completion of
`(s-1)*zeta(s)` at one. `norm_pairedEtaCore_le_div_re` proves
`|eta(s)| <= |s|/Re(s)` throughout the positive half-plane. The exact
identity `pairedEtaCore_mul_sub_one_eq_factor_riemannZeta₁` retains

\[
 (s-1)\eta(s)=(1-2\cdot2^{-s})Z_1(s),
\]

including the removable point. Rectangles centered at integer multiples
of `2*pi/log(2)` have horizontal edges at dyadic phase minus one and
vertical edges at real parts `1/2` and `3/2`. The factor's norm is at least
`1/4` on the full boundary. The maximum-modulus principle for the entire
`Z1` therefore crosses all interior dyadic resonances without dividing
by a vanishing factor. The terminal bounds are

\[
 |Z_1(s)|\le8(|\Im s|+20)^2,
 \qquad \tfrac12\le\Re s\le\tfrac32,
\]
\[
 |Z_1'(s)|\le32(|\Im s|+21)^2,
 \qquad \tfrac34\le\Re s\le\tfrac54.
\]

These are `norm_riemannZeta₁_le_etaStrip` and
`norm_deriv_riemannZeta₁_le_etaStrip`; the latter uses Cauchy's estimate
on an actual disc of radius `1/4`. The horizontal mean-value theorem
then compares the original function to a genuine zero. For
`rho=sigma+i*gamma`, `sigma>=3/4`, `d=1-sigma`, and `t=|gamma|`,
`norm_riemannZeta₁_reflected_across_one_le` gives

\[
 |Z_1(1+d+i\gamma)|\le64(t+21)^2d.
\]

The zero's ordinate is nonzero by the strict positivity of the original
eta mass at frequency zero, checked in
`NontrivialZetaZero.im_ne_zero_of_eta_mass`. The pole denominator and
the same strip bound also prove

\[
 |\zeta(1+d)|\le3200/d,\qquad
 |\zeta(1+d+2i\gamma)|\le16(t+21)^2/t.
\]

Combining these actual upper bounds with prime positivity yields
`one_le_etaPrimeProduct_zero_gap`:

\[
 1\le\frac{16\cdot3200^3\cdot64^4(t+21)^{10}}{t^5}(1-\sigma).
\]

Define the explicit function, with the Cauchy strip threshold retained,

\[
 \delta(y)=\min\left\{\frac14,
 \frac{|y|^5}{16\cdot3200^3\cdot64^4(|y|+21)^{10}}\right\}.
\]

It is strictly positive when `y!=0` by
`etaPrimeProductZeroMargin_pos`. Reflection supplies the left margin
at the same ordinate. Thus
`nontrivialZetaZero_mem_etaPrimeProduct_strip` proves for **every actual
nontrivial zero**, with no growth or zero-free premise,

\[
 \delta(\gamma)\le\sigma\le1-\delta(\gamma).
\]

This is a deliberately crude zero-location bound derived using classical
methods. The [classical prime-positivity argument](https://people.math.harvard.edu/~elkies/M229.20/free.pdf)
has long supported substantially stronger analytic zero-free regions;
no improvement over that literature or novelty priority is claimed here.
The contribution to this proof chain is the fully discharged eta-based
estimate and its transport to the unchanged current/return exponent.

Specifically,
`pairedEtaCurrentHorizontalDisplacement_le_etaPrimeProduct` bounds
`abs(2*sigma-1)` by `1-2*delta(gamma)`, and
`pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_le_etaPrimeProduct`
proves

\[
 S_R(\rho,K)\le C_\rho(K+1)^{1-2\delta(\gamma)}.
\]

The existing completion- and multiplicity-dependent constant is retained.
Both analytic multiplicity branches are covered by the original return
growth theorem. `etaPrimeProduct_return_exponent_bounds` explicitly places
the new exponent in `[1/2,1)`. It therefore still permits cutoff growth.
The interior off-critical contribution remains unexcluded, and the full
cutoff-independent weighted arithmetic estimate remains open.

## Next mathematical obligations

The independent prime-product input now excludes the explicit edge regions
above. It does not force real part `1/2`, and its return bound has a proved
positive exponent. The remaining task is to rule out the interior
off-critical contribution while retaining the unchanged absolute weighted
target. The following inverse and heat carriers remain available for that
task; their established identities alone do not supply the missing estimate.

1. Prove cancellation in the exact inverse-weighted signed head sum
   above, strong enough to bound the original current's weighted absolute
   moment, and supply the corresponding higher-centered-order control.
   The entire odd and even aggregate and all four quadratic block sums
   already have uniform bounds at one physical cutoff. The simple-zero
   current now has an exact reconstruction from those odd aggregates.
   Its termwise absolute inverse-weight cost, however, has proved growth
   `M^(1-Re rho)`; bounding each aggregate separately cannot close this
   transfer estimate. Summing phases within an equal-cutoff block also
   leaves a proved positive-power main term. The complementary cutoffs
   cancel that term with the quantitative complex error above, so their
   interaction must survive any subsequent estimate for the signed pair.
   This zeroth-moment cancellation alone does not exclude an off-critical
   zero or improve the known sharp original-return exponent. Any use of the earlier
   fixed-pair estimate must still account for its divisor-dependent
   normalizers and averaging period. The earlier diagonal bound has a complementary correlation
   sum with a possible nonzero limit; that sum cannot be dropped.
   No uniform estimate for the original weighted return is currently proved.
   All cross-cutoff terms and odd endpoint corrections must be retained. The
   proved matching power bounds show that removing the cutoff growth
   requires such an exclusion; a sharper local approximation alone cannot
   provide it. The signed Euler, half-step head, and heat reconstruction
   errors are now summable in both actual multiplicity branches. Bounds for a positive heat Gram
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

The checked two-transition comparison also remains available for a
quantitative comparison between heat scales with the completion channels
retained. Any use of it must respect the surviving cross-cutoff
correlations above. The table distinguishes the completed identity from
proposed estimates and longer-path targets. None of the open targets is
a premise to add to Lean:

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
linear-width summability, signed principal errors, and matching conditional
off-critical power bounds for the actual weighted return are now proved.
Excluding the surviving off-critical endpoint contribution remains open. The next targets are
**proposed work**, not assumptions to add to the proof chain.

1. Seek an arithmetic estimate on the retained cross-cutoff interactions
   that controls the original completed moment pairs. Their finite
   Möbius constraint, positive diagonal bound, and odd/even fixed-pair
   cancellation are now checked, as are the uniform bounds for the whole
   growing parity aggregates and all four signed block sums. The exact
   simple-zero current now reconstructs by the odd inverse formula.
   Its inverse-weight mass has positive-power growth even on the critical
   line; the next estimate must exploit cancellation in the weighted
   signed sum rather than replace it with termwise absolute values.
   The grouped top inverse block now has its nonzero Mellin main term,
   and the complementary cutoffs have the opposite term with a decaying
   error. These relations must remain available when estimating the
   two completed channels together.
   Higher-centered-order estimates also remain open.
   Any use of the earlier period averages must also preserve their
   divisor-dependent normalizers and errors. Any use of the
   mixed phase matrix must identify the actual finite eta feature vector
   and control its dimension, scale, and compression errors. The above
   midpoint and Euler error estimates alone cannot bound `S_rho(K)`
   independently of cutoff. The proved lower bound forces growth
   under the hypothesis that the actual zero is off the critical line.
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
