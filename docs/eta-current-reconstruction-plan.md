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
| Compare ordered heat compositions on the actual domain | The exact continuous composition, full three-time integrability, and new zero-tilt weighted reconstruction above. | The normalization and reconstruction error are now controlled with quadratic width. The next estimate must preserve cancellation of the signed completed current against the composed term and both corrections. |
| Keep all support/gap paths | The actual two-transition decomposition above, the finite two-stage identity in [ProjectionHeatLeakage](../RiemannGaussian/Hybrid/ProjectionHeatLeakage.lean), and ordered cubic paths in [EtaSpectralHeatCubicPaths](../RiemannGaussian/Hybrid/EtaSpectralHeatCubicPaths.lean). | For any longer-path comparison, prove its identities on the actual continuous eta measure and pair every path with both completed current branches. Include every omitted-time and compression term with its sign. The existing finite matrix algebra alone is insufficient. |
| Test a quantitative scale comparison | The signed two-endpoint heat law, full mixed phase matrix, and the new reconstruction error budget. | Derive an estimate for the actual signed return with cutoff, phase-family size, moving tilt, multiplicity, and accumulated path error explicit. A sufficient endpoint would be a summable majorant for `(2N+1)‖R_N‖`; the exact target is a bound on its partial sums uniform in `K`. |

The decisive test is whether the zero condition and completion symmetry
supply a new cancellation in that comparison. Positive Gram bounds, a
fixed-size matrix limit, or discarding path signs cannot provide it by
themselves. In particular, fixed moving-tilt asymptotics do not control a
fixed off-axis zero: their tilt parameter grows with the logarithmic scale.
If no estimate survives these dependencies, the next result should state
the obstruction precisely rather than rename it as another RH criterion.

### A concrete next overnight experiment in Lean

The new normalization suggests a more specific use of the repository's
evaluated Wallis constants. These are **proposed targets**, not results or
assumptions to add to the theorem chain. Write `ell=log(pi/2)`.

1. Prove a quantitative Wallis limit for the literal cumulative colour
   imbalance `A(t)=integral_0^t (indicator_support-indicator_gap)`.
   The target is `|A(t)-ell| <= C*exp(-t)` for `t>=0`, with a proved
   universal constant. The existing periodic colour and Wallis proofs
   supply arithmetic building blocks; this cumulative statement still
   needs its own proof.
2. Integrate that exact primitive against the Gaussian derivative. The
   candidate broad-width expansion, uniform for `c>=0` and `h>=2`, is
   `g_h(c)=1/4+(c-ell)/(4*sqrt(pi)*h)+O((1+c)^3/h^3)`, with an explicit
   remainder bound replacing the `O` notation in Lean. This would connect
   the evaluated eta endpoint constant to the new full-gap normalization.
3. Carry the expansion through the original signed current before taking
   norms. Its candidate first correction is
   `R_rho,N(h)-J_rho(N) = M_rho,N/(sqrt(pi)*h) + error`, where
   `M_rho,N` is the actual current integral against `(t+u)/2`, using the
   restored head coordinate when necessary. Express this moment in the
   existing finite eta moments and apply only the vanishing identities
   justified by the actual zero's multiplicity. Determine whether the
   completed reflected channels cancel a term that a positive Gram loses.

This session has a clear decision point: either the signed moment gives
an arithmetic gain beyond the current absolute envelope, or the calculation
identifies a surviving term. In the latter case, a checked two-width
subtraction `2*R(2h)-R(h)` could remove the first heat correction, but that
would improve reconstruction only. It would not count as progress on the
uniform weighted current bound without an independent estimate on the
resulting signed return. Broader claims of novelty require comparison with
the literature; Gaussian asymptotics and operator positivity by themselves
are established techniques.

No reconstruction or summability premise has been introduced as an axiom.
The goal remains open because the uniform weighted arithmetic estimate is
not yet established. No `13/18` certificate or RH proof is claimed.
