# RiemannGaussian

[![Lean Action CI](https://github.com/dbsanfte/RiemannGaussian/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/dbsanfte/RiemannGaussian/actions/workflows/lean_action_ci.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)

RiemannGaussian is an open research project building toward a complete,
kernel-checked Lean proof of the Riemann hypothesis. The repository contains
the evolving Lean 4 proof development and supporting analytic and finite-model
theory. The proof is not complete; in the meantime, the extensive Lean theorems and formalizations that we've compiled along the way are provided to the wider community. Only declarations accepted by Lean and the
repository's verification gates count as established results. 

> **Research agent:** GPT-5.6 Sol with **Max** reasoning effort, running in the
> **Codex CLI harness**.

![Lean-verified RiemannGaussian theorem inventory](docs/proof-status.svg)

This panel is generated from Lean's compiled environment. A checkmark means
that the named theorem is kernel-checked; it is not a measure of proximity to
RH. Its boxes are deliberately not connected as a proof chain: green denotes
unconditional analytic infrastructure, purple an RH-equivalent reformulation,
and blue/cyan verified identities or reductions. In particular, proving that
a detector is equivalent to RH does not establish either side. Orange is the
conjecture-strength open mathematics, and its dashed arrow is explicitly
unproved. No current theorem derives an RH-equivalent vanishing condition from
unconditional arithmetic estimates. CI rejects a stale generated panel. The
machine-readable companion is [docs/proof-status.json](docs/proof-status.json).

## Current Direction

Combine literal eta colour, phase probes, and Gaussian gap returns with the completed arithmetic current. Both current branches now have explicit endpoint expressions with summable weighted arithmetic and heat errors. The repeated-zero expression retains two positive coefficients with complementary decay rates and no cutoff Fourier oscillation. Next, seek arithmetic control of this surviving contribution. The uniform weighted return bound remains open.

## Latest Update

The original signed current and its actual linear-width return now differ
from an **explicit completed Euler endpoint expression** by a summable
odd-weighted error. This is an arithmetic estimate on both original
multiplicity branches, with all completion constants retained; see
[pairedEtaLeadingCurrentLinearHeatReturn_weighted_euler_error_le](RiemannGaussian/EtaCurrentEulerEstimate.lean)
and its finite error-sum bound.

The [simple-zero head evaluates exactly in endpoint exponentials](RiemannGaussian/EtaCurrentEulerArithmetic.lean).
In the repeated-zero branch, the common endpoint phase cancels exactly,
leaving a signed difference of **two positive coefficients with
complementary horizontal decay rates**. The weighted endpoint expression
itself remains uncontrolled. The [research ledger](docs/eta-current-reconstruction-plan.md)
records why a bound on oscillatory errors alone cannot finish this route.
RH remains open. No `13/18` certificate exists.

## Notable Formalisations

Selected entry points into the Lean library are listed below. Each link names
a compiled theorem; its source records the precise domains and hypotheses.

| Area | What is formalised | Lean entry points |
| --- | --- | --- |
| **Gaussian/Weil explicit formula** | The arithmetic Gaussian expression, including prime-power and Archimedean terms, equals the canonical multiplicity-weighted symmetric zeta-zero sum for every positive width. | [gaussianArithmeticExplicitFormula_eq_canonical](RiemannGaussian/GaussianXiLogDerivativeGrowth.lean#L1235) |
| **Gaussian heat and reflected-zero Grams** | The complete matched Gaussian correlation equals the boundary heat-residue sum. At positive heat time, its vanishing is equivalent to RH. | [riemannXiUpperReflectedPairGaussianTotal_eq_boundaryHeatResidueTotal](RiemannGaussian/RiemannXiBoundaryGaussianGram.lean#L187), [riemannXiUpperReflectedPairGaussianTotal_eq_zero_iff_rh](RiemannGaussian/RiemannXiBoundaryGaussianGram.lean#L197) |
| **Suzuki arithmetic and spectral formulas** | Suzuki's positive-time arithmetic function equals its spectral expansion on `Im z > 1/2`. The literal arithmetic `Psi` is strictly positive on a nonzero punctured neighbourhood of the origin. | [riemannXiSuzukiArithmeticPPositive_eq_spectral_safe](RiemannGaussian/RiemannXiSuzukiWeilVerticalLimit.lean#L462), [exists_pos_on_abs_riemannXiSuzukiPsi](RiemannGaussian/RiemannXiSuzukiPointwiseLocalPositivity.lean#L298) |
| **Xi growth and divisor summability** | Unconditional `exp(O(R log R))` xi growth and convergence of the multiplicity-weighted inverse-square zero series. | [riemannXi_logLinearGrowth](RiemannGaussian/GaussianXiLogLinearGrowth.lean#L315), [summable_distinct_zetaZeroInverseSquareNorm](RiemannGaussian/GaussianXiInverseSquareSummability.lean#L294) |
| **Finite Hardy-space geometry** | Orthogonality in genuine boundary `L²`, including repeated roots, and a basis-independent determinant formula for the residual Gram operator. | [finiteModelBoundaryLp_inner_residualInner_negative_eq_zero](RiemannGaussian/FiniteHardyOrthogonality.lean#L260), [finiteHardyCrossAngleComplementGramOperator_det_eq_basisResidual_ratio](RiemannGaussian/FiniteHardyMetricDeterminant.lean#L294) |
| **Eta as a positive-measure Laplace transform** | On `Re s > 0`, paired eta divided by `s` is exactly the Laplace transform of Lebesgue measure restricted to the alternating logarithmic intervals `(log(2n+1), log(2n+2)]`. | [integral_exp_neg_mul_pairedEtaLogMeasure_eq_pairedEtaCore_div](RiemannGaussian/RiemannXiSuzukiPositiveCriticalStripEtaInfiniteLaplaceMeasure.lean#L219) |
| **Critical eta support/gap heat law** | A phase-resolved boundary decomposition on the actual eta intervals gives the sharp critical term `(2/√π) h log(1/h)` with error at most `32h`; the stronger phase-profile error is uniform in the ordinate. | [pairedEtaPhaseMismatch_boundary_error_le](RiemannGaussian/EtaLogSupportShift.lean), [pairedEtaSupportGapGaussianLeakage_uniform_error_le](RiemannGaussian/EtaSupportGapGaussian.lean#L349) |
| **Continuous eta phase matrix coercivity** | Mixed phase entries retain their complex Gram integral. Distinct integer probes give the full matrix lower bound `K(h) ≥ h(c* log(1/h) − 32m) I`, with an explicit dimension cost and small-width threshold. | [pairedEtaSupportGapPhaseGram_complex_energy_eq_integral](RiemannGaussian/Hybrid/EtaSupportGapPhaseGram.lean#L304), [pairedEtaSupportGapScaledPhaseGram_integer_coercive](RiemannGaussian/Hybrid/EtaSupportGapPhaseCoercivity.lean#L276) |
| **Eta heat/spectral correspondence** | The actual support/gap heat transfer equals `(1/π) ∫ exp(-h²(y-γ)²) Re(P(s) conj(1/s-P(s))) dy` on every vertical line `Re s > 0`. The uniform critical heat estimate consequently bounds the literal eta spectral correlation. | [pairedEtaSupportGapGaussianLeakage_eq_eta_spectral](RiemannGaussian/EtaSupportGapGaussianSpectral.lean), [pairedEtaSupportGapSpectralKernel_uniform_error_le](RiemannGaussian/EtaSupportGapGaussianSpectral.lean) |
| **Finite cutoffs and continuous commutator kernels** | Explicit cutoff and fixed-ordinate errors; exact half-tilt commutator factorization, square-integrability, and mixed phase kernel inner products. A logarithmically growing finite cutoff preserves the critical heat profile. | [pairedEtaSupportGapGaussianLeakage_cutoff_error_le](RiemannGaussian/EtaSupportGapGaussianCutoff.lean#L92), [integral_pairedEtaHeatCommutatorPhaseKernel_mixed](RiemannGaussian/Hybrid/EtaSupportGapHeatCommutator.lean#L215) |
| **Complex weighted eta boundary distribution** | The actual critical boundary measure converges on logarithmic time to the uniform distribution on `[0,1]`, against bounded Lipschitz complex tests. An explicit `(12B + 4K)r` error preserves the test's phase. | [pairedEtaWeightedMismatch_critical_error_le](RiemannGaussian/EtaLogWeightedBoundary.lean), [pairedEtaWeightedMismatch_scaled_tendsto](RiemannGaussian/EtaLogWeightedBoundaryLimit.lean) |
| **Joint cubic-phase and moving-tilt heat law** | The actual complex displacement and continuous heat have a joint critical scaling profile. A phase-independent polynomial majorant justifies the Gaussian limit; every mixed matrix entry converges to a Gram with an explicit integral-of-squares formula. | [pairedEtaSupportGapGaussianLeakage_cubic_movingTilt_tendsto](RiemannGaussian/EtaCubicHeatLimit.lean), [pairedEtaCubicHeatProfileGram_energy_eq_squares](RiemannGaussian/Hybrid/EtaCubicHeatGram.lean), [pairedEtaSupportGapCubicPhaseGram_tendsto](RiemannGaussian/Hybrid/EtaCubicHeatGram.lean) |
| **Actual eta overlap and Wallis tail** | The literal logarithmic support becomes a periodic unit-interval colour. Its triangular average has an exact Wallis integral, and the actual infinite inverse-square tail has error at most `4ε/a + ε/a²` for every real `0 < ε ≤ 1`, `0 < a ≤ 1`. | [pairedEtaLogShiftMismatch_eq_rescaledOverlap](RiemannGaussian/EtaOverlapAveraging.lean), [integral_Ioi_etaOverlapProfile_div_sq](RiemannGaussian/EtaOverlapWallis.lean), [integral_Ioi_etaRescaledOverlap_div_sq_error_le](RiemannGaussian/EtaOverlapTail.lean) |
| **Evaluated critical eta finite part** | After the critical divergence, the literal mismatch has the constant `γ_E − log(π/2)`: `D₁/₂(r)/r − log(1/r)` converges to it for all positive real displacements tending to zero. Constant complex tests retain their value. | [pairedEtaMismatch_half_finite_part_tendsto](RiemannGaussian/EtaLogFinitePart.lean), [pairedEtaWeightedMismatch_const_finite_part_tendsto](RiemannGaussian/EtaLogFinitePart.lean) |
| **Complex two-endpoint eta law** | The actual weighted finite part converges to `(γ_E−1)F(0) + (1−log(π/2)+d)F(1)` when `log(1/r)−R → d`. The proof retains uniform errors; Gaussian scaling has the checked offset `d = −log(v)`. | [pairedEtaWeightedMismatch_endpoint_error_le](RiemannGaussian/EtaLogTwoEndpoint.lean), [pairedEtaWeightedMismatch_two_endpoint_tendsto](RiemannGaussian/EtaLogTwoEndpointLimit.lean), [pairedEtaWeightedMismatch_exp_scaled_finite_part_tendsto](RiemannGaussian/EtaLogTwoEndpointLimit.lean) |
| **Second-order eta heat and signed reflection** | The actual polynomial-phase heat has its evaluated second-order coefficient, including the logarithmic Gaussian moment. Exact leading cancellation proves the signed endpoint difference `J(κ) − exp(−2λ)J(κ+β+3α)`. | [pairedEtaSupportGapGaussianLeakage_polynomial_finite_part_tendsto](RiemannGaussian/EtaPolynomialHeatFinitePart.lean), [pairedEtaSignedPolynomialHeat_tendsto](RiemannGaussian/EtaPolynomialHeatReflection.lean) |
| **Full signed mixed heat matrix** | Every mixed entry of the actual polynomial-phase matrix has its second-order law and signed two-endpoint limit. The total entrywise error tends to zero for fixed finite families, with an explicit `n²ε` bound from simultaneous entry errors. | [pairedEtaSupportGapPolynomialPhaseGram_finite_part_tendsto](RiemannGaussian/Hybrid/EtaPolynomialHeatMatrix.lean), [pairedEtaSignedPolynomialPhaseGram_tendsto](RiemannGaussian/Hybrid/EtaPolynomialHeatMatrix.lean), [pairedEtaSignedPolynomialPhaseGramError_sum_abs_eventually_le](RiemannGaussian/Hybrid/EtaPolynomialHeatMatrix.lean) |
| **Completed-current heat pairing audit** | Direct signed-heat insertion vanishes in both literal multiplicity branches. Two ordered continuous heat transitions have an exact, integrable gap-return pairing retaining the completion factors, both widths and phases, cutoff, and restored head coordinate. | [pairedEtaLeadingCurrentSignedHeatPairing_eq_zero](RiemannGaussian/EtaSignedHeatCurrentAudit.lean), [pairedEtaLeadingCurrentTwoTransitionPairing_eq_neg_gapReturn](RiemannGaussian/EtaCompletedGapReturnPairing.lean), [pairedEtaLeadingCurrentPolynomialReturn_audit](RiemannGaussian/EtaCompletedGapReturnPairing.lean) |
| **Full gap-return reconstruction** | The infinite gap-time integral is absolutely convergent at positive total tilt. Exact Gaussian and gap-mass normalization, followed by broad heat and vanishing tilt, reconstructs the original completed leading current at every fixed zero and cutoff. | [pairedEtaLeadingCurrentIntegratedGapReturn_eq_prod](RiemannGaussian/EtaIntegratedGapReturn.lean), [pairedEtaLeadingCurrent_gapReturn_reconstruction](RiemannGaussian/EtaLeadingCurrentReconstruction.lean) |
| **Quantitative current reconstruction** | The normalized return has an explicit error in the actual absolute kernel mass, physical cutoff, tilt, and inverse-square heat width. The full gap moment contributes at most `2/(M(1)a³)` for `0 < a ≤ 1`; the exact signed error integral remains available. | [normalized_current_gapReturn_sub_integral](RiemannGaussian/EtaCurrentReconstructionError.lean), [pairedEtaLeadingCurrentNormalizedGapReturn_error_le_smallTilt](RiemannGaussian/EtaCurrentReconstructionError.lean) |
| **Completed arithmetic kernel masses** | Both actual multiplicity carriers have an absolute kernel-mass bound `Cρ(1+log(2N+5))^(2m)/(N+1)`, with the two completion weights and horizontal coordinates explicit. It supplies the mass factor in the quantitative reconstruction error. | [pairedEtaLeadingCurrentAbsoluteKernelMass_le](RiemannGaussian/EtaCurrentKernelMass.lean), [pairedEtaLeadingCurrentNormalizedGapReturn_error_le_arithmetic](RiemannGaussian/EtaCurrentKernelMass.lean) |
| **Summable weighted current reconstruction** | One simultaneous heat/tilt schedule gives a summable odd-weighted error for the actual completed current. Its complex error series converges, and the finite first absolute moments of return and current differ by a single proved finite bound. | [summable_oddEndpoint_mul_norm_pairedEtaLeadingCurrentScheduledGapReturn_error](RiemannGaussian/EtaCurrentWeightedReconstruction.lean), [pairedEtaLeadingCurrentScheduledGapReturn_firstMoment_stability](RiemannGaussian/EtaCurrentWeightedReconstruction.lean) |
| **Actual continuous heat composition** | The completed gap return equals the explicitly composed broader Gaussian minus its support and nonpositive-time corrections. Full three-time convergence holds even at zero tilt; arbitrary ordered phases remain available before the common-phase composition is evaluated. | [integrable_leadingCurrent_fullTwoHeat_prod](RiemannGaussian/EtaCurrentFullHeatComparison.lean), [pairedEtaLeadingCurrentIntegratedGapReturn_eq_composed_sub_corrections](RiemannGaussian/EtaCurrentFullHeatComparison.lean) |
| **Zero-tilt weighted current reconstruction** | Arithmetic interval balance bounds the full Gaussian gap mass away from zero. Its exact midpoint multiplier reconstructs both original current branches with summable odd-weighted error at width `2(N+1)²`, retaining a finite first-moment stability budget. | [pairedEtaGaussianGapMass_zero_bounds](RiemannGaussian/EtaGaussianGapMass.lean), [pairedEtaLeadingCurrentZeroTiltScheduledReturn_firstMoment_stability](RiemannGaussian/EtaZeroTiltWeightedReconstruction.lean) |
| **Wallis colour and the actual current's first heat correction** | The cumulative literal colour approaches `log(π/2)` with error at most `9 exp(−t)`. This evaluates the broad-Gaussian gap term with a cubic-width remainder, then identifies the original signed current's physical midpoint coefficient with an explicit inverse-square-width error. | [pairedEtaLogColourPrimitive_wallis_error_le](RiemannGaussian/EtaLogColourPrimitive.lean), [pairedEtaGaussianGapMass_wallis_expansion_error_le](RiemannGaussian/EtaGaussianGapExpansion.lean), [pairedEtaLeadingCurrentZeroTiltGapReturn_midpoint_error_le_arithmetic](RiemannGaussian/EtaCurrentMidpointCorrection.lean) |
| **Midpoint arithmetic and zero-tail gain** | Both original midpoint coefficients evaluate in finite completed eta moments. The full complex orientation and exact reflection defect survive; the zero equation gives an extra endpoint decay factor in an explicit all-cutoff bound, including the translated simple-zero head. | [pairedEtaLeadingCurrentMidpointMoment_eq_adjacent_reflection](RiemannGaussian/EtaCurrentMidpointReflection.lean), [pairedEtaLeadingCurrentMidpointMoment_eq_head_reflection](RiemannGaussian/EtaCurrentMidpointReflection.lean), [abs_pairedEtaLeadingCurrentMidpointMoment_le_arithmetic](RiemannGaussian/EtaCurrentMidpointBounds.lean) |
| **Linear-width weighted reconstruction** | The actual midpoint gain makes the entire odd-weighted reconstruction error summable already at width `2(N+1)`. One explicit finite budget bounds every partial error sum and the difference of the original return and current's first absolute moments. | [pairedEtaLeadingCurrentLinearHeatReturn_weighted_error_le](RiemannGaussian/EtaCurrentLinearHeatSchedule.lean), [pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_stability](RiemannGaussian/EtaCurrentLinearHeatReconstruction.lean) |
| **Signed arithmetic endpoint estimate** | Both original current branches and the actual linear-width return have summable weighted error from explicit completed Euler endpoint expressions. The head evaluates exactly, and adjacent Euler products retain positive coefficients after their common Fourier phase cancels. | [pairedEtaHeadCompletedMoment_zero_eq_endpoints](RiemannGaussian/EtaCurrentEulerArithmetic.lean), [pairedEtaCurrentEulerAdjacentCoefficient_pos](RiemannGaussian/EtaCurrentEulerArithmetic.lean), [pairedEtaLeadingCurrentLinearHeatReturn_euler_error_sum_le](RiemannGaussian/EtaCurrentEulerEstimate.lean) |
| **Multiplicity-aware rank--trace inequalities** | The attributed Anthropic linear-algebra stack is specialised to actual finite eta zero windows, retaining analytic multiplicity and the signed off-line contribution. | [pairedEtaTopPrefixFiniteZeroWindow_multiplicityRankTrace_ledger](RiemannGaussian/EtaEnergyFiniteWindowMultiplicityRankTrace.lean#L78) |
| **Montgomery--Vaughan weighted Hilbert inequality** | An attributed Apache-2.0 formalisation with exact diagonal constant `13` and bilinear constant `26`. | [MontgomeryVaughan.mvDiag_thirteen](RiemannGaussian/MontgomeryVaughan/Final.lean#L28), [MontgomeryVaughan.mvHilbert_twentySix](RiemannGaussian/MontgomeryVaughan/Final.lean#L31) |

The RH equivalences in this inventory are reformulations. Their open
positivity or vanishing direction remains unproved.

## Accomplishments

- **Reproduced Anthropic's `2/3` certificate in Lean.**
  [externalZeta23_twoThirds_distinctCritical](RiemannGaussian/External/Zeta23Baseline.lean#L30)
  rechecks the unconditional statement that, for every `ε > 0` and all
  sufficiently large `T`, `(2/3 - ε) N(T,2T) ≤ N₀*(T,2T)`. Here `N` counts
  nontrivial zeta zeros with analytic multiplicity and `N₀*` counts distinct
  critical-line zeros in `T < Im rho ≤ 2T`. This reproduces external prior
  work from the pinned Apache-2.0 source; see its
  [provenance and compatibility notes](vendor/zeta23/UPSTREAM.md).
- **Rechecked the stronger Montgomery--Taylor simple-zero benchmark.**
  [externalZeta23_montgomeryTaylor_simpleCritical](RiemannGaussian/External/Zeta23Baseline.lean#L50)
  proves the corresponding bound with exact constant `HD(1)` and a numerator
  counting only simple critical-line zeros. The project also proves
  [externalZeta23_HD_one_gt_two_thirds](RiemannGaussian/External/Zeta23Benchmark.lean#L211),
  so the comparison with `2/3` is checked without a decimal approximation.
- **Formalised two strict improvements over that external benchmark.**
  [Zeta23InverseSampling.externalZeta23_montgomeryTaylor_uncapped_strictly_stronger](RiemannGaussian/External/Zeta23InverseSamplingEndgame.lean#L1779)
  constructs `HD(1) < C₀ < C₁` and proves
  `(Cᵢ - ε) N(T,2T) ≤ N₀ˢ(T,2T)` eventually for each constant, with all
  arithmetic and analytic premises discharged. These are exact existential
  constants obtained from a positive compact minimum; no numerical bound
  above `17/25` or `13/18` has been established. The three-point mechanism
  has [related prior work](https://github.com/ainta/zeta-simple-zeros/blob/main/docs/proof.md#3-the-3-point-certificate).
- **Developed auxiliary theorems for inverse sampling.**
  [montgomeryTaylorKernel_no_additive_zero_below_six_pi](RiemannGaussian/MontgomeryTaylorInverseSampling.lean#L458)
  proves that the kernel cannot vanish at both nonnegative gaps and their
  sum when the span is at most `6π`.
  [exists_montgomeryTaylorTripleEnergy_floor](RiemannGaussian/MontgomeryTaylorInverseSampling.lean#L538)
  supplies a uniform positive energy floor, and
  [Zeta23InverseSampling.ZeroBlockData.three_quarters_tripleOffDiagEnergy_le_sum_simpleDefect](RiemannGaussian/External/Zeta23InverseSamplingZeroSide.lean#L350)
  transports `3/4` of the off-diagonal energy into the spectral defect of a
  positive three-column Gram block with diagonal entries at most one. These
  checked auxiliary estimates feed the literal certificate above.
- **Proved geometric separation of literal eta features.**
  [exists_prime_eventually_linearIndependent_pairedEtaGeometricPackedHyperbolicFeature](RiemannGaussian/Hybrid/EtaGeometricPackedFeatureRank.lean#L210)
  shows that every finite zeta-zero window admits one odd prime sampling base
  for which all sufficiently late packed eta-feature blocks are linearly
  independent. This preserves the information needed to distinguish every
  represented zero, including its completion factors and multiplicity-aware
  features; it supplies no critical-line proportion by itself.
- **Combined literal eta arithmetic, polynomial phase, and Gaussian heat at second order.**
  [pairedEtaSupportGapGaussianLeakage_polynomial_finite_part_tendsto](RiemannGaussian/EtaPolynomialHeatFinitePart.lean)
  evaluates the actual heat finite part using separate harmonic and Wallis
  endpoint constants and a logarithmic Gaussian moment.
  [pairedEtaSignedPolynomialHeat_tendsto](RiemannGaussian/EtaPolynomialHeatReflection.lean)
  proves the signed endpoint law after exact logarithmic reflection.
  These are auxiliary analytic theorems; priority of the combined results
  has not been established.
- **Built a library of more than 10,000 audited project theorems.** The
  [generated inventory](docs/proof-status.json) covers more than 500 compiled
  project modules, with zero project-defined axioms, zero placeholder-dependent
  declarations, and no nonstandard theorem axioms.
- **Proved a uniform critical heat estimate on the literal eta support.**
  [pairedEtaMismatch_critical_error_le](RiemannGaussian/EtaLogSupportCritical.lean)
  bounds the displacement error by `5r` for `0 < r ≤ 1/8`.
  [pairedEtaSupportGapGaussianLeakage_uniform_error_le](RiemannGaussian/EtaSupportGapGaussian.lean#L349)
  carries this arithmetic information into the continuous Gaussian kernel
  with one error constant `32`, valid for every ordinate, including ordinates
  growing like `1/h`. The
  [exact spectral bridge](RiemannGaussian/EtaSupportGapGaussianSpectral.lean)
  also makes this a bound on the literal eta/gap spectral correlation.
  [Finite cutoff control](RiemannGaussian/EtaSupportGapGaussianCutoff.lean#L177)
  preserves that profile on the actual square `(0,log(1/h)]²`, and
  [the limit theorems](RiemannGaussian/EtaSupportGapGaussianLimit.lean)
  retain width-dependent ordinates and every mixed matrix entry.
  The [weighted boundary law](RiemannGaussian/EtaLogWeightedBoundary.lean)
  further retains arbitrary bounded Lipschitz complex tests, with an explicit
  error and a [logarithmic distribution limit](RiemannGaussian/EtaLogWeightedBoundaryLimit.lean).
  The [joint cubic-phase/moving-tilt heat theorem](RiemannGaussian/EtaCubicHeatLimit.lean)
  retains the complex displacement upstream, controls the signed phase
  remainder and omitted time interval, and proves the full Gaussian limit.
  This is new in the repository; wider mathematical priority has not been established.
- **Made actual eta phase-matrix positivity quantitative.**
  [pairedEtaSupportGapScaledPhaseGram_integer_coercive](RiemannGaussian/Hybrid/EtaSupportGapPhaseCoercivity.lean#L276)
  proves a lower bound for the entire continuous phase Gram, with the cost
  of `m` probes explicitly retained as `32m`. The complex integral and
  coefficient bounds preserve mixed phase interference. This auxiliary
  coercivity does not establish the sign of the completed reflected eta
  kernel that remains in the RH criterion.
  The nonlinear extension also proves [convergence of the full fixed mixed
  cubic-phase matrix](RiemannGaussian/Hybrid/EtaCubicHeatGram.lean), with an
  independent integral-of-squares proof of positivity for its limit.

The auxiliary contributions above have project-developed Lean proofs.
Priority or novelty relative to the wider mathematical literature has not
been established. The library also contains checked fourth-moment research,
but no `13/18` certificate or proof of RH is claimed.

## Mathematical Program

The current program combines four connected lines:

- The **finite certificate branch** adapts rank--trace and inertia methods to
  genuine symmetric eta zero windows. Its carrier retains cutoff, phase,
  multiplicity, reflected-zero colour, and coherent cross-zero interference,
  with separate positive and signed matrices joined by exact channel laws.
- The **eta arithmetic branch** realizes completed eta moments as explicit
  finite interval and endpoint sums, develops exact cutoff work laws, and uses
  geometric sampling to produce full-rank actual feature families and their
  multiplicity-weighted positive Gram companion, signed reflection normal
  form, and information-loss diagnosis for complete whitening.
- The **Gaussian/heat branch** supplies positive and signed heat flows,
  higher and mixed-scale moment Grams, projection leakage, closed paths, and
  the odd proper-time transform connecting heat kernels to the checked
  Montgomery--Vaughan inequality.
- The **Suzuki/contour branch** connects arithmetic screw-line quantities to
  the spectral xi logarithmic derivative and an RH-equivalent boundary-heat
  detector through rigorously controlled finite contours and limits.

The older finite Hardy, Blaschke, Pick-matrix, zero-counting, and
finite-to-entire developments remain checked supporting infrastructure and
alternative interfaces to the missing rigidity theorem. None of these
reformulations establishes the open arithmetic direction by itself.

## Repository Structure

- [RiemannGaussian.lean](RiemannGaussian.lean) is the root library module and
  fixes the complete import graph built by CI.
- [RiemannGaussian/](RiemannGaussian/) contains the Lean proof modules.
  Module families named `Gaussian*`, `Finite*`, `RiemannXi*`, and
  `Suzuki*` correspond to the principal parts of the program.
- [RiemannGaussian/HermitianRankTrace/](RiemannGaussian/HermitianRankTrace/)
  contains the attributed Apache-2.0 adaptation of the finite-dimensional
  rank--trace stack used by the eta specialization.
- [RiemannGaussian/MontgomeryVaughan/](RiemannGaussian/MontgomeryVaughan/)
  contains the attributed Apache-2.0 proof of the weighted Hilbert inequality
  and its explicit constants.
- [vendor/zeta23/](vendor/zeta23/) contains the pinned, warning-clean
  transitive source closure for the attributed external zero-proportion
  baselines, with upstream commit and compatibility changes recorded there.
- [scripts/GenerateProjectStatus.lean](scripts/GenerateProjectStatus.lean)
  audits the compiled environment and generates the status artifacts in
  [docs/](docs/).
- [scripts/LintProject.lean](scripts/LintProject.lean) runs all registered
  declaration linters over the complete project namespace.
- [AGENTS.md](AGENTS.md) records the proof discipline, workflow, and mandatory
  gates for research agents.
- [.github/workflows/lean_action_ci.yml](.github/workflows/lean_action_ci.yml)
  and [.githooks/pre-commit](.githooks/pre-commit) implement the remote and
  local verification gates.

## Rigor and Verification

The formal target is Mathlib's `RiemannHypothesis`. Every accepted proof
slice must preserve a continuous chain from imported Mathlib definitions to
the current frontier.

The enforced checks are:

- no Lean source may contain `sorry`, `admit`, or a direct use of Lean's
  unresolved-proof axiom;
- the entire library builds with warnings treated as errors;
- all registered project declaration linters pass;
- every compiled project declaration is audited for unresolved-proof
  dependencies, and project-defined axioms are rejected;
- displayed frontier theorems may depend only on Lean's standard
  `propext`, `Classical.choice`, and `Quot.sound` axioms;
- the generated SVG and JSON must exactly match the compiled environment; and
- GitHub Actions must pass on the exact pushed commit before another proof
  slice begins.

Numerical experiments, symbolic calculations, research notes, and literature
dispatches are used only to discover candidate mathematics. Nothing from them
is trusted until it has been re-derived in Lean and passed every gate.

## Build and Check

The project is pinned to Lean 4.33.1 and Mathlib 4.33.1. With
[elan](https://github.com/leanprover/elan) installed, run from the repository
root:

```bash
lake exe cache get
lake build --wfail
lake env lean -DwarningAsError=true scripts/LintProject.lean
lake env lean -DwarningAsError=true scripts/GenerateProjectStatus.lean
git diff --exit-code -- docs/proof-status.json docs/proof-status.svg
```

Enable the tracked pre-commit gate once per clone:

```bash
git config core.hooksPath .githooks
```

The hook repeats the source-placeholder scan, warning-as-error build,
whole-project lint, compiled-environment audit, dashboard freshness check, and
staged whitespace check. GitHub Actions remains authoritative because local
hooks can be bypassed.

## Research Method

Work proceeds in small theorem slices. Each slice isolates a real obstruction,
proves a reusable Lean lemma without weakening definitions or moving the
obstruction into assumptions, audits its axioms, runs all local gates, and is
then committed and pushed. Work resumes only after CI succeeds on that exact
commit.

Every representation is treated as an information-flow decision. Rich source
objects are retained while norms, traces, asymptotic limits, and triangle
bounds are exposed only as downstream views; phase, sign, orientation,
multiplicity, scale, and channel colour are collapsed only when a proved
estimate gains leverage from doing so.

Lean is also used as a research engine for deriving and testing new
mathematics across analysis, operator theory, spectral theory, number theory,
and mathematical physics. Numerical or symbolic experiments may suggest a
lemma, but only a kernel-checked theorem grounded in the existing chain counts
as progress. See [AGENTS.md](AGENTS.md) for the full methodology.

## License

Copyright 2026 David Sanftenberg.

RiemannGaussian is licensed under the [Apache License, Version 2.0](LICENSE)
(`Apache-2.0`). Third-party source retains its original copyright and
attribution notices; see the notices for
[Zeta23](vendor/zeta23/NOTICE),
[HermitianRankTrace](RiemannGaussian/HermitianRankTrace/NOTICE), and
[MontgomeryVaughan](RiemannGaussian/MontgomeryVaughan/NOTICE).
