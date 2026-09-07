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

Prove the uniform weighted arithmetic bound through the completed Möbius source. The A^(2/3) low-divisor range and single clipped boundary are controlled. The exact parity recurrence now couples complete quotient shells at the original and halved physical cutoffs, preserving all cross terms. Target a fixed gap below the source square through their joint energy and phase-weighted correlation; a power rate is optional. This bound and RH remain unproved.

## Latest Update

Lean now lifts the existing **Möbius parity recurrence into every complete
quotient block and dyadic shell**. The
[exact shell recurrence](RiemannGaussian/EtaMoebiusQuotientParityRecurrence.lean)
is `Z_j(M)=O_j(M)-2^(-rho) O_j(floor(M/2))`, with the original quotient
cap retained on both terms. The
[full parity matrix](RiemannGaussian/EtaMoebiusQuotientParityMatrix.lean)
then gives the checked energy identity

\[
 H_k=E_{0,k}+2^{-2\Re\rho}E_{1,k}
       -2\Re\!\left(\overline{2^{-\rho}}\,B_k\right).
\]

Each `E` is the energy of a whole odd shell channel, including all
within-channel shell cross terms. `B_k` is the complete complex
correlation between the original and halved scales. The matrix is
Hermitian and its diagonal entries are nonnegative. The mixed term's
phase is retained throughout.

**A joint arithmetic bound with a fixed positive gap below the source
square remains unproved.** The small dyadic multiplier alone does not
supply it. The [assessment](docs/eta-hyperbola-endgame-assessment.md)
records the source-preserving recurrence and the remaining signed
correlation target. No sharper zero strip, full arithmetic decay,
uniform weighted current bound, or RH proof is established.

## Notable Formalisations

Selected entry points into the Lean library are listed below. Each link names
a compiled theorem; its source records the precise domains and hypotheses.

| Area | What is formalised | Lean entry points |
| --- | --- | --- |
| **Gaussian/Weil explicit formula** | The arithmetic Gaussian expression, including prime-power and Archimedean terms, equals the canonical multiplicity-weighted symmetric zeta-zero sum for every positive width. | [gaussianArithmeticExplicitFormula_eq_canonical](RiemannGaussian/GaussianXiLogDerivativeGrowth.lean#L1235) |
| **Gaussian Möbius arithmetic and cancellation** | The full reciprocal integral equals the actual Möbius sum, with every contour correction controlled. Its unit-time cancellation transfers through an exact complex heat identity: for each fixed complex `s`, `exp((s−1)a) W_s,2(a) → 0` with full phase retained, hence `W_s,2(log X)=o(X^(1−Re(s)))`. Absolute convergence holds for every positive heat time. | [gaussianMoebiusSum_one_le_reciprocal_log_gain_eventually](RiemannGaussian/GaussianMoebiusCancellation.lean), [summable_complexGaussianMoebiusSummand](RiemannGaussian/ComplexGaussianMoebius.lean), [integral_normalizedGaussianMoebius_heat](RiemannGaussian/GaussianMoebiusPhaseHeat.lean), [complexGaussianMoebiusSum_two_normalized_tendsto_zero](RiemannGaussian/GaussianMoebiusComplexCancellation.lean) |
| **Quantitative finite Möbius cancellation and completed quotient blocks** | The unsmoothed sum has exponential decay in the cubic logarithmic scale `A(h)=10^15 h^3`, with all contour and cutoff errors included. Complex prefixes and literal quotient blocks inherit a quantitative rate above a specified weight-dependent cutoff. A common scale threshold works for all weights, with explicit weight dependence in the constants. The original completed zeroth eta blocks retain their completion and odd endpoint decay. | [abs_moebiusLogPrefix_cubic_le_eventually](RiemannGaussian/MoebiusFiniteQuantitativeCancellation.lean), [exists_complexMoebiusFinitePrefix_cubic_rate](RiemannGaussian/MoebiusFiniteMellinRate.lean), [exists_pairedEtaCompletedMoebius_divided_block_cubic_rate](RiemannGaussian/EtaMoebiusDividedBlockRate.lean) |
| **Harmonic Möbius cancellation in actual inverse regions** | The ordered harmonic prefix tends to zero with a quantitative cubic-scale rate. Across the complete inner-truncated physical hyperbola, the accumulated signed product coefficient is exactly `M H_mu(D)` minus a signed floor remainder of size at most `D`. The original completed complex carrier remains available; its quadratic bound is still open. | [moebiusHarmonicPrefix_tendsto_zero](RiemannGaussian/MoebiusHarmonicCancellation.lean), [sum_pairedEtaInverseInnerCapCoefficient_harmonic](RiemannGaussian/EtaInverseHarmonicCoefficients.lean), [exists_pairedEtaInverseInnerCapCoefficient_cubic_rate](RiemannGaussian/EtaInverseHarmonicCoefficients.lean) |
| **Gaussian heat and reflected-zero Grams** | The complete matched Gaussian correlation equals the boundary heat-residue sum. At positive heat time, its vanishing is equivalent to RH. | [riemannXiUpperReflectedPairGaussianTotal_eq_boundaryHeatResidueTotal](RiemannGaussian/RiemannXiBoundaryGaussianGram.lean#L187), [riemannXiUpperReflectedPairGaussianTotal_eq_zero_iff_rh](RiemannGaussian/RiemannXiBoundaryGaussianGram.lean#L197) |
| **Suzuki arithmetic and spectral formulas** | Suzuki's positive-time arithmetic function equals its spectral expansion on `Im z > 1/2`. The literal arithmetic `Psi` is strictly positive on a nonzero punctured neighbourhood of the origin. | [riemannXiSuzukiArithmeticPPositive_eq_spectral_safe](RiemannGaussian/RiemannXiSuzukiWeilVerticalLimit.lean#L462), [exists_pos_on_abs_riemannXiSuzukiPsi](RiemannGaussian/RiemannXiSuzukiPointwiseLocalPositivity.lean#L298) |
| **Xi growth and divisor summability** | Unconditional `exp(O(R log R))` xi growth and convergence of the multiplicity-weighted inverse-square zero series. | [riemannXi_logLinearGrowth](RiemannGaussian/GaussianXiLogLinearGrowth.lean#L315), [summable_distinct_zetaZeroInverseSquareNorm](RiemannGaussian/GaussianXiInverseSquareSummability.lean#L294) |
| **Finite eta phase bounds on zero coordinates and current powers** | An exact continuous exponential projection and a finite paired eta prefix with complete tail error give `delta_N ≤ Re(rho) ≤ 1−delta_N`. The resulting exponent bounds both original current branches, the Gaussian return, and the full inverse energy at every cutoff. Its proved `1/11` floor limits this particular upper-bound formula. | [norm_pairedEtaPhaseBoundaryValue_le_zero_ratio](RiemannGaussian/EtaPhaseProjectionBound.lean), [nontrivialZetaZero_mem_etaFinitePhase_strip](RiemannGaussian/EtaFinitePhaseMargin.lean), [pairedEtaCurrentFullInverseEnergy_firstMoment_le_finitePhase](RiemannGaussian/EtaCurrentFinitePhasePower.lean) |
| **Finite eta translate Grams and complete current-power budgets** | Nonnegative real translates annihilate every actual eta zero. A compact target sharing the elementary eta factor remains nonzero at actual zeta zeros. Its full residual is bounded by an exact finite overlap Gram plus the complete coefficient-dependent tail; reflection transports this to both current branches, the Gaussian return, and the full inverse energy. A coefficient family making the budget vanish remains open. | [pairedEtaProjectionHeadTransform_ne_zero](RiemannGaussian/EtaProjectionHeadTarget.lean), [pairedEtaTranslatedResidualEnergyCutoff_eq_finiteForm](RiemannGaussian/EtaTranslatedFiniteResidual.lean), [pairedEtaCurrentFullInverseEnergy_firstMoment_le_translatedProjection](RiemannGaussian/EtaCurrentTranslatedProjectionPower.lean) |
| **Exact eta coefficient laws and a complete four-translate bound** | A regularized inverse of the actual Gram defines a growing dyadic coefficient family. Its exact minimizing identity bounds the complete residual and original current; its four-point deficit is below `1/4`. Four explicit rational coefficients separately give full residual energy below `1/5`. Decay of the family deficit remains open. | [pairedEtaCanonicalTranslateBudget_le_trial](RiemannGaussian/EtaCanonicalTranslateBound.lean), [pairedEtaDyadicTranslateDeficit_two_lt_one_quarter](RiemannGaussian/EtaCanonicalTranslateFamily.lean), [pairedEtaFourProjection_residualEnergy_lt_one_fifth](RiemannGaussian/EtaFourTranslateBound.lean), [pairedEtaLeadingCurrent_firstMoment_le_dyadicTranslate](RiemannGaussian/EtaCanonicalTranslateFamily.lean) |
| **Exact Möbius candidates with vanishing coefficient cost and infinite tail** | Balanced logarithmic Möbius coefficients have zero signed total mass and absolute sum at most `2(k+1)`. Their full regularization penalty is at most `(k+1)^2/2^k` and tends to zero, as does the actual entire omitted residual integral. The canonical deficit is bounded by the growing finite residual plus this vanishing allowance; decay of that finite residual remains open. | [pairedEtaMoebiusTrialPrimitive_eq_harmonic_difference](RiemannGaussian/EtaMoebiusTrialCoefficients.lean), [pairedEtaDyadicMoebiusTrialPenalty_tendsto_zero](RiemannGaussian/EtaMoebiusTrialPenalty.lean), [pairedEtaDyadicMoebiusTrialResidualTail_tendsto_zero](RiemannGaussian/EtaMoebiusTrialResidual.lean), [pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_moebius_cutoff_add_allowance](RiemannGaussian/EtaMoebiusTrialResidual.lean) |
| **Full Möbius grid-refinement and residual stability** | Exact signed block sums identify every coarse and fine candidate. With the arithmetic weights fixed at each stage, arbitrary integer refinement changes both the full critical square approximation and the complete target residual energy by proved vanishing amounts. The canonical deficit is bounded by any refined arithmetic residual plus an explicit allowance tending to zero. Decay of the arithmetic residual remains open. | [pairedEtaTranslateDifferenceEnergy_zero_eq](RiemannGaussian/EtaTranslateDifference.lean), [pairedEtaMoebiusTrialRefinementError_le](RiemannGaussian/EtaMoebiusTrialRefinement.lean), [pairedEtaDyadicMoebiusResidual_sub_refined_tendsto_zero](RiemannGaussian/EtaMoebiusRefinedBudget.lean), [pairedEtaDyadicTranslateDeficit_le_refined_moebius](RiemannGaussian/EtaMoebiusRefinedBudget.lean) |
| **Full critical-square transport to signed continuum arithmetic** | Every actual grid converges to an explicit locally finite odd/even primitive formula with the exact endpoint convention. Its entire critical square error is at most `32M²√(2M/d)` under the stated grid conditions. Every refined residual and the identified continuum residual differ by a proved vanishing amount along the original stages. Decay of that arithmetic residual remains open. | [pairedEtaMoebiusTrialGridCombination_tendsto_continuum](RiemannGaussian/EtaMoebiusContinuumCombination.lean), [pairedEtaMoebiusContinuumGridError_le](RiemannGaussian/EtaMoebiusContinuumEnergy.lean), [pairedEtaDyadicMoebiusRefinedResidual_sub_continuum_tendsto_zero](RiemannGaussian/EtaMoebiusContinuumBudget.lean) |
| **Complete divisor square sum and decay of both arithmetic ends** | The full continuum energy equals a genuinely summable sequence of squared signed divisor residuals. Its interior retains the exact prime variance and normalization cost. The original normalization is at most `5/log M` in absolute value, giving a joint prefix bound `484R/log² M` for `R≤M`. The complete head through `floor(log M)` and tail past `M²` both decay. The intervening band remains uncontrolled and enters the original zero comparison unchanged. | [hasSum_pairedEtaMoebiusArithmeticCellResidual_sq](RiemannGaussian/EtaMoebiusArithmeticEnergy.lean), [pairedEtaMoebiusContinuumResidualEnergy_eq_primeVariance_add_exterior](RiemannGaussian/EtaMoebiusPrimeVariance.lean), [pairedEtaMoebiusArithmeticSquarePrefix_le_log_bound](RiemannGaussian/EtaMoebiusArithmeticGrowingHead.lean), [pairedEtaMoebiusArithmeticSquareTail_quadratic_tendsto_zero](RiemannGaussian/EtaMoebiusArithmeticSamplingTail.lean), [pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_moebius_middle](RiemannGaussian/EtaMoebiusMiddleBudget.lean) |
| **Exact Hardy transform and balanced floor-cell norm comparison** | The full arithmetic Hardy transform preserves the original reciprocal-cell-weighted norm, including the vanishing endpoint term. The actual eta residual is its signed dyadic difference. Its full energy lies between `1/6` and `6` times the balanced floor-cell energy for all original bounded weights. Decay of either full norm remains unproved. | [tsum_etaDiscreteHardyTransform_sq_eq](RiemannGaussian/EtaDiscreteHardyTransform.lean), [pairedEtaMoebiusArithmeticCellResidual_eq_hardy_dyadic](RiemannGaussian/EtaMoebiusBeurlingComparison.lean), [pairedEtaMoebiusContinuumResidualEnergy_beurling_bounds](RiemannGaussian/EtaMoebiusBeurlingComparison.lean) |
| **Exact Möbius normalization main term and uniform prime discrepancy** | The entire signed Euler quotient correction tends to zero, giving `p_M log M→1` for the original coefficients. Every interior cell has the exact rescaled residual `Δ(L)+e_M H_eta(L)`, uniformly within `2|e_M|` of its prime discrepancy. The complete signed cross moment and the growing normalization square cost remain explicit; full residual decay is open. | [pairedEtaMoebiusLogEulerCorrection_tendsto_zero](RiemannGaussian/EtaMoebiusLogEulerCancellation.lean), [pairedEtaMoebiusLogHarmonic_mul_log_tendsto_one](RiemannGaussian/EtaMoebiusNormalizationMainTerm.lean), [pairedEtaMoebiusArithmeticSquarePrefix_mul_log_sq_eq_discrepancy](RiemannGaussian/EtaMoebiusNormalizationMainTerm.lean) |
| **Completed Möbius hyperbola, boundary decay, and exact quotient shells** | The original divisor aggregate through `A^(2/3)` has vanishing mean square at a hypothetical right-half zero. The single clipped fibre also has vanishing mean square, leaving complete quotient blocks grouped into exact dyadic shells with all cross terms retained. Their nonzero source limit is checked; an independent upper bound with a fixed gap below the source remains open. | [pairedEtaCompletedMoebiusOriginalMeanSquare_twoThirds_tendsto_zero](RiemannGaussian/EtaMoebiusTwoThirdsMeanSquare.lean), [norm_pairedEtaCompletedMoebiusBoundaryFibre_twoThirds_le](RiemannGaussian/EtaMoebiusBoundaryFibre.lean), [pairedEtaCompletedMoebiusBoundaryMeanSquare_twoThirds_tendsto_zero](RiemannGaussian/EtaMoebiusBoundaryFibreDecay.lean), [pairedEtaCompletedMoebiusCompleteQuotientMeanSquare_twoThirds_eq_shellCorrelations](RiemannGaussian/EtaMoebiusQuotientShells.lean) |
| **Parity coupling of complete quotient shells** | The literal even-divisor contribution is an exact multiple of the odd contribution at half the physical cutoff, with the original quotient cap held fixed. The full shell energy factors through a Hermitian two-scale matrix, retaining every shell pair and the phase-weighted mixed correlation. Its arithmetic upper bound remains open. | [pairedEtaCompletedMoebiusQuotientShell_eq_odd_sub_half](RiemannGaussian/EtaMoebiusQuotientParityRecurrence.lean), [pairedEtaCompletedMoebiusCompleteQuotientMeanSquare_twoThirds_eq_parityEnergy](RiemannGaussian/EtaMoebiusQuotientParityMatrix.lean) |
| **Actual exterior parity energy and signed covariance** | Exact period-two waves represent the original full grid exterior. Discrete summation by parts has zero boundary terms, and the resulting short-window covariance retains every signed primitive cross term. The entire far part costs at most `M²/(2d)`. The original zero comparison transfers to the remaining near energy with a vanishing allowance; its decay remains open. | [integral_pairedEtaMoebiusGrid_exterior_eq_parity](RiemannGaussian/EtaMoebiusExteriorParityEnergy.lean), [pairedEtaMoebiusGridParitySum_eq_primitive_differences](RiemannGaussian/EtaMoebiusExteriorParity.lean), [integral_pairedEtaMoebiusGridParitySum_sq_eq_covariance](RiemannGaussian/EtaMoebiusParityCovariance.lean), [pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_moebius_nearParity](RiemannGaussian/EtaMoebiusParityBudget.lean) |
| **Exact exterior Möbius arithmetic and partial residual decay** | The harmonic correction and actual target-interval residual tend to zero. The entire exterior energy is exactly the square integral of a signed odd/even primitive formula plus its full infinite tail, bounded by `(k+1)^2/4^k` for every refinement schedule. Decay of the growing arithmetic square integral remains open. | [pairedEtaDyadicMoebiusRefinedHeadResidual_tendsto_zero](RiemannGaussian/EtaMoebiusRefinedHeadDecay.lean), [pairedEtaMoebiusTrialGridCombination_eq_arithmeticPrefix](RiemannGaussian/EtaMoebiusGridArithmetic.lean), [pairedEtaDyadicMoebiusRefinedExteriorEnergy_eq_arithmetic_add_tail](RiemannGaussian/EtaMoebiusExteriorBudget.lean) |
| **Explicit zero-free strip from signed prime positivity** | The exact pole geometry and complete signed local zero sum give a multiplicity-sensitive margin more than 31 times the preceding signed margin. Every actual zero of absolute ordinate at least one stays at least `1/(56458 log(abs(gamma)+22))` from either edge. | [multiplicity_le_quadratic_signed_zero_gap](RiemannGaussian/ZetaSignedExactPole.lean), [nontrivialZetaZero_mem_signedQuadratic_strip](RiemannGaussian/ZetaSignedQuadraticMargin.lean), [nontrivialZetaZero_mem_quadratic_reciprocal_log_strip](RiemannGaussian/ZetaSignedQuadraticComparison.lean) |
| **Simultaneous edge-window simplicity and separation** | At absolute center height at least one, a rectangle of width and ordinate half-width `1/(6000 log(abs(y)+22))` adjoining either strip edge has total analytic multiplicity at most one. The common complex pole sum and its full complement remain available. | [sum_multiplicity_le_one_in_signedEdgeWindow](RiemannGaussian/ZetaSignedWindowMultiplicity.lean), [sum_multiplicity_le_one_in_signedLeftEdgeWindow](RiemannGaussian/ZetaSignedZeroSeparation.lean), [signedEdgeWindowWidth_lt_im_sub_of_ne](RiemannGaussian/ZetaSignedZeroSeparation.lean) |
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
| **Sublinear weighted return bound** | The actual return's first absolute moment is at most `C_rho (K+1)^|2 Re(rho)-1|`. Both multiplicity branches and their completion constants are retained, with exact critical-line cancellation handled separately; dividing the moment by `K+1` gives a limit of zero. | [pairedEtaLeadingCurrent_weighted_le_doubleDecay](RiemannGaussian/EtaCurrentArithmeticEnvelope.lean), [pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_growth_le](RiemannGaussian/EtaCurrentReturnGrowth.lean), [pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_div_cutoff_tendsto_zero](RiemannGaussian/EtaCurrentReturnGrowth.lean) |
| **Explicit eta and prime-product zero margins** | Height-adapted eta prefixes and classical prime positivity give every actual zero a positive edge margin, bounded below by an explicit reciprocal fourteenth logarithmic power above height twenty-one. This strictly improves the previous ordinate-only bound. Taking the maximum with the higher-order Schwarz margin retains analytic multiplicity and lowers the unchanged return's still-positive exponent. | [norm_riemannZeta₁_le_etaThinStrip](RiemannGaussian/EtaThinStripRectangle.lean), [nontrivialZetaZero_mem_reciprocal_logarithmic_strip](RiemannGaussian/EtaLogarithmicMarginComparison.lean), [nontrivialZetaZero_mem_etaRefinedPrimeProduct_strip](RiemannGaussian/EtaLogarithmicZeroMargin.lean) |
| **Positive principal endpoints for both multiplicities** | The actual current and return have summable weighted error from one signed difference of complementary endpoint decays, with both completion coefficients strictly positive. The simple head's complex phase correction is explicit; one finite budget controls every difference of first absolute moments. | [pairedEtaCurrentPrincipalCoefficient_pos](RiemannGaussian/EtaCurrentPrincipalEndpoints.lean), [pairedEtaCurrentHalfStepHead_mul_conj_euler](RiemannGaussian/EtaCurrentHalfStepPairs.lean), [pairedEtaLeadingCurrentLinearHeatReturn_principal_firstMoment_stability](RiemannGaussian/EtaCurrentPrincipalEndpoints.lean) |
| **Sharp growth at a hypothetical off-critical zero** | Assuming an actual zero is off the critical line, its slower positive completion channel gives matching eventual displacement-power bounds for the original return's weighted first absolute moment. An explicit finite offset gives an all-cutoff lower bound, and the moment tends to infinity. This does not exclude such a zero. | [pairedEtaCurrentPrincipalEndpoint_eq_dominant_factor](RiemannGaussian/EtaCurrentPrincipalDominance.lean), [pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_lower_with_offset](RiemannGaussian/EtaCurrentReturnSharpGrowth.lean), [pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_power_bounds_eventually](RiemannGaussian/EtaCurrentReturnSharpGrowth.lean) |
| **Finite Möbius constraints and eta phase cancellation** | Fixed odd/even divisor pairs have period cancellation, and zeroth-order parity aggregates have uniform bounds. Every centered moment now has full Möbius inversion with exact center translations and a fixed-center aggregate bound. Both original current branches reconstruct, including the adjacent-order double sum for repeated zeros. The weighted bound remains open. | [norm_pairedEtaSignedCompletedMoebiusDyadicCorrelation_le](RiemannGaussian/EtaMoebiusDyadicCorrelation.lean), [pairedEtaLeadingCurrent_eq_oddInverse_head](RiemannGaussian/EtaCurrentMoebiusInverse.lean), [norm_pairedEtaCompletedOddInverseTop_sub_main_le](RiemannGaussian/EtaMoebiusGroupedInverse.lean), [norm_pairedEtaCompletedOddInverseBottom_add_main_le](RiemannGaussian/EtaMoebiusGroupedInverse.lean), [norm_pairedEtaCompletedMomentMoebiusAggregate_le](RiemannGaussian/EtaMomentMoebiusTransform.lean), [pairedEtaLeadingCurrent_eq_momentInverse_adjacent](RiemannGaussian/EtaCurrentMomentMoebiusInverse.lean) |
| **Divisor Fourier separation and physical mean square** | Literal quotient phases have proved finite Fourier support, exact gcd covariance, and separated divisor frequencies. Their original completed Möbius family has mean square at most `C_rho D(1+log D) A^(-2 Re rho)` when `D²` is at most both the starting cutoff and averaging length. The original signed pair retains both complementary physical decay rates. | [pairedEtaCompletedMoebiusParityFamily_eq_fourier](RiemannGaussian/EtaMoebiusFourierSpectrum.lean), [pairedEtaDivisorFourierSpectrum_separated](RiemannGaussian/EtaDivisorFourierGrid.lean), [pairedEtaCompletedMoebiusParityFamily_period_energy_eq](RiemannGaussian/EtaMoebiusParityEnergy.lean), [pairedEtaCompletedMoebiusOriginalMeanSquare_le_quadratic](RiemannGaussian/EtaMoebiusOriginalQuadraticFamily.lean), [pairedEtaSignedCompletedMoebiusOriginalMeanAbsolute_le_quadratic](RiemannGaussian/EtaMoebiusOriginalQuadraticFamily.lean) |
| **Moving-center moments and inverse-term reduction** | Every moment below the actual multiplicity reduces quantitatively to the original zeroth-order family with coefficient `k!/rho^k`. The square-root divisor-range mean square and signed adjacent-order bound hold at moving physical centers. An explicit companion error applies inside the original inverse terms; the full weighted inverse sum remains open. | [norm_pairedEtaCompletedMomentMoebiusTerm_physical_sub_zero_le](RiemannGaussian/EtaMomentPhysicalReduction.lean), [pairedEtaCompletedMomentOriginalMeanSquare_le_quadratic](RiemannGaussian/EtaMomentQuadraticMeanSquare.lean), [pairedEtaSignedCompletedMomentOriginalMeanAbsolute_adjacent_le_quadratic](RiemannGaussian/EtaMomentSignedQuadraticFamily.lean), [norm_pairedEtaCompletedMomentInversePartialTerm_sub_zero_le](RiemannGaussian/EtaMomentInverseReduction.lean) |
| **Joint control of original inverse rectangles** | Exact product grouping and a proved collision-energy estimate bound both actual inverse divisor sums together, with mean square at most `C_rho,k ED(1+log E)²(1+log(ED))² A^(-2 Re rho)` for `(ED)²≤A,L`. The original signed adjacent pair retains both physical decay rates. The complete inverse range remains open. | [sum_sq_pairedEtaInverseProductCoefficient_le_log_sq](RiemannGaussian/EtaInverseProductCoefficients.lean), [pairedEtaCompletedMomentInverseRectangleMeanSquare_le_quadratic](RiemannGaussian/EtaInverseRectangleMeanSquare.lean), [pairedEtaSignedCompletedMomentInverseRectangleMeanAbsolute_adjacent_le_quadratic](RiemannGaussian/EtaInverseRectangleSigned.lean) |
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
- **Formalised a concrete reciprocal-logarithm zero-free strip.**
  [nontrivialZetaZero_mem_signedQuadratic_strip](RiemannGaussian/ZetaSignedQuadraticMargin.lean)
  gives a multiplicity-sensitive margin at both edges for every actual nontrivial zero,
  combining the repository's eta bounds with classical signed prime
  positivity. [thirtyOne_mul_signedLogZeroMargin_lt_quadratic](RiemannGaussian/ZetaSignedQuadraticComparison.lean)
  proves a margin more than 31 times the previous signed project bound at every nonzero ordinate. This is a
  formalisation of a classical type of region, with no novelty claim.
- **Proved local simplicity and separation for actual zeros near either edge.**
  [sum_multiplicity_le_one_in_signedEdgeWindow](RiemannGaussian/ZetaSignedWindowMultiplicity.lean)
  and its [reflected counterpart](RiemannGaussian/ZetaSignedZeroSeparation.lean)
  bound the full multiplicity in an explicit rectangle by one. This
  constrains several zeros together and proves simplicity from location;
  it does not establish global simplicity or RH.
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
