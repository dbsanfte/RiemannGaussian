import RiemannGaussian.EtaZeroTiltCurrentReconstruction

/-!
# Summable weighted reconstruction with zero tilt and quadratic heat width

The width `2(N+1)²` is independent of the zero. Gaussian mass normalization
on the actual full gap produces a summable odd-weighted error on the
original completed current, without any exponential tilt amplification.
The first absolute moment of the current itself remains the open target.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The zero-tilt reconstruction uses only quadratic broadening in cutoff. -/
def pairedEtaCurrentZeroTiltWidth (N : ℕ) : ℝ := 2 * (N + 1 : ℝ) ^ 2

/-- The original full gap return with the zero-tilt quadratic-width schedule. -/
def pairedEtaLeadingCurrentZeroTiltScheduledReturn (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  pairedEtaLeadingCurrentZeroTiltGapReturn rho N (pairedEtaCurrentZeroTiltWidth N)

/-- Every scheduled width lies in the range of the uniform gap normalization. -/
theorem pairedEtaCurrentZeroTiltWidth_ge_two (N : ℕ) : 2 ≤ pairedEtaCurrentZeroTiltWidth N := by
  have hx : (1 : ℝ) ≤ N + 1 := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  unfold pairedEtaCurrentZeroTiltWidth
  nlinarith

/-- The completed arithmetic mass bound turns the zero-tilt reconstruction
error into an explicit logarithmic-over-cubic estimate. -/
theorem pairedEtaLeadingCurrentZeroTiltScheduledReturn_error_le
    (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaLeadingCurrentZeroTiltScheduledReturn rho N -
      (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ)‖ ≤
      (13 / 2) * pairedEtaLeadingCurrentMassConstant rho *
        (1 + pairedEtaLogTailCutoff (N + 2)) ^ (2 * analyticZetaZeroMultiplicity rho + 2) /
          (N + 1 : ℝ) ^ 3 := by
  have hL := pairedEtaLogTailCutoff_nonneg (N + 2)
  have hw := pairedEtaCurrentZeroTiltWidth_ge_two N
  calc
    _ ≤ pairedEtaLeadingCurrentAbsoluteKernelMass rho N *
        (13 * (1 + pairedEtaLogTailCutoff (N + 2)) ^ 2 / pairedEtaCurrentZeroTiltWidth N) :=
      pairedEtaLeadingCurrentZeroTiltGapReturn_error_le rho N hw
    _ ≤ (pairedEtaLeadingCurrentMassConstant rho *
        (1 + pairedEtaLogTailCutoff (N + 2)) ^ (2 * analyticZetaZeroMultiplicity rho) / (N + 1 : ℝ)) *
        (13 * (1 + pairedEtaLogTailCutoff (N + 2)) ^ 2 / pairedEtaCurrentZeroTiltWidth N) :=
      mul_le_mul_of_nonneg_right (pairedEtaLeadingCurrentAbsoluteKernelMass_le rho N) (by positivity)
    _ = _ := by
      unfold pairedEtaCurrentZeroTiltWidth
      rw [pow_add]
      field_simp

/-- The odd arithmetic weight leaves a summable logarithmic-over-square
majorant, with its completion-dependent coefficient explicit. -/
theorem pairedEtaLeadingCurrentZeroTiltScheduledReturn_weighted_error_le
    (rho : NontrivialZetaZero) (N : ℕ) :
    (2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentZeroTiltScheduledReturn rho N -
      (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ)‖ ≤
      13 * pairedEtaLeadingCurrentMassConstant rho *
        (1 + pairedEtaLogTailCutoff (N + 2)) ^ (2 * analyticZetaZeroMultiplicity rho + 2) /
          (N + 1 : ℝ) ^ 2 := by
  have hC := pairedEtaLeadingCurrentMassConstant_nonneg rho
  have hL := pairedEtaLogTailCutoff_nonneg (N + 2)
  calc
    _ ≤ (2 * N + 1 : ℝ) * ((13 / 2) * pairedEtaLeadingCurrentMassConstant rho *
        (1 + pairedEtaLogTailCutoff (N + 2)) ^ (2 * analyticZetaZeroMultiplicity rho + 2) /
          (N + 1 : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_left (pairedEtaLeadingCurrentZeroTiltScheduledReturn_error_le rho N) (by positivity)
    _ ≤ (2 * (N + 1) : ℝ) * ((13 / 2) * pairedEtaLeadingCurrentMassConstant rho *
        (1 + pairedEtaLogTailCutoff (N + 2)) ^ (2 * analyticZetaZeroMultiplicity rho + 2) /
          (N + 1 : ℝ) ^ 3) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by field_simp

/-- The actual zero-tilt schedule has summable weighted norm error relative
to the unchanged leading current for every nontrivial zeta zero. -/
theorem summable_oddEndpoint_mul_norm_pairedEtaLeadingCurrentZeroTiltScheduledReturn_error
    (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦ (2 * N + 1 : ℝ) *
      ‖pairedEtaLeadingCurrentZeroTiltScheduledReturn rho N -
        (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ)‖) := by
  have hs := (summable_pairedEtaCurrent_logPower_div_sq
    (2 * analyticZetaZeroMultiplicity rho + 2)).mul_left (13 * pairedEtaLeadingCurrentMassConstant rho)
  apply hs.of_nonneg_of_le (fun N ↦ by positivity)
  intro N
  simpa only [mul_div_assoc] using pairedEtaLeadingCurrentZeroTiltScheduledReturn_weighted_error_le rho N

/-- The signed complex weighted error series is also summable. -/
theorem summable_oddEndpoint_smul_pairedEtaLeadingCurrentZeroTiltScheduledReturn_error
    (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦ (2 * N + 1 : ℝ) •
      (pairedEtaLeadingCurrentZeroTiltScheduledReturn rho N -
        (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ))) := by
  apply (summable_oddEndpoint_mul_norm_pairedEtaLeadingCurrentZeroTiltScheduledReturn_error rho).of_norm_bounded
  intro N
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * N + 1), le_refl]

/-- An explicit finite budget for every partial sum of weighted reconstruction errors. -/
def pairedEtaCurrentZeroTiltWeightedErrorBound (rho : NontrivialZetaZero) : ℝ :=
  13 * pairedEtaLeadingCurrentMassConstant rho *
    ∑' N : ℕ, (1 + pairedEtaLogTailCutoff (N + 2)) ^
      (2 * analyticZetaZeroMultiplicity rho + 2) / (N + 1 : ℝ) ^ 2

/-- Every finite weighted reconstruction error stays below the same budget. -/
theorem pairedEtaLeadingCurrentZeroTiltScheduledReturn_weighted_error_sum_le
    (rho : NontrivialZetaZero) (K : ℕ) :
    (∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) *
      ‖pairedEtaLeadingCurrentZeroTiltScheduledReturn rho N -
        (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ)‖) ≤
      pairedEtaCurrentZeroTiltWeightedErrorBound rho := by
  have hC := pairedEtaLeadingCurrentMassConstant_nonneg rho
  have hs := (summable_pairedEtaCurrent_logPower_div_sq
    (2 * analyticZetaZeroMultiplicity rho + 2)).mul_left (13 * pairedEtaLeadingCurrentMassConstant rho)
  calc
    _ ≤ ∑ N ∈ Finset.range K, 13 * pairedEtaLeadingCurrentMassConstant rho *
        ((1 + pairedEtaLogTailCutoff (N + 2)) ^
          (2 * analyticZetaZeroMultiplicity rho + 2) / (N + 1 : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro N _
      simpa only [mul_div_assoc] using pairedEtaLeadingCurrentZeroTiltScheduledReturn_weighted_error_le rho N
    _ ≤ ∑' N : ℕ, 13 * pairedEtaLeadingCurrentMassConstant rho *
        ((1 + pairedEtaLogTailCutoff (N + 2)) ^
          (2 * analyticZetaZeroMultiplicity rho + 2) / (N + 1 : ℝ) ^ 2) := by
      apply hs.sum_le_tsum
      intro N _
      have hL := pairedEtaLogTailCutoff_nonneg (N + 2)
      positivity
    _ = _ := by rw [tsum_mul_left]; rfl

/-- The actual zero-tilt return preserves the finite first absolute-moment
frontier up to a uniform finite error. Neither moment is bounded here. -/
theorem pairedEtaLeadingCurrentZeroTiltScheduledReturn_firstMoment_stability
    (rho : NontrivialZetaZero) (K : ℕ) :
    |(∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentZeroTiltScheduledReturn rho N‖) -
      (∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N|)| ≤
      pairedEtaCurrentZeroTiltWeightedErrorBound rho := by
  calc
    _ = |∑ N ∈ Finset.range K, ((2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentZeroTiltScheduledReturn rho N‖ -
        (2 * N + 1 : ℝ) * |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N|)| := by
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ N ∈ Finset.range K, |(2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentZeroTiltScheduledReturn rho N‖ -
        (2 * N + 1 : ℝ) * (|pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N|)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) *
        ‖pairedEtaLeadingCurrentZeroTiltScheduledReturn rho N -
          (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ)‖ := by
      apply Finset.sum_le_sum
      intro N _
      have hw : (0 : ℝ) ≤ 2 * N + 1 := by positivity
      rw [← mul_sub, abs_mul, abs_of_nonneg hw]
      apply mul_le_mul_of_nonneg_left _ hw
      simpa only [Complex.norm_real, Real.norm_eq_abs] using
        abs_norm_sub_norm_le (pairedEtaLeadingCurrentZeroTiltScheduledReturn rho N)
          (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ)
    _ ≤ _ := pairedEtaLeadingCurrentZeroTiltScheduledReturn_weighted_error_sum_le rho K

end

end RiemannGaussian
