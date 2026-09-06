import RiemannGaussian.EtaCurrentLinearHeatSchedule

/-!
# Summable weighted reconstruction at linear heat width

The actual zero-tail gain controls the midpoint term and the remaining
Gaussian defect has a logarithmic-power-over-square weighted majorant.
Together they give one finite all-cutoff budget for reconstructing the
unchanged original current at width `2(N+1)`. The signed weighted error
series is retained. The return's own first absolute moment remains open.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The midpoint term of the original return has summable odd-weighted
norm at linear heat width, using the actual zero-tail arithmetic gain. -/
theorem summable_oddEndpoint_mul_norm_pairedEtaLeadingCurrentLinearMidpointTerm (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦ (2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearMidpointTerm rho N‖) := by
  have hs := (summable_pairedEtaCurrent_midpointEnvelope_log_div rho).mul_left
    (2 * (analyticZetaZeroMultiplicity rho : ℝ) / Real.sqrt Real.pi)
  exact hs.of_nonneg_of_le (fun N ↦ by positivity) (pairedEtaLeadingCurrentLinearMidpointTerm_weighted_le rho)

/-- The remaining actual Gaussian defect is summable with the odd
arithmetic weight after the midpoint term is retained separately. -/
theorem summable_oddEndpoint_mul_norm_pairedEtaLeadingCurrentLinearHeatReturn_after_midpoint
    (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦ (2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho N -
      (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ) - pairedEtaLeadingCurrentLinearMidpointTerm rho N‖) := by
  have hs := (summable_pairedEtaCurrent_logPower_div_sq
    (2 * analyticZetaZeroMultiplicity rho + 3)).mul_left ((19 / 2) * pairedEtaLeadingCurrentMassConstant rho)
  apply hs.of_nonneg_of_le (fun N ↦ by positivity)
  intro N
  simpa only [mul_div_assoc] using pairedEtaLeadingCurrentLinearHeatReturn_after_midpoint_weighted_error_le rho N

/-- The explicit full linear-width reconstruction majorant has a genuine
finite sum for every actual nontrivial zero. -/
theorem summable_pairedEtaCurrentLinearHeatErrorMajorant (rho : NontrivialZetaZero) :
    Summable (pairedEtaCurrentLinearHeatErrorMajorant rho) :=
  ((summable_pairedEtaCurrent_logPower_div_sq (2 * analyticZetaZeroMultiplicity rho + 3)).mul_left
    ((19 / 2) * pairedEtaLeadingCurrentMassConstant rho)).add
      ((summable_pairedEtaCurrent_midpointEnvelope_log_div rho).mul_left
        (2 * (analyticZetaZeroMultiplicity rho : ℝ) / Real.sqrt Real.pi))

/-- The original completed current is reconstructed with summable
odd-weighted norm error on the actual full gap at linear heat width. -/
theorem summable_oddEndpoint_mul_norm_pairedEtaLeadingCurrentLinearHeatReturn_error (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦ (2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho N -
      (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ)‖) :=
  (summable_pairedEtaCurrentLinearHeatErrorMajorant rho).of_nonneg_of_le (fun N ↦ by positivity)
    (pairedEtaLeadingCurrentLinearHeatReturn_weighted_error_le rho)

/-- The signed complex weighted reconstruction error remains a convergent
series for the original linear-width return and original current. -/
theorem summable_oddEndpoint_smul_pairedEtaLeadingCurrentLinearHeatReturn_error (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦ (2 * N + 1 : ℝ) • (pairedEtaLeadingCurrentLinearHeatReturn rho N -
      (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ))) := by
  apply (summable_oddEndpoint_mul_norm_pairedEtaLeadingCurrentLinearHeatReturn_error rho).of_norm_bounded
  intro N
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * N + 1), le_refl]

/-- One explicit finite budget controls all partial sums of weighted
linear-width reconstruction error; its majorant is proved summable. -/
def pairedEtaCurrentLinearHeatWeightedErrorBound (rho : NontrivialZetaZero) : ℝ :=
  ∑' N : ℕ, pairedEtaCurrentLinearHeatErrorMajorant rho N

/-- The explicit linear-width weighted error budget is nonnegative. -/
theorem pairedEtaCurrentLinearHeatWeightedErrorBound_nonneg (rho : NontrivialZetaZero) :
    0 ≤ pairedEtaCurrentLinearHeatWeightedErrorBound rho :=
  tsum_nonneg (pairedEtaCurrentLinearHeatErrorMajorant_nonneg rho)

/-- Every finite weighted reconstruction error stays below the same
proved finite budget, independently of the terminal arithmetic cutoff. -/
theorem pairedEtaLeadingCurrentLinearHeatReturn_weighted_error_sum_le (rho : NontrivialZetaZero) (K : ℕ) :
    (∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho N -
      (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ)‖) ≤
      pairedEtaCurrentLinearHeatWeightedErrorBound rho := by
  calc
    _ ≤ ∑ N ∈ Finset.range K, pairedEtaCurrentLinearHeatErrorMajorant rho N := by
      apply Finset.sum_le_sum
      intro N _
      exact pairedEtaLeadingCurrentLinearHeatReturn_weighted_error_le rho N
    _ ≤ ∑' N : ℕ, pairedEtaCurrentLinearHeatErrorMajorant rho N :=
      (summable_pairedEtaCurrentLinearHeatErrorMajorant rho).sum_le_tsum _
        (fun N _ ↦ pairedEtaCurrentLinearHeatErrorMajorant_nonneg rho N)
    _ = _ := rfl

/-- The linear-width actual return preserves the first absolute-moment
frontier up to one finite error budget. This bounds the difference of
moments and supplies no bound for either moment itself. -/
theorem pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_stability (rho : NontrivialZetaZero) (K : ℕ) :
    |(∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho N‖) -
      (∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N|)| ≤
      pairedEtaCurrentLinearHeatWeightedErrorBound rho := by
  calc
    _ = |∑ N ∈ Finset.range K, ((2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho N‖ -
        (2 * N + 1 : ℝ) * |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N|)| := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ N ∈ Finset.range K, |(2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho N‖ -
        (2 * N + 1 : ℝ) * (|pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N|)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho N -
        (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ)‖ := by
      apply Finset.sum_le_sum
      intro N _
      have hw : (0 : ℝ) ≤ 2 * N + 1 := by positivity
      rw [← mul_sub, abs_mul, abs_of_nonneg hw]
      apply mul_le_mul_of_nonneg_left _ hw
      simpa only [Complex.norm_real, Real.norm_eq_abs] using
        abs_norm_sub_norm_le (pairedEtaLeadingCurrentLinearHeatReturn rho N) (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ)
    _ ≤ _ := pairedEtaLeadingCurrentLinearHeatReturn_weighted_error_sum_le rho K

end

end RiemannGaussian
