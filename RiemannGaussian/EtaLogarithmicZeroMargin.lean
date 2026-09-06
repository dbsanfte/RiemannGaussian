import RiemannGaussian.EtaLogarithmicPrimeProduct
import RiemannGaussian.EtaPrimeProductMultiplicityComparison

/-!
# A logarithmic zero margin for the original Gaussian return

The explicit prime-product ratio is small enough to satisfy the analytic
disc threshold at every ordinate. It therefore gives an unconditional
two-sided zero bound. Taking its maximum with the earlier multiplicity
margin retains both independent estimates for the unchanged return.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The explicit zero margin from height-adapted eta and prime positivity. -/
def etaLogPrimeProductZeroMargin (y : ℝ) : ℝ :=
  |y| ^ 5 / (etaLogPrimeProductConstant * (|y| + 21) ^ 5 * etaLogHeight y ^ 14)

/-- The logarithmic margin is positive at every nonzero ordinate. -/
theorem etaLogPrimeProductZeroMargin_pos {y : ℝ} (hy : y ≠ 0) :
    0 < etaLogPrimeProductZeroMargin y := by
  have ht := abs_pos.mpr hy
  have hL : 0 < etaLogHeight y := by linarith [two_lt_etaLogHeight y]
  unfold etaLogPrimeProductZeroMargin
  exact div_pos (pow_pos ht 5) (by have := etaLogPrimeProductConstant_pos; positivity)

/-- The explicit ratio always lies below the actual analytic-disc
threshold; no additional minimum is needed in its definition. -/
theorem etaLogPrimeProductZeroMargin_le_disc_width (y : ℝ) :
    etaLogPrimeProductZeroMargin y ≤ (etaLogHeight y)⁻¹ / 16 := by
  have hL : 1 ≤ etaLogHeight y := by linarith [two_lt_etaLogHeight y]
  have hLp : 0 < etaLogHeight y := by linarith
  have hC : 16 ≤ etaLogPrimeProductConstant := by norm_num [etaLogPrimeProductConstant]
  have ht : |y| ^ 5 ≤ (|y| + 21) ^ 5 := by gcongr; linarith
  have hpow : etaLogHeight y ≤ etaLogHeight y ^ 14 := by
    simpa using pow_le_pow_right₀ hL (show 1 ≤ 14 by omega)
  have hden : 0 < etaLogPrimeProductConstant * (|y| + 21) ^ 5 * etaLogHeight y ^ 14 := by
    have := etaLogPrimeProductConstant_pos
    positivity
  unfold etaLogPrimeProductZeroMargin
  rw [inv_eq_one_div, div_div, div_le_div_iff₀ hden (by positivity)]
  have hm := mul_le_mul ht (mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 16))
    (by positivity) (by positivity : (0 : ℝ) ≤ (|y| + 21) ^ 5)
  have hc := mul_le_mul_of_nonneg_right hC
    (by positivity : (0 : ℝ) ≤ (|y| + 21) ^ 5 * etaLogHeight y ^ 14)
  nlinarith

/-- Every actual zero stays its explicit logarithmic margin from the
right edge of the critical strip. -/
theorem etaLogPrimeProductZeroMargin_le_one_sub_re (rho : NontrivialZetaZero) :
    etaLogPrimeProductZeroMargin rho.1.im ≤ 1 - rho.1.re := by
  by_cases hrho : 1 - (etaLogHeight rho.1.im)⁻¹ / 16 ≤ rho.1.re
  · have ht : 0 < |rho.1.im| := abs_pos.mpr (NontrivialZetaZero.im_ne_zero_of_eta_mass rho)
    have hL : 0 < etaLogHeight rho.1.im := by linarith [two_lt_etaLogHeight rho.1.im]
    have hc : 0 < etaLogPrimeProductConstant * (|rho.1.im| + 21) ^ 5 * etaLogHeight rho.1.im ^ 14 := by
      have := etaLogPrimeProductConstant_pos
      positivity
    unfold etaLogPrimeProductZeroMargin
    rw [div_le_iff₀ hc]
    have h := one_le_etaLogPrimeProduct_zero_gap rho hrho
    rw [div_mul_eq_mul_div] at h
    have hp := (le_div_iff₀ (pow_pos ht 5)).mp h
    simpa only [one_mul, mul_one, mul_comm] using hp
  · exact (etaLogPrimeProductZeroMargin_le_disc_width rho.1.im).trans (by linarith)

/-- Reflection gives the identical logarithmic margin at the left edge. -/
theorem etaLogPrimeProductZeroMargin_le_re (rho : NontrivialZetaZero) :
    etaLogPrimeProductZeroMargin rho.1.im ≤ rho.1.re := by
  have h := etaLogPrimeProductZeroMargin_le_one_sub_re (NontrivialZetaZero.conjugatePartner rho)
  simpa using h

/-- Every actual nontrivial zero lies inside the explicit logarithmic
strip, with no assumed zero-location estimate. -/
theorem nontrivialZetaZero_mem_etaLogPrimeProduct_strip (rho : NontrivialZetaZero) :
    rho.1.re ∈ Icc (etaLogPrimeProductZeroMargin rho.1.im) (1 - etaLogPrimeProductZeroMargin rho.1.im) :=
  ⟨etaLogPrimeProductZeroMargin_le_re rho, by linarith [etaLogPrimeProductZeroMargin_le_one_sub_re rho]⟩

/-- The combined margin retains the logarithmic bound and the full
analytic-multiplicity bound without weakening either one. -/
def etaRefinedPrimeProductZeroMargin (m : ℕ) (y : ℝ) : ℝ :=
  max (etaPrimeProductMultiplicityZeroMargin m y) (etaLogPrimeProductZeroMargin y)

/-- Both independent margins constrain each original actual zero. -/
theorem nontrivialZetaZero_mem_etaRefinedPrimeProduct_strip (rho : NontrivialZetaZero) :
    rho.1.re ∈ Icc
      (etaRefinedPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im)
      (1 - etaRefinedPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im) := by
  have hm := nontrivialZetaZero_mem_etaPrimeProductMultiplicity_strip rho
  have hl := nontrivialZetaZero_mem_etaLogPrimeProduct_strip rho
  constructor
  · exact max_le hm.1 hl.1
  · have h : etaRefinedPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im ≤
        1 - rho.1.re := max_le (by linarith [hm.2]) (by linarith [hl.2])
    linarith

/-- The combined margin still gives a positive, cutoff-dependent
return exponent, so it does not establish uniform boundedness. -/
theorem etaRefinedPrimeProduct_return_exponent_bounds (rho : NontrivialZetaZero) :
    7 / 8 ≤ 1 - 2 * etaRefinedPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im ∧
      1 - 2 * etaRefinedPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im < 1 := by
  have hlog : etaLogPrimeProductZeroMargin rho.1.im ≤ 1 / 16 :=
    (etaLogPrimeProductZeroMargin_le_disc_width rho.1.im).trans
      (by linarith [(etaLogHeight_inv_bounds rho.1.im).2])
  have hmax : etaRefinedPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im ≤ 1 / 16 :=
    max_le (etaPrimeProductMultiplicityZeroMargin_le_sixteenth _ _) hlog
  have hpos : 0 < etaRefinedPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im :=
    (etaLogPrimeProductZeroMargin_pos (NontrivialZetaZero.im_ne_zero_of_eta_mass rho)).trans_le
      (le_max_right _ _)
  constructor <;> linarith

/-- The original return's weighted first absolute moment has the
exponent supplied by both independent zero margins. -/
theorem pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_le_etaRefinedPrimeProduct
    (rho : NontrivialZetaZero) (K : ℕ) :
    (∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho N‖) ≤
      pairedEtaCurrentReturnGrowthConstant rho * (K + 1 : ℝ) ^
        (1 - 2 * etaRefinedPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im) := by
  have hstrip := nontrivialZetaZero_mem_etaRefinedPrimeProduct_strip rho
  have hdisp : pairedEtaCurrentHorizontalDisplacement rho ≤
      1 - 2 * etaRefinedPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im := by
    unfold pairedEtaCurrentHorizontalDisplacement
    exact abs_le.mpr ⟨by linarith [hstrip.1], by linarith [hstrip.2]⟩
  apply (pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_growth_le rho K).trans
  apply mul_le_mul_of_nonneg_left _ (pairedEtaCurrentReturnGrowthConstant_nonneg rho)
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) K]) hdisp

end

end RiemannGaussian
