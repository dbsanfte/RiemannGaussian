import RiemannGaussian.EtaPrimeProductMultiplicityGap
import RiemannGaussian.EtaPrimeProductZeroMargin

/-!
# An explicit zero margin retaining analytic multiplicity

Taking the positive `4*m-3` root of the checked prime-product constraint
gives an ordinate- and multiplicity-dependent exclusion at each strip edge.
The reflection partner has the same multiplicity and ordinate. This bounds
the original return-growth exponent while leaving the cutoff-independent
weighted estimate open.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The explicit positive root margin supplied by full multiplicity in
the eta-derived prime-product estimate. Its use at a zero has `m>=1`. -/
def etaPrimeProductMultiplicityZeroMargin (m : ℕ) (y : ℝ) : ℝ :=
  min (1 / 16) ((|y| ^ 5 / (16 * 3200 ^ 3 * 8 ^ (4 * m + 4) * (|y| + 21) ^ 10)) ^
    (((4 * m - 3 : ℕ) : ℝ)⁻¹))

/-- The multiplicity margin is positive at every nonzero ordinate. -/
theorem etaPrimeProductMultiplicityZeroMargin_pos (m : ℕ) {y : ℝ} (hy : y ≠ 0) :
    0 < etaPrimeProductMultiplicityZeroMargin m y := by
  have ht : 0 < |y| := abs_pos.mpr hy
  unfold etaPrimeProductMultiplicityZeroMargin
  positivity

/-- The margin retains the threshold needed to place the reflected
evaluation point inside the disc of the Schwarz estimate. -/
theorem etaPrimeProductMultiplicityZeroMargin_le_sixteenth (m : ℕ) (y : ℝ) :
    etaPrimeProductMultiplicityZeroMargin m y ≤ 1 / 16 := min_le_left _ _

/-- Every actual zero stays at least its explicit multiplicity margin
away from the pole line. The root exponent is proved positive. -/
theorem etaPrimeProductMultiplicityZeroMargin_le_one_sub_re (rho : NontrivialZetaZero) :
    etaPrimeProductMultiplicityZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im ≤ 1 - rho.1.re := by
  by_cases hrho : 15 / 16 ≤ rho.1.re
  · refine (min_le_right _ _).trans ?_
    have hm := analyticZetaZeroMultiplicity_positive rho
    have hp : 0 < 4 * analyticZetaZeroMultiplicity rho - 3 := by omega
    have hq : 0 ≤ |rho.1.im| ^ 5 /
        (16 * 3200 ^ 3 * 8 ^ (4 * analyticZetaZeroMultiplicity rho + 4) * (|rho.1.im| + 21) ^ 10) := by
      positivity
    have h := Real.rpow_le_rpow hq (etaPrimeProduct_multiplicity_gap_power_le rho hrho)
      (show 0 ≤ (((4 * analyticZetaZeroMultiplicity rho - 3 : ℕ) : ℝ)⁻¹) by positivity)
    exact h.trans_eq (Real.pow_rpow_inv_natCast
      (sub_nonneg.mpr (NontrivialZetaZero.re_lt_one rho).le) hp.ne')
  · exact (etaPrimeProductMultiplicityZeroMargin_le_sixteenth _ _).trans (by linarith)

/-- Reflection preserves the actual multiplicity and ordinate, giving
the same explicit exclusion at the opposite strip edge. -/
theorem etaPrimeProductMultiplicityZeroMargin_le_re (rho : NontrivialZetaZero) :
    etaPrimeProductMultiplicityZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im ≤ rho.1.re := by
  have h := etaPrimeProductMultiplicityZeroMargin_le_one_sub_re (NontrivialZetaZero.conjugatePartner rho)
  simpa using h

/-- Every original nontrivial zeta zero lies in the explicit strip
determined by its ordinate and its full analytic multiplicity. -/
theorem nontrivialZetaZero_mem_etaPrimeProductMultiplicity_strip (rho : NontrivialZetaZero) :
    rho.1.re ∈ Icc
      (etaPrimeProductMultiplicityZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im)
      (1 - etaPrimeProductMultiplicityZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im) := by
  exact ⟨etaPrimeProductMultiplicityZeroMargin_le_re rho,
    by linarith [etaPrimeProductMultiplicityZeroMargin_le_one_sub_re rho]⟩

/-- The multiplicity-dependent zero margin controls the horizontal
displacement in the unchanged return-growth theorem. -/
theorem pairedEtaCurrentHorizontalDisplacement_le_etaPrimeProductMultiplicity (rho : NontrivialZetaZero) :
    pairedEtaCurrentHorizontalDisplacement rho ≤
      1 - 2 * etaPrimeProductMultiplicityZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im := by
  have h := nontrivialZetaZero_mem_etaPrimeProductMultiplicity_strip rho
  unfold pairedEtaCurrentHorizontalDisplacement
  exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩

/-- The multiplicity-based return exponent remains positive. Its
arithmetic improvement does not supply a uniform bound in the cutoff. -/
theorem etaPrimeProductMultiplicity_return_exponent_bounds (rho : NontrivialZetaZero) :
    7 / 8 ≤ 1 - 2 * etaPrimeProductMultiplicityZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im ∧
      1 - 2 * etaPrimeProductMultiplicityZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im < 1 := by
  have hp := etaPrimeProductMultiplicityZeroMargin_pos (analyticZetaZeroMultiplicity rho)
    (NontrivialZetaZero.im_ne_zero_of_eta_mass rho)
  have hq := etaPrimeProductMultiplicityZeroMargin_le_sixteenth (analyticZetaZeroMultiplicity rho) rho.1.im
  constructor <;> linarith

/-- The actual Gaussian return has an explicit multiplicity-dependent
growth exponent. This remains a cutoff-dependent bound. -/
theorem pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_le_etaPrimeProductMultiplicity
    (rho : NontrivialZetaZero) (K : ℕ) :
    (∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho N‖) ≤
      pairedEtaCurrentReturnGrowthConstant rho * (K + 1 : ℝ) ^
        (1 - 2 * etaPrimeProductMultiplicityZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im) := by
  apply (pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_growth_le rho K).trans
  apply mul_le_mul_of_nonneg_left _ (pairedEtaCurrentReturnGrowthConstant_nonneg rho)
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) K])
    (pairedEtaCurrentHorizontalDisplacement_le_etaPrimeProductMultiplicity rho)

end

end RiemannGaussian
