import RiemannGaussian.ZetaSignedLogarithmicGap
import RiemannGaussian.EtaLogarithmicZeroMargin

/-!
# An explicit reciprocal-logarithm zero-free strip

Signed prime positivity gives an unconditional margin for every actual
nontrivial zero. Reflection gives the same margin on both sides. The
original Gaussian return inherits the resulting exponent bound, while
all previous multiplicity-sensitive estimates remain available.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The explicit margin from the signed local logarithmic derivative
and the actual prime series. -/
def zetaSignedLogZeroMargin (y : ℝ) : ℝ :=
  |y| / (1800000 * (|y| + 1) * localZetaLogHeight y)

/-- The signed logarithmic margin is positive at every nonzero ordinate. -/
theorem zetaSignedLogZeroMargin_pos {y : ℝ} (hy : y ≠ 0) :
    0 < zetaSignedLogZeroMargin y := by
  have hL : 0 < localZetaLogHeight y := by linarith [two_lt_localZetaLogHeight y]
  exact div_pos (abs_pos.mpr hy) (by positivity)

/-- The explicit ratio fits inside the actual real-axis neighborhood
used in the signed pole estimate; no minimum is needed. -/
theorem zetaSignedLogZeroMargin_le_pole_width (y : ℝ) :
    zetaSignedLogZeroMargin y ≤ 1 / 112896 := by
  have hL := two_lt_localZetaLogHeight y
  have hLp : 0 < localZetaLogHeight y := by linarith
  unfold zetaSignedLogZeroMargin
  rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 112896)]
  have hp := mul_nonneg (abs_nonneg y) (by linarith : 0 ≤ localZetaLogHeight y - 2)
  nlinarith [abs_nonneg y]

/-- The margin is the exact reciprocal of the signed gap coefficient
at each nonzero ordinate. -/
theorem zetaSignedLogZeroMargin_mul_coefficient {y : ℝ} (hy : y ≠ 0) :
    zetaSignedLogZeroMargin y *
      (1800000 * localZetaLogHeight y * (1 + 1 / |y|)) = 1 := by
  have ht : 0 < |y| := abs_pos.mpr hy
  have hL : 0 < localZetaLogHeight y := by linarith [two_lt_localZetaLogHeight y]
  unfold zetaSignedLogZeroMargin
  field_simp

/-- Every actual nontrivial zero stays the explicit signed logarithmic
margin from the right edge of the critical strip. -/
theorem zetaSignedLogZeroMargin_le_one_sub_re (rho : NontrivialZetaZero) :
    zetaSignedLogZeroMargin rho.1.im ≤ 1 - rho.1.re := by
  by_cases hrho : 1 - 1 / 112896 ≤ rho.1.re
  · have h := one_le_signedLogHeight_mul_zero_gap rho hrho
    have he := zetaSignedLogZeroMargin_mul_coefficient (NontrivialZetaZero.im_ne_zero_of_eta_mass rho)
    have hp : 0 < 1800000 * localZetaLogHeight rho.1.im * (1 + 1 / |rho.1.im|) := by
      have hL : 0 < localZetaLogHeight rho.1.im := by linarith [two_lt_localZetaLogHeight rho.1.im]
      positivity
    nlinarith
  · exact (zetaSignedLogZeroMargin_le_pole_width rho.1.im).trans (by linarith)

/-- Reflection gives the same signed logarithmic margin at the left edge. -/
theorem zetaSignedLogZeroMargin_le_re (rho : NontrivialZetaZero) :
    zetaSignedLogZeroMargin rho.1.im ≤ rho.1.re := by
  have h := zetaSignedLogZeroMargin_le_one_sub_re (NontrivialZetaZero.conjugatePartner rho)
  simpa using h

/-- Every actual nontrivial zeta zero lies in the explicit
reciprocal-logarithm strip, with all analytic and arithmetic inputs proved. -/
theorem nontrivialZetaZero_mem_signedLogarithmic_strip (rho : NontrivialZetaZero) :
    rho.1.re ∈ Icc (zetaSignedLogZeroMargin rho.1.im) (1 - zetaSignedLogZeroMargin rho.1.im) :=
  ⟨zetaSignedLogZeroMargin_le_re rho, by linarith [zetaSignedLogZeroMargin_le_one_sub_re rho]⟩

/-- Above height one the explicit signed margin has reciprocal-logarithm
size with a fixed numerical constant. -/
theorem one_div_logHeight_le_zetaSignedLogZeroMargin {y : ℝ} (hy : 1 ≤ |y|) :
    1 / (3600000 * localZetaLogHeight y) ≤ zetaSignedLogZeroMargin y := by
  have hL : 0 < localZetaLogHeight y := by linarith [two_lt_localZetaLogHeight y]
  unfold zetaSignedLogZeroMargin
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- The checked strip has the classical reciprocal-logarithm shape at
all actual nontrivial zeros of absolute ordinate at least one. -/
theorem nontrivialZetaZero_mem_reciprocal_log_strip (rho : NontrivialZetaZero) (ht : 1 ≤ |rho.1.im|) :
    rho.1.re ∈ Icc (1 / (3600000 * localZetaLogHeight rho.1.im))
      (1 - 1 / (3600000 * localZetaLogHeight rho.1.im)) := by
  have h := nontrivialZetaZero_mem_signedLogarithmic_strip rho
  have hm := one_div_logHeight_le_zetaSignedLogZeroMargin ht
  constructor <;> linarith [h.1, h.2]

/-- Combining the signed margin with every previous multiplicity and
eta bound preserves the strongest established constraint. -/
def etaSignedPrimeProductZeroMargin (m : ℕ) (y : ℝ) : ℝ :=
  max (etaRefinedPrimeProductZeroMargin m y) (zetaSignedLogZeroMargin y)

/-- The original actual zero satisfies the combined signed and
multiplicity-sensitive strip bound. -/
theorem nontrivialZetaZero_mem_etaSignedPrimeProduct_strip (rho : NontrivialZetaZero) :
    rho.1.re ∈ Icc (etaSignedPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im)
      (1 - etaSignedPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im) := by
  have hprevious := nontrivialZetaZero_mem_etaRefinedPrimeProduct_strip rho
  have hsigned := nontrivialZetaZero_mem_signedLogarithmic_strip rho
  constructor
  · exact max_le hprevious.1 hsigned.1
  · have h : etaSignedPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im ≤ 1 - rho.1.re :=
      max_le (by linarith [hprevious.2]) (by linarith [hsigned.2])
    linarith

/-- The improved return exponent remains positive and depends on
the cutoff; the estimate does not give the uniform RH-strength bound. -/
theorem etaSignedPrimeProduct_return_exponent_bounds (rho : NontrivialZetaZero) :
    7 / 8 ≤ 1 - 2 * etaSignedPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im ∧
      1 - 2 * etaSignedPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im < 1 := by
  have hprevious := etaRefinedPrimeProduct_return_exponent_bounds rho
  have hsmall : etaSignedPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im ≤ 1 / 16 :=
    max_le (by linarith [hprevious.1]) ((zetaSignedLogZeroMargin_le_pole_width rho.1.im).trans (by norm_num))
  have hpos : 0 < etaSignedPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im :=
    (zetaSignedLogZeroMargin_pos (NontrivialZetaZero.im_ne_zero_of_eta_mass rho)).trans_le (le_max_right _ _)
  constructor <;> linarith

/-- The original Gaussian return retains its exact completion and
summable-error constant while acquiring the improved signed-prime exponent. -/
theorem pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_le_etaSignedPrimeProduct
    (rho : NontrivialZetaZero) (K : ℕ) :
    (∑ N ∈ Finset.range K, (2 * (N : ℝ) + 1) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho N‖) ≤
      pairedEtaCurrentReturnGrowthConstant rho *
        ((K : ℝ) + 1) ^ (1 - 2 * etaSignedPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im) := by
  have hstrip := nontrivialZetaZero_mem_etaSignedPrimeProduct_strip rho
  have hexp : pairedEtaCurrentHorizontalDisplacement rho ≤
      1 - 2 * etaSignedPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im := by
    unfold pairedEtaCurrentHorizontalDisplacement
    rw [abs_le]
    constructor <;> linarith [hstrip.1, hstrip.2]
  exact (pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_growth_le rho K).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) K]) hexp)
      (pairedEtaCurrentReturnGrowthConstant_nonneg rho))

end

end RiemannGaussian
