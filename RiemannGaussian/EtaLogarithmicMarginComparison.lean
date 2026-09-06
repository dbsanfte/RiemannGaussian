import RiemannGaussian.EtaLogarithmicZeroMargin

/-!
# Quantitative comparison with the previous zero margin

The new ordinate-only margin is strictly larger than the earlier
ordinate-only margin at every nonzero height. Above height twenty-one it
also dominates an explicit reciprocal fourteenth logarithmic power.
The maximum with the existing multiplicity margin preserves repeated-zero
information and gives a strict improvement for every actual simple zero.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- A single positive term of the exponential series gives the exact
logarithmic power comparison needed to compare the zero margins. -/
theorem etaLogHeight_pow_fourteen_le (y : ℝ) :
    etaLogHeight y ^ 14 ≤ 15 * (|y| + 21) ^ 5 := by
  have hL : 0 < etaLogHeight y := by linarith [two_lt_etaLogHeight y]
  have h := Real.pow_div_factorial_le_exp (5 * etaLogHeight y)
    (show 0 ≤ 5 * etaLogHeight y by positivity) 14
  have he : Real.exp (5 * etaLogHeight y) = (|y| + 21) ^ 5 := by
    rw [show (5 : ℝ) = (5 : ℕ) by norm_num, Real.exp_nat_mul,
      etaLogHeight, Real.exp_log (by positivity)]
  rw [he, mul_pow] at h
  norm_num at h
  nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ |y| + 21) 5]

/-- The logarithmic margin strictly improves the original
ordinate-only margin at every nonzero ordinate. -/
theorem etaPrimeProductZeroMargin_lt_logarithmic {y : ℝ} (hy : y ≠ 0) :
    etaPrimeProductZeroMargin y < etaLogPrimeProductZeroMargin y := by
  have ht : 0 < |y| := abs_pos.mpr hy
  have hL : 0 < etaLogHeight y := by linarith [two_lt_etaLogHeight y]
  have hC := etaLogPrimeProductConstant_pos
  rw [etaPrimeProductZeroMargin_eq_ratio, etaLogPrimeProductZeroMargin]
  apply div_lt_div_of_pos_left (pow_pos ht 5) (by positivity)
  calc
    _ ≤ etaLogPrimeProductConstant * (|y| + 21) ^ 5 * (15 * (|y| + 21) ^ 5) :=
      mul_le_mul_of_nonneg_left (etaLogHeight_pow_fourteen_le y) (by positivity)
    _ = (15 * etaLogPrimeProductConstant) * (|y| + 21) ^ 10 := by ring
    _ < _ := by
      apply mul_lt_mul_of_pos_right _ (by positivity : (0 : ℝ) < (|y| + 21) ^ 10)
      norm_num [etaLogPrimeProductConstant]

/-- Above height twenty-one the margin has a purely logarithmic
lower bound, with no remaining negative power of the height. -/
theorem one_div_logHeight_pow_le_etaLogPrimeProductZeroMargin {y : ℝ} (hy : 21 ≤ |y|) :
    1 / (32 * etaLogPrimeProductConstant * etaLogHeight y ^ 14) ≤ etaLogPrimeProductZeroMargin y := by
  have ht : 0 < |y| := by linarith
  have hL : 0 < etaLogHeight y := by linarith [two_lt_etaLogHeight y]
  have hC := etaLogPrimeProductConstant_pos
  have hp : (|y| + 21) ^ 5 ≤ 32 * |y| ^ 5 := by
    calc
      _ ≤ (2 * |y|) ^ 5 := by gcongr; linarith
      _ = _ := by ring
  unfold etaLogPrimeProductZeroMargin
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hm := mul_le_mul_of_nonneg_left hp
    (by positivity : (0 : ℝ) ≤ etaLogPrimeProductConstant * etaLogHeight y ^ 14)
  nlinarith

/-- Every actual zero above height twenty-one lies in an explicit
strip whose edge margin is a reciprocal fourteenth logarithmic power. -/
theorem nontrivialZetaZero_mem_reciprocal_logarithmic_strip (rho : NontrivialZetaZero)
    (ht : 21 ≤ |rho.1.im|) :
    rho.1.re ∈ Icc (1 / (32 * etaLogPrimeProductConstant * etaLogHeight rho.1.im ^ 14))
      (1 - 1 / (32 * etaLogPrimeProductConstant * etaLogHeight rho.1.im ^ 14)) := by
  have hm := one_div_logHeight_pow_le_etaLogPrimeProductZeroMargin ht
  have hz := nontrivialZetaZero_mem_etaLogPrimeProduct_strip rho
  exact ⟨hm.trans hz.1, by linarith [hz.2]⟩

/-- At an actual simple zero, the new combined margin equals the
strictly stronger logarithmic margin. -/
theorem etaRefinedPrimeProductZeroMargin_eq_logarithmic_of_simple (rho : NontrivialZetaZero)
    (hm : analyticZetaZeroMultiplicity rho = 1) :
    etaRefinedPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im =
      etaLogPrimeProductZeroMargin rho.1.im := by
  unfold etaRefinedPrimeProductZeroMargin
  rw [hm, etaPrimeProductMultiplicityZeroMargin_one]
  exact max_eq_right (etaPrimeProductZeroMargin_lt_logarithmic
    (NontrivialZetaZero.im_ne_zero_of_eta_mass rho)).le

/-- The original return's proved exponent strictly decreases at
every actual simple zero compared with the previous multiplicity bound. -/
theorem etaRefinedPrimeProduct_return_exponent_lt_of_simple (rho : NontrivialZetaZero)
    (hm : analyticZetaZeroMultiplicity rho = 1) :
    1 - 2 * etaRefinedPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im <
      1 - 2 * etaPrimeProductMultiplicityZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im := by
  rw [etaRefinedPrimeProductZeroMargin_eq_logarithmic_of_simple rho hm, hm,
    etaPrimeProductMultiplicityZeroMargin_one]
  linarith [etaPrimeProductZeroMargin_lt_logarithmic (NontrivialZetaZero.im_ne_zero_of_eta_mass rho)]

end

end RiemannGaussian
