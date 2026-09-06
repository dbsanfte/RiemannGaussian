import RiemannGaussian.ZetaSignedZeroMargin
import RiemannGaussian.EtaLogarithmicMarginComparison

/-!
# Strict improvement from retaining the signed pole contribution

The new signed logarithmic margin is strictly larger than the previous
fourteenth-logarithmic-power margin at every nonzero ordinate. Taking the
maximum preserves all existing multiplicity information, and the original
Gaussian return has a strictly improved exponent at every actual simple zero.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The new translated-disc logarithmic height is at most twice the
previous eta logarithmic height at every real ordinate. -/
theorem localZetaLogHeight_le_two_etaLogHeight (y : ℝ) :
    localZetaLogHeight y ≤ 2 * etaLogHeight y := by
  unfold localZetaLogHeight etaLogHeight
  calc
    Real.log (|y| + 22) ≤ Real.log ((|y| + 21) ^ 2) :=
      Real.log_le_log (by positivity) (by nlinarith [abs_nonneg y])
    _ = _ := by rw [Real.log_pow]; norm_num

/-- The signed prime estimate strictly improves the previously
proved logarithmic zero margin at every nonzero ordinate. -/
theorem etaLogPrimeProductZeroMargin_lt_signed {y : ℝ} (hy : y ≠ 0) :
    etaLogPrimeProductZeroMargin y < zetaSignedLogZeroMargin y := by
  have ht : 0 < |y| := abs_pos.mpr hy
  have hL : 1 ≤ etaLogHeight y := by linarith [two_lt_etaLogHeight y]
  have hLp : 0 < etaLogHeight y := by linarith
  have hlocal : 0 < localZetaLogHeight y := by linarith [two_lt_localZetaLogHeight y]
  have hC := etaLogPrimeProductConstant_pos
  have hpoly : |y| ^ 4 * (|y| + 1) ≤ (|y| + 21) ^ 5 := by
    calc
      _ ≤ (|y| + 21) ^ 4 * (|y| + 21) :=
        mul_le_mul (pow_le_pow_left₀ (abs_nonneg y) (by linarith) 4)
          (by linarith) (by positivity) (by positivity)
      _ = _ := by ring
  have hpow : etaLogHeight y ≤ etaLogHeight y ^ 14 := by
    simpa using pow_le_pow_right₀ hL (show 1 ≤ 14 by omega)
  have hcoeff : 3600000 * etaLogHeight y < etaLogPrimeProductConstant * etaLogHeight y ^ 14 := by
    calc
      _ < etaLogPrimeProductConstant * etaLogHeight y :=
        mul_lt_mul_of_pos_right (by norm_num [etaLogPrimeProductConstant]) hLp
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow hC.le
  unfold etaLogPrimeProductZeroMargin zetaSignedLogZeroMargin
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  calc
    |y| ^ 5 * (1800000 * (|y| + 1) * localZetaLogHeight y) ≤
        |y| ^ 5 * (1800000 * (|y| + 1) * (2 * etaLogHeight y)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (localZetaLogHeight_le_two_etaLogHeight y) (by positivity))
        (by positivity)
    _ = (3600000 * etaLogHeight y) * (|y| * (|y| ^ 4 * (|y| + 1))) := by ring
    _ ≤ (3600000 * etaLogHeight y) * (|y| * (|y| + 21) ^ 5) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpoly ht.le) (by positivity)
    _ < (etaLogPrimeProductConstant * etaLogHeight y ^ 14) * (|y| * (|y| + 21) ^ 5) :=
      mul_lt_mul_of_pos_right hcoeff (by positivity)
    _ = _ := by ring

/-- At every actual simple zero the combined bound equals the
strictly stronger signed logarithmic margin. -/
theorem etaSignedPrimeProductZeroMargin_eq_signed_of_simple (rho : NontrivialZetaZero)
    (hm : analyticZetaZeroMultiplicity rho = 1) :
    etaSignedPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im =
      zetaSignedLogZeroMargin rho.1.im := by
  unfold etaSignedPrimeProductZeroMargin
  rw [etaRefinedPrimeProductZeroMargin_eq_logarithmic_of_simple rho hm]
  exact max_eq_right (etaLogPrimeProductZeroMargin_lt_signed
    (NontrivialZetaZero.im_ne_zero_of_eta_mass rho)).le

/-- The original Gaussian return's exponent strictly decreases at
every actual simple zero relative to the previous logarithmic estimate. -/
theorem etaSignedPrimeProduct_return_exponent_lt_of_simple (rho : NontrivialZetaZero)
    (hm : analyticZetaZeroMultiplicity rho = 1) :
    1 - 2 * etaSignedPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im <
      1 - 2 * etaRefinedPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im := by
  rw [etaSignedPrimeProductZeroMargin_eq_signed_of_simple rho hm,
    etaRefinedPrimeProductZeroMargin_eq_logarithmic_of_simple rho hm]
  linarith [etaLogPrimeProductZeroMargin_lt_signed (NontrivialZetaZero.im_ne_zero_of_eta_mass rho)]

end

end RiemannGaussian
