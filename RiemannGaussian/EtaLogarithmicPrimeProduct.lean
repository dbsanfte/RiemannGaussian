import RiemannGaussian.EtaLogarithmicStrip

/-!
# An independent logarithmic zero-gap inequality

The literal eta prefix, tail, dyadic rectangles, and Schwarz estimate
supply every analytic bound in the classical three-four-one prime
product. Only logarithmic height powers remain in its zero-gap constraint.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The explicit constant in the logarithmic prime-product constraint. -/
def etaLogPrimeProductConstant : ℝ := 144 * 4 ^ 3 * 576 ^ 4

/-- The logarithmic prime-product constant is strictly positive. -/
theorem etaLogPrimeProductConstant_pos : 0 < etaLogPrimeProductConstant := by
  norm_num [etaLogPrimeProductConstant]

/-- The actual zeta value at twice the ordinate has a logarithmic
bound on the short real segment used by the prime product. -/
theorem norm_riemannZeta_one_add_double_ordinate_le_etaLog {x y : ℝ}
    (hx : 0 < x) (hxhi : x ≤ (etaLogHeight y)⁻¹ / 16) (hy : y ≠ 0) :
    ‖riemannZeta (1 + x + 2 * I * y)‖ ≤
      144 * (|y| + 21) * etaLogHeight y ^ 2 / |y| := by
  obtain ⟨he, hehi⟩ := etaLogHeight_inv_bounds y
  have him : (1 + (x : ℂ) + 2 * I * y).im = 2 * y := by simp
  have himabs : |(1 + (x : ℂ) + 2 * I * y).im| = 2 * |y| := by
    rw [him, abs_mul]; norm_num
  have hlo : 1 - (etaLogHeight y)⁻¹ ≤ (1 + (x : ℂ) + 2 * I * y).re := by
    simp; linarith
  have hhi : (1 + (x : ℂ) + 2 * I * y).re ≤ 1 + (etaLogHeight y)⁻¹ := by
    simp; linarith
  have hp : (2 * |y| + 20) ^ (etaLogHeight y)⁻¹ ≤ 6 := by
    calc
      _ ≤ (2 * (|y| + 21)) ^ (etaLogHeight y)⁻¹ := by
        apply Real.rpow_le_rpow (by positivity) _ he.le
        linarith
      _ = (2 : ℝ) ^ (etaLogHeight y)⁻¹ * Real.exp 1 := by
        rw [Real.mul_rpow (by norm_num) (by positivity), etaLogHeight_rpow_inv]
      _ ≤ 2 * 3 := by
        apply mul_le_mul _ Real.exp_one_lt_three.le (Real.exp_pos 1).le (by norm_num)
        exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by linarith : (etaLogHeight y)⁻¹ ≤ 1)).trans_eq (Real.rpow_one 2)
      _ = _ := by norm_num
  have hb : ‖riemannZeta₁ (1 + x + 2 * I * y)‖ ≤
      288 * (|y| + 21) * etaLogHeight y ^ 2 := by
    have h := norm_riemannZeta₁_le_etaThinStrip he hehi hlo hhi
    rw [himabs] at h
    calc
      _ ≤ 24 * (2 * |y| + 20) * (2 * |y| + 20) ^ (etaLogHeight y)⁻¹ /
          ((etaLogHeight y)⁻¹) ^ 2 := h
      _ ≤ 24 * (2 * (|y| + 21)) * 6 / ((etaLogHeight y)⁻¹) ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul (by linarith) hp (by positivity) (by positivity)
      _ = _ := by rw [inv_pow, div_inv_eq_mul]; ring
  calc
    _ ≤ ‖riemannZeta₁ (1 + x + 2 * I * y)‖ / |(1 + (x : ℂ) + 2 * I * y).im| :=
      norm_riemannZeta_le_poleRemoved_div_abs_im (by rw [him]; exact mul_ne_zero (by norm_num) hy)
    _ ≤ (288 * (|y| + 21) * etaLogHeight y ^ 2) / (2 * |y|) := by
      rw [himabs]
      exact div_le_div_of_nonneg_right hb (by positivity)
    _ = _ := by ring

/-- Independent prime positivity bounds the actual zero gap with a
fourteenth logarithmic power, retaining the exact ordinate dependence. -/
theorem one_le_etaLogPrimeProduct_zero_gap (rho : NontrivialZetaZero)
    (hrho : 1 - (etaLogHeight rho.1.im)⁻¹ / 16 ≤ rho.1.re) :
    1 ≤ (etaLogPrimeProductConstant * (|rho.1.im| + 21) ^ 5 * etaLogHeight rho.1.im ^ 14 /
      |rho.1.im| ^ 5) * (1 - rho.1.re) := by
  let d := 1 - rho.1.re
  let t := |rho.1.im|
  let L := etaLogHeight rho.1.im
  have hd : 0 < d := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have hdhi : d ≤ L⁻¹ / 16 := by dsimp [d, L]; linarith
  have him := NontrivialZetaZero.im_ne_zero_of_eta_mass rho
  have ht : 0 < t := abs_pos.mpr him
  have hbase : (1 + (d : ℂ) + I * rho.1.im) =
      (((2 - rho.1.re : ℝ) : ℂ) + I * rho.1.im) := by dsimp [d]; push_cast; ring
  have hvalue : ‖riemannZeta (1 + (d : ℂ) + I * rho.1.im)‖ ≤
      576 * (t + 21) * L ^ 3 * d / t := by
    have him' : (1 + (d : ℂ) + I * rho.1.im).im = rho.1.im := by simp
    calc
      _ ≤ ‖riemannZeta₁ (1 + (d : ℂ) + I * rho.1.im)‖ / t := by
        simpa only [him', t] using norm_riemannZeta_le_poleRemoved_div_abs_im
          (s := 1 + (d : ℂ) + I * rho.1.im) (by rw [him']; exact him)
      _ ≤ _ := by
        rw [hbase]
        exact div_le_div_of_nonneg_right (norm_riemannZeta₁_reflected_across_one_le_etaLog rho hrho) ht.le
  have hreal := norm_riemannZeta_one_add_le_four_div hd
    (show d ≤ 1 / 2 by linarith [(etaLogHeight_inv_bounds rho.1.im).2])
  have hdouble := norm_riemannZeta_one_add_double_ordinate_le_etaLog hd hdhi him
  have hp := one_le_riemannZeta_three_four_one hd rho.1.im
  have hupper : ‖riemannZeta (1 + (d : ℂ))‖ ^ 3 *
      ‖riemannZeta (1 + (d : ℂ) + I * rho.1.im)‖ ^ 4 *
      ‖riemannZeta (1 + (d : ℂ) + 2 * I * rho.1.im)‖ ≤
      (4 / d) ^ 3 * (576 * (t + 21) * L ^ 3 * d / t) ^ 4 * (144 * (t + 21) * L ^ 2 / t) := by
    gcongr
  refine (hp.trans hupper).trans_eq ?_
  change (4 / d) ^ 3 * (576 * (t + 21) * L ^ 3 * d / t) ^ 4 * (144 * (t + 21) * L ^ 2 / t) =
    (etaLogPrimeProductConstant * (t + 21) ^ 5 * L ^ 14 / t ^ 5) * d
  unfold etaLogPrimeProductConstant
  field_simp

end

end RiemannGaussian
