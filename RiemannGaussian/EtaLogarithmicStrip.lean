import RiemannGaussian.EtaThinStripRectangle
import RiemannGaussian.EtaZetaMultiplicitySchwarz

/-!
# Logarithmic-width zeta bounds at actual zeros

Choosing strip width `1/log(|y|+21)` removes the remaining small power of
height. The entire pole-removed function is controlled on an actual disc
about each sufficiently near-edge zero. Schwarz's lemma then gives the
small value needed by independent prime positivity.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The positive logarithmic height used to choose the analytic strip. -/
def etaLogHeight (y : ℝ) : ℝ := Real.log (|y| + 21)

/-- The logarithmic height exceeds two even at ordinate zero. -/
theorem two_lt_etaLogHeight (y : ℝ) : 2 < etaLogHeight y := by
  have hexp : Real.exp 2 < 9 := by
    have he : Real.exp 2 = Real.exp 1 ^ 2 := by
      simp [← Real.exp_nat_mul]
    rw [he]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
  exact (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < |y| + 21)).mpr
    (by linarith [abs_nonneg y])

/-- The chosen strip width is positive and at most one half. -/
theorem etaLogHeight_inv_bounds (y : ℝ) :
    0 < (etaLogHeight y)⁻¹ ∧ (etaLogHeight y)⁻¹ ≤ 1 / 2 := by
  have hL : 0 < etaLogHeight y := by linarith [two_lt_etaLogHeight y]
  constructor
  · positivity
  · rw [inv_eq_one_div, div_le_iff₀ hL]
    linarith [two_lt_etaLogHeight y]

/-- At the selected width the small height power is exactly `exp(1)`. -/
theorem etaLogHeight_rpow_inv (y : ℝ) :
    (|y| + 21) ^ (etaLogHeight y)⁻¹ = Real.exp 1 := by
  have hL : etaLogHeight y ≠ 0 := ne_of_gt (by linarith [two_lt_etaLogHeight y])
  rw [Real.rpow_def_of_pos (by positivity), ← etaLogHeight, mul_inv_cancel₀ hL]

/-- Near an ordinate, the thin-strip estimate becomes a linear height
factor times the square of its logarithm. -/
theorem norm_riemannZeta₁_le_etaLogStrip {s : ℂ} {y : ℝ}
    (hslo : 1 - (etaLogHeight y)⁻¹ ≤ s.re)
    (hshi : s.re ≤ 1 + (etaLogHeight y)⁻¹) (him : |s.im| + 20 ≤ |y| + 21) :
    ‖riemannZeta₁ s‖ ≤ 72 * (|y| + 21) * etaLogHeight y ^ 2 := by
  obtain ⟨he, hehi⟩ := etaLogHeight_inv_bounds y
  have hp := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ |s.im| + 20) him he.le
  rw [etaLogHeight_rpow_inv] at hp
  have hb := norm_riemannZeta₁_le_etaThinStrip he hehi hslo hshi
  calc
    _ ≤ 24 * (|s.im| + 20) * (|s.im| + 20) ^ (etaLogHeight y)⁻¹ /
        ((etaLogHeight y)⁻¹) ^ 2 := hb
    _ ≤ 24 * (|y| + 21) * 3 / ((etaLogHeight y)⁻¹) ^ 2 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_left him (by norm_num))
          (hp.trans Real.exp_one_lt_three.le) (by positivity) (by positivity)) (by positivity)
    _ = _ := by rw [inv_pow, div_inv_eq_mul]; ring

/-- A whole disc about an actual near-edge zero has a proved
logarithmic zeta envelope, uniformly through dyadic resonances. -/
theorem norm_riemannZeta₁_le_etaLog_zero_ball (rho : NontrivialZetaZero)
    (hrho : 1 - (etaLogHeight rho.1.im)⁻¹ / 2 ≤ rho.1.re)
    {z : ℂ} (hz : z ∈ ball rho.1 ((etaLogHeight rho.1.im)⁻¹ / 4)) :
    ‖riemannZeta₁ z‖ ≤ 72 * (|rho.1.im| + 21) * etaLogHeight rho.1.im ^ 2 := by
  have hehi := (etaLogHeight_inv_bounds rho.1.im).2
  have he := (etaLogHeight_inv_bounds rho.1.im).1
  have hdist : ‖z - rho.1‖ < (etaLogHeight rho.1.im)⁻¹ / 4 := by
    simpa only [mem_ball, dist_eq_norm] using hz
  have hre : |z.re - rho.1.re| < (etaLogHeight rho.1.im)⁻¹ / 4 := by
    simpa only [Complex.sub_re] using (Complex.abs_re_le_norm (z - rho.1)).trans_lt hdist
  have him : |z.im - rho.1.im| < (etaLogHeight rho.1.im)⁻¹ / 4 := by
    simpa only [Complex.sub_im] using (Complex.abs_im_le_norm (z - rho.1)).trans_lt hdist
  apply norm_riemannZeta₁_le_etaLogStrip
  · linarith [(abs_lt.mp hre).1]
  · linarith [(abs_lt.mp hre).2, NontrivialZetaZero.re_lt_one rho]
  · have h := abs_add_le (z.im - rho.1.im) rho.1.im
    rw [sub_add_cancel] at h
    linarith

/-- Schwarz control on the actual logarithmic disc gives a small
value at the point reflected across `Re s = 1`. -/
theorem norm_riemannZeta₁_reflected_across_one_le_etaLog (rho : NontrivialZetaZero)
    (hrho : 1 - (etaLogHeight rho.1.im)⁻¹ / 16 ≤ rho.1.re) :
    ‖riemannZeta₁ (((2 - rho.1.re : ℝ) : ℂ) + I * rho.1.im)‖ ≤
      576 * (|rho.1.im| + 21) * etaLogHeight rho.1.im ^ 3 * (1 - rho.1.re) := by
  have hd : 0 < 1 - rho.1.re := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have he := (etaLogHeight_inv_bounds rho.1.im).1
  have hL : etaLogHeight rho.1.im ≠ 0 := ne_of_gt (by linarith [two_lt_etaLogHeight rho.1.im])
  have hdiff : (((2 - rho.1.re : ℝ) : ℂ) + I * rho.1.im) - rho.1 =
      ((2 * (1 - rho.1.re) : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
    ring
  have hn : ‖(((2 - rho.1.re : ℝ) : ℂ) + I * rho.1.im) - rho.1‖ = 2 * (1 - rho.1.re) := by
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hball : ((2 - rho.1.re : ℝ) : ℂ) + I * rho.1.im ∈
      ball rho.1 ((etaLogHeight rho.1.im)⁻¹ / 4) := by
    rw [mem_ball, dist_eq_norm, hn]
    linarith
  have hmaps : MapsTo riemannZeta₁ (ball rho.1 ((etaLogHeight rho.1.im)⁻¹ / 4))
      (closedBall (riemannZeta₁ rho.1) (72 * (|rho.1.im| + 21) * etaLogHeight rho.1.im ^ 2)) := by
    intro z hz
    simpa only [mem_closedBall, riemannZeta₁_nontrivialZetaZero, dist_zero_right] using
      norm_riemannZeta₁_le_etaLog_zero_ball rho (by linarith) hz
  have h := Complex.dist_le_div_mul_dist_of_mapsTo_ball
    differentiable_riemannZeta₁.differentiableOn hmaps hball
  simp only [riemannZeta₁_nontrivialZetaZero, dist_eq_norm, sub_zero, hn] at h
  refine h.trans_eq ?_
  field_simp
  ring

end

end RiemannGaussian
