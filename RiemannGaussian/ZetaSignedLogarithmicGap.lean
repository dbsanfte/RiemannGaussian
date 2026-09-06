import RiemannGaussian.ZetaSignedLocalEstimate
import RiemannGaussian.ZetaSignedPrimeSeries

/-!
# An explicit zero gap from signed prime positivity

The exact three-height prime inequality competes with a selected actual
zero's complete pole contribution. Choosing the real displacement as four
times its distance to one gives a reciprocal-logarithm zero-free margin.
-/

open Complex Filter MeasureTheory MeromorphicOn Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Doubling the ordinate costs at most a factor two in the local
logarithmic height, uniformly down to height zero. -/
theorem localZetaLogHeight_two_mul_le (y : ℝ) :
    localZetaLogHeight (2 * y) ≤ 2 * localZetaLogHeight y := by
  unfold localZetaLogHeight
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    Real.log (2 * |y| + 22) ≤ Real.log ((|y| + 22) ^ 2) :=
      Real.log_le_log (by positivity) (by nlinarith [abs_nonneg y])
    _ = _ := by rw [Real.log_pow]; norm_num

/-- The complete actual multiplicity is constrained by signed prime
positivity and the explicitly bounded local analytic remainder. -/
theorem four_mul_multiplicity_div_gap_le_signedLogHeight (rho : NontrivialZetaZero)
    (hrho : 3 / 4 ≤ rho.1.re) {x : ℝ} (hx : 0 < x) (hxsmall : x ≤ 1 / 28224) :
    4 * (analyticZetaZeroMultiplicity rho : ℝ) / (x + 1 - rho.1.re) ≤
      3 / x + 90000 * localZetaLogHeight rho.1.im * (1 + 1 / |rho.1.im|) := by
  let y := rho.1.im
  have hy : y ≠ 0 := NontrivialZetaZero.im_ne_zero_of_eta_mass rho
  have ht : 0 < |y| := abs_pos.mpr hy
  have hxquarter : x ≤ 1 / 4 := by linarith
  have hprime := neg_logDeriv_riemannZeta_three_height_nonneg (a := 1 + x) (by linarith) y
  have hreal := neg_logDeriv_riemannZeta_real_le hx hxsmall
  have hzero := neg_logDeriv_riemannZeta_re_le_sub_zero rho hrho hx hxquarter
  have hdouble := neg_logDeriv_riemannZeta_re_le (y := 2 * y) (mul_ne_zero (by norm_num) hy) hx hxquarter
  have hdouble' : (-logDeriv riemannZeta (((1 + x : ℝ) : ℂ) + I * ((2 * y : ℝ) : ℂ))).re ≤
      1 / (2 * |y|) + 896 * localZetaLogHeight y := by
    have hL := localZetaLogHeight_two_mul_le y
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hdouble
    linarith
  have herror : 3 * 28224 + 2688 * localZetaLogHeight y + 4 / |y| + 1 / (2 * |y|) ≤
      90000 * localZetaLogHeight y * (1 + 1 / |y|) := by
    have hL := two_lt_localZetaLogHeight y
    have hinv : 0 ≤ 1 / |y| := (one_div_pos.mpr ht).le
    have hp := mul_nonneg (by linarith : 0 ≤ localZetaLogHeight y - 2) hinv
    rw [show 1 / (2 * |y|) = (1 / |y|) / 2 by ring]
    simp only [div_eq_mul_inv] at hinv hp ⊢
    nlinarith
  have he : 4 * (analyticZetaZeroMultiplicity rho : ℝ) / (x + 1 - rho.1.re) ≤
      3 / x + (3 * 28224 + 2688 * localZetaLogHeight y + 4 / |y| + 1 / (2 * |y|)) := by
    dsimp only [y] at hprime hdouble' ⊢
    simp only [Complex.neg_re, div_eq_mul_inv] at hprime hreal hzero hdouble' ⊢
    nlinarith
  exact he.trans (add_le_add le_rfl herror)

/-- At the displacement four times the actual zero gap, signed prime
positivity forces an explicit reciprocal-logarithm distance from one. -/
theorem one_le_signedLogHeight_mul_zero_gap (rho : NontrivialZetaZero)
    (hrho : 1 - 1 / 112896 ≤ rho.1.re) :
    1 ≤ 1800000 * localZetaLogHeight rho.1.im *
      (1 + 1 / |rho.1.im|) * (1 - rho.1.re) := by
  let d : ℝ := 1 - rho.1.re
  have hd : 0 < d := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have hx : 0 < 4 * d := by positivity
  have hxsmall : 4 * d ≤ 1 / 28224 := by dsimp [d]; linarith
  have hsigma : 3 / 4 ≤ rho.1.re := by linarith
  have h := four_mul_multiplicity_div_gap_le_signedLogHeight rho hsigma hx hxsmall
  have hden : 4 * d + 1 - rho.1.re = 5 * d := by dsimp [d]; ring
  rw [hden] at h
  have hm : (1 : ℝ) ≤ analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  have hsingle : 4 / (5 * d) ≤ 3 / (4 * d) +
      90000 * localZetaLogHeight rho.1.im * (1 + 1 / |rho.1.im|) := by
    apply le_trans _ h
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hdiff : 4 / (5 * d) - 3 / (4 * d) = 1 / (20 * d) := by field_simp; ring
  have hbound : 1 / (20 * d) ≤ 90000 * localZetaLogHeight rho.1.im * (1 + 1 / |rho.1.im|) := by
    rw [← hdiff]
    linarith
  have hmul := (div_le_iff₀ (by positivity : 0 < 20 * d)).mp hbound
  dsimp [d] at hmul
  nlinarith

end

end RiemannGaussian
