import RiemannGaussian.ZetaSignedLogarithmicGap

/-!
# Exact pole geometry in the signed prime estimate

The translated local decomposition also controls the real axis, without
the earlier small-disc nonvanishing loss. At nonzero height the pole at
one retains its real Cauchy kernel, gaining a factor of the real shift.
The actual three-height prime inequality consequently gives a quadratic
constraint on the distance of a zero from the strip boundary, with its
full analytic multiplicity retained.
-/

open Complex
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- The real Cauchy contribution of zeta's pole is kept exactly at every height. -/
theorem zetaPole_real_part (x y : ℝ) :
    (1 / ((x : ℂ) + I * y)).re = x / (x ^ 2 + y ^ 2) := by
  simp only [one_div, Complex.inv_re, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.ofReal_im, mul_zero, zero_mul,
    sub_zero, add_zero, Complex.normSq_apply, Complex.add_im, Complex.mul_im,
    Complex.I_im, one_mul, zero_add]
  ring

/-- The full signed local zero sum survives the exact pole evaluation. -/
theorem neg_logDeriv_riemannZeta_re_le_exactPole_sub_poleSum (y : ℝ)
    {x : ℝ} (hx : 0 < x) (hxsmall : x ≤ 1 / 4) :
    (-logDeriv riemannZeta (((1 + x : ℝ) : ℂ) + I * y)).re ≤
      x / (x ^ 2 + y ^ 2) + 448 * localZetaLogHeight y -
        (localZetaPoleSum y ((x - 1 / 2 : ℝ) : ℂ)).re := by
  have hnorm : ‖((x - 1 / 2 : ℝ) : ℂ)‖ ≤ 1 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hrem := norm_localZetaLogRemainder_le y hnorm
  rw [neg_logDeriv_riemannZeta_eq_local y hx hxsmall, Complex.sub_re, Complex.sub_re, zetaPole_real_part]
  linarith [(abs_le.mp (Complex.abs_re_le_norm (localZetaLogRemainder y ((x - 1 / 2 : ℝ) : ℂ)))).1]

/-- The actual real-axis pole estimate has a logarithmic remainder on the whole shift interval. -/
theorem neg_logDeriv_riemannZeta_real_le_local (hx : 0 < x) (hxsmall : x ≤ 1 / 4) :
    (-logDeriv riemannZeta ((1 + x : ℝ) : ℂ)).re ≤ 1 / x + 448 * localZetaLogHeight 0 := by
  have h := neg_logDeriv_riemannZeta_re_le_exactPole_sub_poleSum 0 hx hxsmall
  have hp := localZetaPoleSum_re_nonneg 0 hx
  have he : x / (x ^ 2 + (0 : ℝ) ^ 2) = 1 / x := by field_simp; ring
  simpa only [Complex.ofReal_zero, mul_zero, add_zero, he] using h.trans (sub_le_self _ hp)

/-- Away from ordinate zero the exact pole contribution is at most shift divided by squared height. -/
theorem neg_logDeriv_riemannZeta_re_le_shift_div_sq {y x : ℝ} (hy : y ≠ 0)
    (hx : 0 < x) (hxsmall : x ≤ 1 / 4) :
    (-logDeriv riemannZeta (((1 + x : ℝ) : ℂ) + I * y)).re ≤
      x / y ^ 2 + 448 * localZetaLogHeight y := by
  have h := (neg_logDeriv_riemannZeta_re_le_exactPole_sub_poleSum y hx hxsmall).trans
    (sub_le_self _ (localZetaPoleSum_re_nonneg y hx))
  have hp : x / (x ^ 2 + y ^ 2) ≤ x / y ^ 2 :=
    div_le_div_of_nonneg_left hx.le (sq_pos_of_ne_zero hy) (by nlinarith [sq_nonneg x])
  exact h.trans (add_le_add hp le_rfl)

/-- A selected actual zero keeps its full multiplicity beside the sharpened pole term. -/
theorem neg_logDeriv_riemannZeta_re_le_shift_div_sq_sub_zero (rho : NontrivialZetaZero)
    (hrho : 3 / 4 ≤ rho.1.re) {x : ℝ} (hx : 0 < x) (hxsmall : x ≤ 1 / 4) :
    (-logDeriv riemannZeta (((1 + x : ℝ) : ℂ) + I * rho.1.im)).re ≤
      x / rho.1.im ^ 2 + 448 * localZetaLogHeight rho.1.im -
        (analyticZetaZeroMultiplicity rho : ℝ) / (x + 1 - rho.1.re) := by
  have h := (neg_logDeriv_riemannZeta_re_le_exactPole_sub_poleSum rho.1.im hx hxsmall).trans
    (sub_le_sub_left (multiplicity_div_gap_le_localZetaPoleSum_re rho hrho hx) _)
  have hp : x / (x ^ 2 + rho.1.im ^ 2) ≤ x / rho.1.im ^ 2 := div_le_div_of_nonneg_left hx.le
    (sq_pos_of_ne_zero (NontrivialZetaZero.im_ne_zero_of_eta_mass rho))
      (by nlinarith [sq_nonneg x])
  exact h.trans (sub_le_sub (add_le_add hp le_rfl) le_rfl)

/-- The logarithmic height at zero never exceeds the actual height. -/
theorem localZetaLogHeight_zero_le (y : ℝ) : localZetaLogHeight 0 ≤ localZetaLogHeight y := by
  unfold localZetaLogHeight
  rw [abs_zero, zero_add]
  exact Real.log_le_log (by norm_num) (by linarith [abs_nonneg y])

/-- The actual prime inequality bounds the selected zero using an error linear in shift over squared height. -/
theorem four_mul_multiplicity_div_gap_le_exactPole (rho : NontrivialZetaZero)
    (hrho : 3 / 4 ≤ rho.1.re) {x : ℝ} (hx : 0 < x) (hxsmall : x ≤ 1 / 4) :
    4 * (analyticZetaZeroMultiplicity rho : ℝ) / (x + 1 - rho.1.re) ≤
      3 / x + 448 * (3 * localZetaLogHeight 0 + 4 * localZetaLogHeight rho.1.im +
        localZetaLogHeight (2 * rho.1.im)) + 17 * x / (4 * rho.1.im ^ 2) := by
  have hprime := neg_logDeriv_riemannZeta_three_height_nonneg (a := 1 + x) (by linarith) rho.1.im
  have hreal := neg_logDeriv_riemannZeta_real_le_local hx hxsmall
  have hzero := neg_logDeriv_riemannZeta_re_le_shift_div_sq_sub_zero rho hrho hx hxsmall
  have hdouble := neg_logDeriv_riemannZeta_re_le_shift_div_sq
    (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (NontrivialZetaZero.im_ne_zero_of_eta_mass rho)) hx hxsmall
  have he : x / (2 * rho.1.im) ^ 2 = (x / rho.1.im ^ 2) / 4 := by ring
  rw [he] at hdouble
  simp only [Complex.neg_re, div_eq_mul_inv, mul_inv_rev] at hprime hreal hzero hdouble ⊢
  nlinarith

/-- Keeping the local height error separate yields the explicit improved coefficient 4032. -/
theorem four_mul_multiplicity_div_gap_le_quadraticHeight (rho : NontrivialZetaZero)
    (hrho : 3 / 4 ≤ rho.1.re) {x : ℝ} (hx : 0 < x) (hxsmall : x ≤ 1 / 4) :
    4 * (analyticZetaZeroMultiplicity rho : ℝ) / (x + 1 - rho.1.re) ≤
      3 / x + 4032 * localZetaLogHeight rho.1.im + 17 * x / (4 * rho.1.im ^ 2) := by
  have h := four_mul_multiplicity_div_gap_le_exactPole rho hrho hx hxsmall
  linarith [localZetaLogHeight_zero_le rho.1.im, localZetaLogHeight_two_mul_le rho.1.im]

/-- At six times the actual boundary gap, the complete prime estimate gives a quadratic multiplicity constraint. -/
theorem multiplicity_le_quadratic_signed_zero_gap (rho : NontrivialZetaZero)
    (hrho : 23 / 24 ≤ rho.1.re) :
    8 * (analyticZetaZeroMultiplicity rho : ℝ) - 7 ≤
      56448 * localZetaLogHeight rho.1.im * (1 - rho.1.re) +
        357 * (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 := by
  let d : ℝ := 1 - rho.1.re
  have hd : 0 < d := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have h := four_mul_multiplicity_div_gap_le_quadraticHeight rho (by linarith : 3 / 4 ≤ rho.1.re)
    (by positivity : 0 < 6 * d) (by dsimp [d]; linarith : 6 * d ≤ 1 / 4)
  rw [show 6 * d + 1 - rho.1.re = 7 * d by dsimp [d]; ring] at h
  have hmul := mul_le_mul_of_nonneg_left h (show 0 ≤ 14 * d by positivity)
  have he : 14 * d * (4 * (analyticZetaZeroMultiplicity rho : ℝ) / (7 * d)) =
      8 * (analyticZetaZeroMultiplicity rho : ℝ) := by field_simp; ring
  have hr : 14 * d * (3 / (6 * d) + 4032 * localZetaLogHeight rho.1.im +
      17 * (6 * d) / (4 * rho.1.im ^ 2)) =
        7 + 56448 * localZetaLogHeight rho.1.im * d + 357 * d ^ 2 / rho.1.im ^ 2 := by
    field_simp
    ring
  rw [he, hr] at hmul
  dsimp only [d] at hmul
  linarith

end

end RiemannGaussian
