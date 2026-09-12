/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaEulerCell
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# A phase-preserving primitive for oscillatory powers

For `exp(i*w*x)*x^r`, division by `i*w*x+r` retains the linear and
logarithmic phases together. Its exact derivative leaves a defect with
two powers of that denominator. Separation of the two frequencies
therefore controls the defect before discarding the original phase.
-/

namespace RiemannGaussian.OscillatoryPowerPrimitive
noncomputable section
open Complex MeasureTheory Set
open scoped Interval

/-- The original coupled linear and logarithmic complex phase. -/
def mode (r : ℂ) (w x : ℝ) : ℂ := exp (I * w * x) * (x : ℂ) ^ r

/-- The full complex phase derivative multiplied by the coordinate. -/
def denominator (r : ℂ) (w x : ℝ) : ℂ := I * w * x + r

/-- The approximate primitive retains the actual complex denominator. -/
def primitive (r : ℂ) (w x : ℝ) : ℂ :=
  exp (I * w * x) * (x : ℂ) ^ (r + 1) / denominator r w x

private theorem power_deriv (r : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ ↦ (y : ℂ) ^ r) (r * (x : ℂ) ^ (r - 1)) x := by
  by_cases hr : r = 0
  · subst r
    simpa using hasDerivAt_const x (1 : ℂ)
  · exact hasDerivAt_ofReal_cpow_const hx.ne' hr

/-- The exact derivative separates the original phase from a defect
with the square of its full complex phase denominator. -/
theorem hasDerivAt_primitive (r : ℂ) (w : ℝ) {x : ℝ} (hx : 0 < x)
    (hd : denominator r w x ≠ 0) :
    HasDerivAt (primitive r w)
      (mode r w x + r * mode r w x / denominator r w x ^ 2) x := by
  have he := (((hasDerivAt_id x).ofReal_comp).const_mul (I * w)).cexp
  have hp := power_deriv (r + 1) hx
  have hl := (((hasDerivAt_id x).ofReal_comp).const_mul (I * w)).add_const r
  apply ((he.mul hp).div hl hd).congr_deriv
  dsimp
  rw [show r + 1 - 1 = r by ring]
  rw [cpow_add r 1 (Complex.ofReal_ne_zero.mpr hx.ne'), cpow_one]
  unfold mode denominator
  unfold denominator at hd
  field_simp [hd]
  ring

/-- The original phase has exactly its real power amplitude. -/
theorem norm_mode (r : ℂ) (w : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖mode r w x‖ = x ^ r.re := by
  unfold mode
  rw [norm_mul, Complex.norm_exp, norm_cpow_eq_rpow_re_of_pos hx]
  simp

/-- Separation from the logarithmic frequency gives a quantitative
lower bound for the original complex denominator, including either sign
of the linear frequency. -/
theorem denominator_lower (r : ℂ) (w : ℝ) {x : ℝ} (hx : 0 ≤ x)
    (hsep : 2 * |r.im| ≤ |w| * x) :
    |w| * x / 2 ≤ ‖denominator r w x‖ := by
  have hi : (denominator r w x).im = w * x + r.im := by simp [denominator]
  have ht : |w| * x ≤ |w * x + r.im| + |r.im| := by
    have h := abs_add_le (w * x + r.im) (-r.im)
    simpa only [add_neg_cancel_right, abs_neg, abs_mul, abs_of_nonneg hx] using h
  have hn := abs_im_le_norm (denominator r w x)
  rw [hi] at hn
  linarith

/-- Frequency separation discharges the denominator's nonvanishing
hypothesis on the actual positive coordinate. -/
theorem denominator_ne_zero (r : ℂ) {w x : ℝ} (hw : w ≠ 0) (hx : 0 < x)
    (hsep : 2 * |r.im| ≤ |w| * x) : denominator r w x ≠ 0 := by
  apply norm_pos_iff.mp
  exact (by positivity : 0 < |w| * x / 2).trans_le (denominator_lower r w hx.le hsep)

/-- The original primitive is smaller by one separated frequency;
its logarithmic phase has not been differentiated in isolation. -/
theorem norm_primitive_le (r : ℂ) {w x : ℝ} (hw : w ≠ 0) (hx : 0 < x)
    (hsep : 2 * |r.im| ≤ |w| * x) :
    ‖primitive r w x‖ ≤ 2 / |w| * x ^ r.re := by
  have hd := denominator_lower r w hx.le hsep
  have hn : ‖exp (I * w * x) * (x : ℂ) ^ (r + 1)‖ = x ^ (r.re + 1) := by
    simpa only [mode, add_re, one_re] using norm_mode (r + 1) w hx
  unfold primitive
  rw [norm_div, hn]
  apply (div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _) (by positivity) hd).trans_eq
  rw [Real.rpow_add hx, Real.rpow_one]
  field_simp

/-- The exact derivative defect has two separated frequency powers
and two additional powers of the coordinate in its envelope. -/
theorem norm_defect_le (r : ℂ) {w x : ℝ} (hw : w ≠ 0) (hx : 0 < x)
    (hsep : 2 * |r.im| ≤ |w| * x) :
    ‖r * mode r w x / denominator r w x ^ 2‖ ≤
      4 * ‖r‖ / |w| ^ 2 * x ^ (r.re - 2) := by
  have hd := denominator_lower r w hx.le hsep
  rw [norm_div, norm_mul, norm_pow, norm_mode r w hx]
  apply (div_le_div_of_nonneg_left (by positivity) (by positivity)
    (pow_le_pow_left₀ (by positivity) hd 2)).trans_eq
  rw [Real.rpow_sub hx, Real.rpow_two]
  field_simp
  ring

private theorem mode_continuousOn (r : ℂ) (w : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (mode r w) [[a, b]] := by
  unfold mode
  apply ContinuousOn.mul (by fun_prop)
  apply ContinuousOn.cpow_const continuous_ofReal.continuousOn
  intro x hx
  rw [uIcc_of_le hab] at hx
  exact ofReal_mem_slitPlane.mpr (ha.trans_le hx.1)

/-- The full complex mode is genuinely integrable on every positive
compact interval, before any frequency separation is needed. -/
theorem intervalIntegrable_mode (r : ℂ) (w : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (mode r w) volume a b :=
  (mode_continuousOn r w ha hab).intervalIntegrable

/-- On a separated positive interval, the integral is exactly the two
complex primitive endpoints minus the original coupled defect integral. -/
theorem integral_eq (r : ℂ) {w a b : ℝ} (hw : w ≠ 0) (ha : 0 < a) (hab : a ≤ b)
    (hsep : 2 * |r.im| ≤ |w| * a) :
    (∫ x : ℝ in a..b, mode r w x) = primitive r w b - primitive r w a -
      ∫ x : ℝ in a..b, r * mode r w x / denominator r w x ^ 2 := by
  have hs {x : ℝ} (hx : x ∈ [[a, b]]) :
      0 < x ∧ 2 * |r.im| ≤ |w| * x := by
    rw [uIcc_of_le hab] at hx
    exact ⟨ha.trans_le hx.1, hsep.trans (mul_le_mul_of_nonneg_left hx.1 (abs_nonneg w))⟩
  have hm : IntervalIntegrable (mode r w) volume a b :=
    (mode_continuousOn r w ha hab).intervalIntegrable
  have hd : IntervalIntegrable (fun x ↦ r * mode r w x / denominator r w x ^ 2)
      volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (continuousOn_const.mul (mode_continuousOn r w ha hab))
      (by unfold denominator; fun_prop)
    exact fun x hx ↦ pow_ne_zero 2 (denominator_ne_zero r hw (hs hx).1 (hs hx).2)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx ↦ hasDerivAt_primitive r w (hs hx).1
      (denominator_ne_zero r hw (hs hx).1 (hs hx).2)) (hm.add hd)
  rw [intervalIntegral.integral_add hm hd] at h
  exact eq_sub_of_add_eq h

/-- The genuine oscillatory integral is controlled by its separated
endpoint amplitudes and the faster-decaying defect envelope. -/
theorem norm_integral_le (r : ℂ) {w a b : ℝ} (hw : w ≠ 0) (ha : 0 < a) (hab : a ≤ b)
    (hsep : 2 * |r.im| ≤ |w| * a) :
    ‖∫ x : ℝ in a..b, mode r w x‖ ≤
      2 / |w| * (a ^ r.re + b ^ r.re) +
        (4 * ‖r‖ / |w| ^ 2) * ∫ x : ℝ in a..b, x ^ (r.re - 2) := by
  have hs {x : ℝ} (hx : x ∈ [[a, b]]) :
      0 < x ∧ 2 * |r.im| ≤ |w| * x := by
    rw [uIcc_of_le hab] at hx
    exact ⟨ha.trans_le hx.1, hsep.trans (mul_le_mul_of_nonneg_left hx.1 (abs_nonneg w))⟩
  have hi : IntervalIntegrable (fun x : ℝ ↦ x ^ (r.re - 2)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_id.rpow_const
    exact fun x hx ↦ Or.inl (hs hx).1.ne'
  have hd : ‖∫ x : ℝ in a..b, r * mode r w x / denominator r w x ^ 2‖ ≤
      (4 * ‖r‖ / |w| ^ 2) * ∫ x : ℝ in a..b, x ^ (r.re - 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.norm_integral_le_of_norm_le hab
    · apply Filter.Eventually.of_forall
      intro x hx
      exact norm_defect_le r hw (ha.trans hx.1)
        (hsep.trans (mul_le_mul_of_nonneg_left hx.1.le (abs_nonneg w)))
    · exact hi.const_mul _
  rw [integral_eq r hw ha hab hsep]
  have hb := norm_primitive_le r hw (ha.trans_le hab)
    (hsep.trans (mul_le_mul_of_nonneg_left hab (abs_nonneg w)))
  have hna := norm_primitive_le r hw ha hsep
  apply (norm_sub_le _ _).trans
  have he := (norm_sub_le (primitive r w b) (primitive r w a)).trans (add_le_add hb hna)
  exact (add_le_add he hd).trans_eq (by ring)

/-- A cosine channel retains both oppositely oriented complex modes. -/
theorem cosine_eq_modes (r : ℂ) (w x : ℝ) :
    (Real.cos (w * x) : ℂ) * (x : ℂ) ^ r = (mode r w x + mode r (-w) x) / 2 := by
  rw [ofReal_cos, Complex.cos]
  unfold mode
  push_cast
  ring_nf

/-- The complete cosine channel satisfies the same separated-frequency
estimate after retaining and integrating both complex orientations. -/
theorem norm_cosine_integral_le (r : ℂ) {w a b : ℝ} (hw : w ≠ 0)
    (ha : 0 < a) (hab : a ≤ b) (hsep : 2 * |r.im| ≤ |w| * a) :
    ‖∫ x : ℝ in a..b, (Real.cos (w * x) : ℂ) * (x : ℂ) ^ r‖ ≤
      2 / |w| * (a ^ r.re + b ^ r.re) +
        (4 * ‖r‖ / |w| ^ 2) * ∫ x : ℝ in a..b, x ^ (r.re - 2) := by
  have hi := intervalIntegrable_mode r w ha hab
  have hj := intervalIntegrable_mode r (-w) ha hab
  simp_rw [cosine_eq_modes]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add hi hj, norm_div]
  have hp := norm_integral_le r hw ha hab hsep
  have hn := norm_integral_le r (neg_ne_zero.mpr hw) ha hab
    (show 2 * |r.im| ≤ |-w| * a by simpa only [abs_neg] using hsep)
  simp only [abs_neg] at hn
  norm_num only [norm_ofNat]
  have h := (norm_add_le (∫ x : ℝ in a..b, mode r w x)
    (∫ x : ℝ in a..b, mode r (-w) x)).trans (add_le_add hp hn)
  linarith

end
end RiemannGaussian.OscillatoryPowerPrimitive
