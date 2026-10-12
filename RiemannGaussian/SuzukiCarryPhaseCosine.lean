/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarryPhaseInjectivity
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! Compact-coordinate cosine transforms and exact contrast derivatives. -/

namespace RiemannGaussian.SuzukiCarryPhaseCosine
noncomputable section
open Complex MeasureTheory Set Filter Metric
open scoped BigOperators Topology

/-- Exponential transform of a density in a bounded real coordinate. -/
def exponentialResponse (X : ℝ → ℝ) (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (z*X t)*f t

theorem norm_exp_coordinate_le {X : ℝ → ℝ} (hX : ∀ t, 0 ≤ X t ∧ X t ≤ 2)
    (z : ℂ) (t : ℝ) : ‖Complex.exp (z*X t)‖ ≤ Real.exp (2*‖z‖) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  calc
    z.re*X t ≤ ‖z‖*X t := mul_le_mul_of_nonneg_right (Complex.re_le_norm z) (hX t).1
    _ ≤ 2*‖z‖ := by nlinarith [(hX t).2, norm_nonneg z]

theorem integrable_exponentialResponse {X : ℝ → ℝ} (mX : Measurable X)
    (hX : ∀ t, 0 ≤ X t ∧ X t ≤ 2) {f : ℝ → ℂ} (mf : Measurable f) (hi : Integrable f)
    (z : ℂ) : Integrable (fun t => Complex.exp (z*X t)*f t) := by
  apply (hi.norm.const_mul (Real.exp (2*‖z‖))).mono' (by fun_prop)
  filter_upwards with t
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_exp_coordinate_le hX z t) (norm_nonneg _)

theorem analytic_exponentialResponse {X : ℝ → ℝ} (mX : Measurable X)
    (hX : ∀ t, 0 ≤ X t ∧ X t ≤ 2) {f : ℝ → ℂ} (mf : Measurable f) (hi : Integrable f) :
    AnalyticOnNhd ℂ (exponentialResponse X f) univ := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_univ
  intro z _
  let F : ℂ → ℝ → ℂ := fun z t => Complex.exp (z*X t)*f t
  let F' : ℂ → ℝ → ℂ := fun z t => (X t : ℂ)*Complex.exp (z*X t)*f t
  have hdiff (w : ℂ) (t : ℝ) : HasDerivAt (fun z => F z t) (F' w t) w := by
    have hd := (((hasDerivAt_id w).mul_const (X t : ℂ)).cexp).mul_const (f t)
    convert! hd using 1
    try dsimp [F, F']
    ring
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun t => 2*Real.exp (2*(‖z‖+1))*‖f t‖)
    (ball_mem_nhds z (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall (fun _ => by dsimp [F]; fun_prop))
    (integrable_exponentialResponse mX hX mf hi z)
    (by dsimp [F']; fun_prop) ?_
    (hi.norm.const_mul _) (Eventually.of_forall fun t w _ => hdiff w t)
  · exact hd.2.differentiableAt.differentiableWithinAt
  · filter_upwards with t
    intro w hw
    have hw' : ‖w‖ ≤ ‖z‖+1 := by
      have hb : ‖w-z‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hw
      have hh := norm_add_le (w-z) z
      rw [sub_add_cancel] at hh
      linarith
    dsimp [F']
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hX t).1]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact mul_le_mul (hX t).2
      ((norm_exp_coordinate_le hX w t).trans (Real.exp_le_exp.mpr (by linarith)))
      (norm_nonneg _) (by norm_num)

/-- Entire cosine transform of a density in a bounded real coordinate. -/
def cosineResponse (X : ℝ → ℝ) (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  (exponentialResponse X f (I*z)+exponentialResponse X f (-I*z))/2

theorem analytic_cosineResponse {X : ℝ → ℝ} (mX : Measurable X)
    (hX : ∀ t, 0 ≤ X t ∧ X t ≤ 2) {f : ℝ → ℂ} (mf : Measurable f) (hi : Integrable f) :
    AnalyticOnNhd ℂ (cosineResponse X f) univ := by
  intro z _
  unfold cosineResponse
  have hp : AnalyticAt ℂ (fun w : ℂ => I*w) z := by fun_prop
  have hn : AnalyticAt ℂ (fun w : ℂ => -I*w) z := by fun_prop
  exact (((analytic_exponentialResponse mX hX mf hi (I*z) (mem_univ _)).comp
    (f := fun w => I*w) hp).add
      ((analytic_exponentialResponse mX hX mf hi (-I*z) (mem_univ _)).comp
        (f := fun w => -I*w) hn)).div_const

theorem cosineResponse_real {X : ℝ → ℝ} (mX : Measurable X)
    (hX : ∀ t, 0 ≤ X t ∧ X t ≤ 2) {f : ℝ → ℂ} (mf : Measurable f) (hi : Integrable f)
    (tau : ℝ) : cosineResponse X f tau =
      ∫ t : ℝ, (Real.cos (tau*X t) : ℂ)*f t := by
  unfold cosineResponse exponentialResponse
  rw [← integral_add (integrable_exponentialResponse mX hX mf hi (I*tau))
    (integrable_exponentialResponse mX hX mf hi (-I*tau)), ← integral_div]
  apply integral_congr_ae
  filter_upwards with t
  have he : Complex.exp (I*tau*X t)+Complex.exp (-I*tau*X t) =
      2*(Real.cos (tau*X t) : ℂ) := by
    rw [show I*(tau : ℂ)*X t = ((tau*X t : ℝ) : ℂ)*I by push_cast; ring,
      show -I*(tau : ℂ)*X t = ((-(tau*X t) : ℝ) : ℂ)*I by push_cast; ring,
      Complex.exp_mul_I, Complex.exp_mul_I]
    simp [Complex.ofReal_mul]
    ring
  rw [← add_mul, he]
  ring

/-- Twice-integrated cosine contrast retaining the coordinate denominator. -/
def contrastResponse (X : ℝ → ℝ) (f : ℝ → ℂ) (tau : ℝ) : ℂ :=
  ∫ t : ℝ, ((Real.cos (tau*X t)-1)/(X t)^2 : ℝ)*f t

/-- First derivative of the twice-integrated cosine contrast. -/
def sineResponse (X : ℝ → ℝ) (f : ℝ → ℂ) (tau : ℝ) : ℂ :=
  ∫ t : ℝ, (-Real.sin (tau*X t)/X t : ℝ)*f t

theorem contrastScalar_bound {v : ℝ} (hv : 0 < v) (tau : ℝ) :
    |(Real.cos (tau*v)-1)/v^2| ≤ tau^2/2 := by
  rw [abs_div, abs_of_nonneg (show 0 ≤ v^2 from sq_nonneg v)]
  apply (div_le_iff₀ (sq_pos_of_pos hv)).mpr
  rw [abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one _))]
  nlinarith [Real.one_sub_sq_div_two_le_cos (x := tau*v)]

theorem sineScalar_bound {v : ℝ} (hv : 0 < v) (tau : ℝ) :
    |-Real.sin (tau*v)/v| ≤ |tau| := by
  rw [abs_div, abs_neg, abs_of_pos hv]
  apply (div_le_iff₀ hv).mpr
  simpa only [abs_mul, abs_of_pos hv] using (Real.abs_sin_le_abs (x := tau*v))

theorem integrable_contrast {X : ℝ → ℝ} (mX : Measurable X) (hX : ∀ t, 0 < X t)
    {f : ℝ → ℂ} (mf : Measurable f) (hi : Integrable f) (tau : ℝ) :
    Integrable (fun t : ℝ => ((Real.cos (tau*X t)-1)/(X t)^2 : ℝ)*f t) := by
  apply (hi.norm.const_mul (tau^2/2)).mono' (by fun_prop)
  filter_upwards with t
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (contrastScalar_bound (hX t) tau) (norm_nonneg _)

theorem integrable_sine {X : ℝ → ℝ} (mX : Measurable X) (hX : ∀ t, 0 < X t)
    {f : ℝ → ℂ} (mf : Measurable f) (hi : Integrable f) (tau : ℝ) :
    Integrable (fun t : ℝ => (-Real.sin (tau*X t)/X t : ℝ)*f t) := by
  apply (hi.norm.const_mul |tau|).mono' (by fun_prop)
  filter_upwards with t
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (sineScalar_bound (hX t) tau) (norm_nonneg _)

theorem hasDerivAt_contrast {X : ℝ → ℝ} (mX : Measurable X) (hX : ∀ t, 0 < X t)
    {f : ℝ → ℂ} (mf : Measurable f) (hi : Integrable f) (tau : ℝ) :
    HasDerivAt (contrastResponse X f) (sineResponse X f tau) tau := by
  let F : ℝ → ℝ → ℂ := fun tau t => ((Real.cos (tau*X t)-1)/(X t)^2 : ℝ)*f t
  let F' : ℝ → ℝ → ℂ := fun tau t => (-Real.sin (tau*X t)/X t : ℝ)*f t
  have hdiff (w t : ℝ) : HasDerivAt (fun tau => F tau t) (F' w t) w := by
    have hd := ((((Real.hasDerivAt_cos (w*X t)).comp w
      ((hasDerivAt_id w).mul_const (X t))).sub_const 1).div_const ((X t)^2)).ofReal_comp.mul_const (f t)
    convert! hd using 1
    try dsimp [F, F']
    push_cast
    field_simp [ne_of_gt (hX t)]
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun t => (|tau|+1)*‖f t‖)
    (ball_mem_nhds tau (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall fun _ => by dsimp [F]; fun_prop)
    (integrable_contrast mX hX mf hi tau) (by dsimp [F']; fun_prop) ?_
    (hi.norm.const_mul _) (Eventually.of_forall fun t w _ => hdiff w t)
  · exact hd.2
  · filter_upwards with t
    intro w hw
    have hw' : |w| ≤ |tau|+1 := by
      have hb : |w-tau| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using hw
      have hh := abs_add_le (w-tau) tau
      rw [sub_add_cancel] at hh
      linarith
    dsimp [F']
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right ((sineScalar_bound (hX t) w).trans hw') (norm_nonneg _)

theorem hasDerivAt_sine {X : ℝ → ℝ} (mX : Measurable X) (hX : ∀ t, 0 < X t)
    {f : ℝ → ℂ} (mf : Measurable f) (hi : Integrable f) (tau : ℝ) :
    HasDerivAt (sineResponse X f) (-∫ t : ℝ, (Real.cos (tau*X t) : ℂ)*f t) tau := by
  let F : ℝ → ℝ → ℂ := fun tau t => (-Real.sin (tau*X t)/X t : ℝ)*f t
  let F' : ℝ → ℝ → ℂ := fun tau t => (-Real.cos (tau*X t) : ℝ)*f t
  have hdiff (w t : ℝ) : HasDerivAt (fun tau => F tau t) (F' w t) w := by
    have hd := (((Real.hasDerivAt_sin (w*X t)).comp w
      ((hasDerivAt_id w).mul_const (X t))).neg.div_const (X t)).ofReal_comp.mul_const (f t)
    convert! hd using 1
    try dsimp [F, F']
    push_cast
    field_simp [ne_of_gt (hX t)]
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun t => ‖f t‖)
    (univ_mem : (univ : Set ℝ) ∈ 𝓝 tau)
    (Eventually.of_forall fun _ => by dsimp [F]; fun_prop)
    (integrable_sine mX hX mf hi tau) (by dsimp [F']; fun_prop) ?_ hi.norm
    (Eventually.of_forall fun t w _ => hdiff w t)
  · convert! hd.2 using 1
    simp only [F', Complex.ofReal_neg, neg_mul, integral_neg]
  · filter_upwards with t
    intro w _
    dsimp [F']
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)

end
end RiemannGaussian.SuzukiCarryPhaseCosine
