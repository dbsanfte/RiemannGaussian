/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GammaPhaseApproximation
import RiemannGaussian.ZetaFiniteZeroCount

/-!
# The complete Gamma contribution to the zero-count path

The unwrapped quarter-contour integral of the actual completed Gamma
logarithmic derivative is exactly theta. Cauchy's theorem removes the
horizontal side inside the positive half-plane, without replacing the
continuous phase by a principal argument.
-/

namespace RiemannGaussian.GammaCountingPhase
noncomputable section
open Complex MeasureTheory Set
open scoped Interval

/-- The change of argument along the right vertical segment and then back
to the critical line, for a logarithmic derivative supplied as `f`. -/
def pathPhase (f : ℂ → ℂ) (T : ℝ) : ℝ :=
  (∫ t : ℝ in 0..T, (f ((3 / 2 : ℂ) + t * I)).re) -
    ∫ x : ℝ in (1 / 2 : ℝ)..(3 / 2), (f ((x : ℂ) + T * I)).im

/-- Linearity keeps every boundary contribution, with its integrability
requirements stated for the actual two path segments. -/
theorem pathPhase_add (T : ℝ) {f g : ℂ → ℂ}
    (hfv : IntervalIntegrable (fun t : ℝ => f ((3 / 2 : ℂ) + t * I)) volume 0 T)
    (hfh : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + T * I)) volume (1 / 2 : ℝ) (3 / 2))
    (hgv : IntervalIntegrable (fun t : ℝ => g ((3 / 2 : ℂ) + t * I)) volume 0 T)
    (hgh : IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + T * I)) volume (1 / 2 : ℝ) (3 / 2)) :
    pathPhase (fun s => f s + g s) T = pathPhase f T + pathPhase g T := by
  have hr {a b : ℝ} {k : ℝ → ℂ} (hk : IntervalIntegrable k volume a b) :
      IntervalIntegrable (fun x => (k x).re) volume a b :=
    ⟨Complex.reCLM.integrable_comp hk.1, Complex.reCLM.integrable_comp hk.2⟩
  have hi {a b : ℝ} {k : ℝ → ℂ} (hk : IntervalIntegrable k volume a b) :
      IntervalIntegrable (fun x => (k x).im) volume a b :=
    ⟨Complex.imCLM.integrable_comp hk.1, Complex.imCLM.integrable_comp hk.2⟩
  simp only [pathPhase, add_re, add_im,
    intervalIntegral.integral_add (hr hfv) (hr hgv),
    intervalIntegral.integral_add (hi hfh) (hi hgh)]
  ring

/-- The complete xi count uses this actual quarter-contour change of argument. -/
theorem count_eq_pathPhase {T : ℝ} (hT : 0 ≤ T)
    (hb : ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≠ T) :
    Real.pi * (ZetaFiniteZeroCount.count T : ℝ) = 2 * pathPhase (logDeriv riemannXi) T :=
  ZetaFiniteZeroCount.quarter_contour hT hb

/-- The actual completed Gamma logarithmic derivative is analytic in the
whole positive real half-plane. -/
theorem analytic_gamma {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (logDeriv Complex.Gammaℝ) s := by
  have hA : AnalyticOnNhd ℂ Complex.Gammaℝ {z : ℂ | 0 < z.re} :=
    DifferentiableOn.analyticOnNhd
      (fun z hz => (differentiableAt_Gammaℝ_of_re_pos hz).differentiableWithinAt)
      (isOpen_lt continuous_const Complex.continuous_re)
  simpa only [logDeriv] using (hA s hs).deriv.div (hA s hs) (Gammaℝ_ne_zero_of_re_pos hs)

/-- Every positive vertical Gamma line is genuinely integrable. -/
theorem gamma_vertical_integrable {a : ℝ} (ha : 0 < a) (T : ℝ) :
    IntervalIntegrable (fun t : ℝ => logDeriv Complex.Gammaℝ ((a : ℂ) + t * I)) volume 0 T := by
  apply Continuous.intervalIntegrable
  apply continuous_comp_of_forall_analyticAt _ _ (by fun_prop)
  intro t
  apply analytic_gamma
  simpa using ha

/-- The full horizontal Gamma side is genuinely integrable at every height. -/
theorem gamma_horizontal_integrable (T : ℝ) :
    IntervalIntegrable (fun x : ℝ => logDeriv Complex.Gammaℝ ((x : ℂ) + T * I))
      volume (1 / 2 : ℝ) (3 / 2) := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hx' : 0 < x := by
    rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 3 / 2)] at hx
    linarith [hx.1]
  exact ((analytic_gamma (by simpa using hx')).continuousAt.comp
    (by fun_prop : ContinuousAt (fun x : ℝ => (x : ℂ) + T * I) x)).continuousWithinAt

private theorem gamma_real {x : ℝ} (hx : 0 < x) :
    (logDeriv Complex.Gammaℝ (x : ℂ)).im = 0 := by
  rw [logDeriv_Gammaℝ (by simpa using hx)]
  have hd : (Complex.digamma ((x : ℂ) / 2)).im = 0 := by
    apply Complex.conj_eq_iff_im.mp
    simpa only [map_div₀, Complex.conj_ofReal, Complex.conj_ofNat] using
      (digamma_conj ((x : ℂ) / 2)).symm
  have hl : Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) :=
    (Complex.ofReal_log Real.pi_pos.le).symm
  rw [hl]
  simp [hd]

private theorem gamma_rectangle (T : ℝ) :
    rectangularBoundaryIntegral (1 / 2) (3 / 2) 0 T (logDeriv Complex.Gammaℝ) = 0 := by
  apply rectangularBoundaryIntegral_eq_zero_of_differentiableOn
  intro z hz
  apply (analytic_gamma (s := z) ?_).differentiableAt.differentiableWithinAt
  have hx := hz.1
  norm_num [Complex.Rectangle, uIcc_of_le] at hx
  linarith [hx.1]

/-- Cauchy's theorem keeps the full Gamma phase while eliminating its
horizontal side. No contour winding is discarded. -/
theorem gamma_path_eq_vertical (T : ℝ) :
    pathPhase (logDeriv Complex.Gammaℝ) T =
      ∫ t : ℝ in 0..T, (logDeriv Complex.Gammaℝ ((1 / 2 : ℂ) + t * I)).re := by
  have hi : ∀ {a b : ℝ} {f : ℝ → ℂ}, IntervalIntegrable f volume a b →
      (∫ t : ℝ in a..b, f t).im = ∫ t : ℝ in a..b, (f t).im := by
    intro a b f hf
    simpa only [Complex.imCLM_apply] using
      (Complex.imCLM.intervalIntegral_comp_comm (μ := volume) hf).symm
  have hr : ∀ {a b : ℝ} {f : ℝ → ℂ}, IntervalIntegrable f volume a b →
      (∫ t : ℝ in a..b, f t).re = ∫ t : ℝ in a..b, (f t).re := by
    intro a b f hf
    simpa only [Complex.reCLM_apply] using
      (Complex.reCLM.intervalIntegral_comp_comm (μ := volume) hf).symm
  have hb : (∫ x : ℝ in (1 / 2 : ℝ)..(3 / 2),
      logDeriv Complex.Gammaℝ ((x : ℂ) + (0 : ℝ) * I)).im = 0 := by
    rw [hi (gamma_horizontal_integrable 0)]
    rw [← intervalIntegral.integral_zero (a := (1 / 2 : ℝ)) (b := (3 / 2 : ℝ))]
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : 0 < x := by
      rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 3 / 2)] at hx
      linarith [hx.1]
    simpa using gamma_real hx'
  have he := congrArg Complex.im (gamma_rectangle T)
  unfold rectangularBoundaryIntegral at he
  simp only [sub_im, add_im, I_mul_im, zero_im, hb] at he
  rw [hi (gamma_horizontal_integrable T),
    hr (gamma_vertical_integrable (by norm_num : (0 : ℝ) < 3 / 2) T),
    hr (gamma_vertical_integrable (by norm_num : (0 : ℝ) < 1 / 2) T)] at he
  unfold pathPhase
  push_cast at he
  linarith

/-- The actual completed Gamma contribution is precisely the theta phase
whose finite approximation has a proved uniform error. -/
theorem gamma_path_eq_theta (T : ℝ) :
    pathPhase (logDeriv Complex.Gammaℝ) T = GammaPhaseApproximation.theta T := by
  rw [gamma_path_eq_vertical]
  have hp : ∀ t : ℝ, (logDeriv Complex.Gammaℝ ((1 / 2 : ℂ) + t * I)).re =
      -Real.log Real.pi / 2 + (Complex.digamma ((1 / 4 : ℂ) + (t / 2 : ℝ) * I)).re / 2 := by
    intro t
    rw [logDeriv_Gammaℝ (by norm_num)]
    have hs : ((1 / 2 : ℂ) + t * I) / 2 = (1 / 4 : ℂ) + (t / 2 : ℝ) * I := by
      push_cast
      ring
    rw [hs]
    simp [Complex.log_re, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  simp_rw [hp]
  have hc : IntervalIntegrable (fun t : ℝ =>
      (Complex.digamma ((1 / 4 : ℂ) + (t / 2 : ℝ) * I)).re / 2) volume 0 T := by
    apply Continuous.intervalIntegrable
    apply Continuous.div_const
    apply Complex.continuous_re.comp
    apply continuous_comp_of_forall_analyticAt _ _ (by fun_prop)
    intro t
    apply analyticOnNhd_digamma_re_pos
    norm_num
  rw [intervalIntegral.integral_add intervalIntegrable_const hc,
    intervalIntegral.integral_const, intervalIntegral.integral_div]
  have he : (∫ t : ℝ in 0..T,
      (Complex.digamma ((1 / 4 : ℂ) + (t / 2 : ℝ) * I)).re) =
      2 * GammaPhaseApproximation.phase (1 / 4) (T / 2) := by
    have hh := intervalIntegral.integral_comp_div
      (fun y : ℝ => (Complex.digamma ((1 / 4 : ℂ) + y * I)).re)
      (a := (0 : ℝ)) (b := T) (by norm_num : (2 : ℝ) ≠ 0)
    simpa [GammaPhaseApproximation.phase] using hh
  rw [he]
  simp only [GammaPhaseApproximation.theta, sub_zero, smul_eq_mul]
  ring

end
end RiemannGaussian.GammaCountingPhase
