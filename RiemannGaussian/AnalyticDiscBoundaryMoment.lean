/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.AnalyticDiscCanonicalControl
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Complex.OpenMapping

/-!
# The complete complex first moment of the boundary logarithm

The canonical residual's logarithmic derivative is exactly the first
complex boundary moment of the original logarithmic modulus. The real
part therefore retains the sign of the angular kernel. Its two
semicircles can use different, oppositely directed arithmetic bounds.
All original zeros and multiplicities remain in the separate exact
canonical divisor sum.
-/

namespace RiemannGaussian.AnalyticDiscBoundaryMoment
noncomputable section
open Complex Filter Metric Set MeromorphicOn
open AnalyticDiscCanonicalBounds AnalyticDiscSignedDerivative
open scoped Topology

/-- The full complex first angular moment of the actual boundary
logarithm, before any component or absolute value is selected. -/
def moment (f : ℂ → ℂ) (R : ℝ) : ℂ :=
  Real.circleAverage (fun z : ℂ ↦ (2 * z / z ^ 2) * (Real.log ‖f z‖ : ℂ)) 0 R

/-- The Herglotz integral retains both harmonic conjugate channels of
the real boundary logarithm. -/
def extension (f : ℂ → ℂ) (R : ℝ) (w : ℂ) : ℂ :=
  Real.circleAverage
    (fun z : ℂ ↦ herglotzRieszKernel 0 w z * (Real.log ‖f z‖ : ℂ)) 0 R

/-- A nonvanishing analytic disc has an integrable actual boundary
logarithm, with no branch choice for the complex logarithm. -/
theorem circleIntegrable_log_norm {f : ℂ → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hne : ∀ z ∈ closedBall 0 R, f z ≠ 0) :
    CircleIntegrable (fun z ↦ Real.log ‖f z‖) 0 R := by
  exact ContinuousOn.circleIntegrable hR
    ((hf.continuousOn.norm.log (fun z hz ↦ norm_ne_zero_iff.mpr (hne z hz))).mono
      sphere_subset_closedBall)

/-- The real part of the Herglotz extension is exactly the interior
logarithmic modulus of every nonvanishing analytic disc function. -/
theorem extension_re {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hne : ∀ z ∈ closedBall 0 R, f z ≠ 0) {w : ℂ} (hw : w ∈ ball 0 R) :
    (extension f R w).re = Real.log ‖f w‖ := by
  have hh : InnerProductSpace.HarmonicOnNhd (fun z ↦ Real.log ‖f z‖) (closedBall 0 R) :=
    fun z hz ↦ (hf z hz).harmonicAt_log_norm (hne z hz)
  simpa only [extension, smul_eq_mul] using
    (re_circleAverage_herglotzRieszKernel_smul
      (circleIntegrable_log_norm (pos_of_mem_ball hw).le hf hne) hw).trans
      (hh.circleAverage_re_herglotzRieszKernel_smul hw)

/-- The entire complex logarithmic derivative equals the first
boundary moment. This keeps its signed real and imaginary channels. -/
theorem logDeriv_eq_moment {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hne : ∀ z ∈ closedBall 0 R, g z ≠ 0) : logDeriv g 0 = moment g R := by
  have hzero : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hcc : CircleIntegrable (fun z ↦ (Real.log ‖g z‖ : ℂ)) 0 R := by
    exact ContinuousOn.circleIntegrable hR.le
      ((Complex.ofRealCLM.continuous.comp_continuousOn
        (hg.continuousOn.norm.log (fun z hz ↦ norm_ne_zero_iff.mpr (hne z hz)))).mono
        sphere_subset_closedBall)
  have hH : HasDerivAt (extension g R) (moment g R) 0 := by
    simpa only [extension, moment, sub_zero, smul_eq_mul] using!
      hasDerivAt_circleAverage_herglotzRieszKernel_smul hcc hzero
  have hHa : AnalyticOnNhd ℂ (extension g R) (ball 0 R) := by
    simpa only [extension, smul_eq_mul] using!
      analyticOnNhd_circleAverage_herglotzRieszKernel_smul hcc
  obtain ⟨L, hL0, hL⟩ := AnalyticDiscLogarithm.exists_logarithm hg hne
  have hLa : AnalyticOnNhd ℂ L (ball 0 R) :=
    (show DifferentiableOn ℂ L (ball 0 R) from
      fun z hz ↦ (hL z hz).differentiableAt.differentiableWithinAt).analyticOnNhd isOpen_ball
  have hLre {z : ℂ} (hz : z ∈ ball 0 R) :
      (L z).re = Real.log ‖g z‖ - Real.log ‖g 0‖ := by
    have he := congrArg norm (AnalyticDiscLogarithm.exp_mul_center hR hg hne hL0 hL hz)
    rw [norm_mul, Complex.norm_exp] at he
    have hl := congrArg Real.log he
    rw [Real.log_mul (Real.exp_ne_zero _) (norm_ne_zero_iff.mpr
      (hne 0 (mem_closedBall_self hR.le))), Real.log_exp] at hl
    linarith
  obtain ⟨c, heq⟩ := (hHa.sub hLa).eq_const_of_re_eq_const
    (c₀ := Real.log ‖g 0‖)
    (fun z hz ↦ by simp only [Pi.sub_apply, Complex.sub_re, extension_re hg hne hz, hLre hz]; ring)
    isOpen_ball (isConnected_ball hR)
  have hevent : (fun z ↦ extension g R z - L z) =ᶠ[𝓝 0] fun _ ↦ c :=
    Filter.eventually_of_mem (ball_mem_nhds 0 hR) heq
  have hzderiv : HasDerivAt (fun z ↦ extension g R z - L z) 0 0 :=
    (hasDerivAt_const 0 c).congr_of_eventuallyEq hevent
  have hd := (hH.sub (hL 0 hzero)).unique hzderiv
  exact (sub_eq_zero.mp hd).symm

/-- The real component retains the signed first angular projection
of the original boundary logarithm, with its exact radius factor. -/
theorem moment_re {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ContinuousOn f (sphere 0 R)) (hne : ∀ z ∈ sphere 0 R, f z ≠ 0) :
    (moment f R).re = 2 / R ^ 2 *
      Real.circleAverage (fun z : ℂ ↦ z.re * Real.log ‖f z‖) 0 R := by
  have hz0 : ∀ z ∈ sphere (0 : ℂ) R, z ≠ 0 := by
    intro z hz he
    subst z
    simp only [mem_sphere, dist_self] at hz
    linarith
  have hk : ContinuousOn (fun z : ℂ ↦ 2 * z / z ^ 2) (sphere 0 R) :=
    (continuous_const.mul continuous_id).continuousOn.div
      (continuous_id.pow 2).continuousOn (fun z hz ↦ pow_ne_zero 2 (hz0 z hz))
  have hl := hf.norm.log (fun z hz ↦ norm_ne_zero_iff.mpr (hne z hz))
  have hp : CircleIntegrable
      (fun z : ℂ ↦ (2 * z / z ^ 2) * (Real.log ‖f z‖ : ℂ)) 0 R :=
    ContinuousOn.circleIntegrable hR.le
      (hk.mul (Complex.ofRealCLM.continuous.comp_continuousOn hl))
  calc
    (moment f R).re = Real.circleAverage
        (fun z : ℂ ↦ ((2 * z / z ^ 2) * (Real.log ‖f z‖ : ℂ)).re) 0 R := by
      exact (Complex.reCLM.circleAverage_comp_comm hp).symm
    _ = Real.circleAverage (fun z : ℂ ↦ (2 / R ^ 2) * (z.re * Real.log ‖f z‖)) 0 R := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      rw [abs_of_pos hR] at hz
      have hn : ‖z‖ = R := by simpa only [mem_sphere, dist_zero_right] using hz
      have he : 2 * z / z ^ 2 = 2 / z := by field_simp
      dsimp only
      rw [he]
      norm_num [Complex.mul_re, Complex.div_re, Complex.normSq_eq_norm_sq, hn]
      ring
    _ = _ := by
      simpa only [smul_eq_mul] using!
        (Real.circleAverage_fun_smul (a := 2 / R ^ 2)
          (f := fun z : ℂ ↦ z.re * Real.log ‖f z‖) (c := 0) (R := R))

/-- Negation keeps the opposite signed angular projection explicitly,
so upper and lower boundary information can be used on different arcs. -/
theorem neg_moment_re {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ContinuousOn f (sphere 0 R)) (hne : ∀ z ∈ sphere 0 R, f z ≠ 0) :
    (-moment f R).re = 2 / R ^ 2 *
      Real.circleAverage (fun z : ℂ ↦ -z.re * Real.log ‖f z‖) 0 R := by
  rw [Complex.neg_re, moment_re hR hf hne]
  have he : Real.circleAverage (fun z : ℂ ↦ -z.re * Real.log ‖f z‖) 0 R =
      -Real.circleAverage (fun z : ℂ ↦ z.re * Real.log ‖f z‖) 0 R := by
    simpa [smul_eq_mul, neg_mul] using!
      (Real.circleAverage_fun_smul (a := (-1 : ℝ))
        (f := fun z : ℂ ↦ z.re * Real.log ‖f z‖) (c := 0) (R := R))
  rw [he]
  ring

/-- Complete canonical zero removal gives the original logarithmic
derivative as its exact complex boundary moment plus the entire signed,
multiplicity-weighted local divisor. -/
theorem logDeriv_eq_moment_add_divisor {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hf0 : f 0 ≠ 0)
    (hs : ∀ z : ℂ, ‖z‖ = R → f z ≠ 0) :
    logDeriv f 0 = moment f R + ∑ᶠ a, divisor f (ball 0 R) a • kernel R a := by
  obtain ⟨g, D⟩ := exists_decomp hR hf hf0
  rw [logDeriv_center_eq hR hf hf0 hs D, logDeriv_eq_moment hR D.analyticOnNhd D.ne_zero]
  congr 1
  unfold moment
  apply Real.circleAverage_congr_sphere
  intro z hz
  rw [abs_of_pos hR] at hz
  dsimp only
  rw [norm_eq_on_sphere hR hf hs D hz]

end
end RiemannGaussian.AnalyticDiscBoundaryMoment
