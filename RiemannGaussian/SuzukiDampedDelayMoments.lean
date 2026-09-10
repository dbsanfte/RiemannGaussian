/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GammaWindowRecovery
import RiemannGaussian.SuzukiControlledRecovery

/-!
# Variable damping of the actual delayed Suzuki moments

The positive delay construction cancels the complete genuine zero window
before changing the damping. A disk centered at any real damping greater
than one half still extends a fixed distance past the central double pole.
Its exact normalized moments have the same positive linear coefficient as
at unit damping, with a uniformly bounded remainder. All time integrals
are those of the literal delayed arithmetic signal.
-/

namespace RiemannGaussian
noncomputable section
open Complex Filter MeasureTheory Metric Set
open scoped Topology

private theorem safe_not_mem_zeroWindow {T : ℝ} {z : ℂ} (hz : 1 / 2 < z.re) :
    z ∉ suzukiChebyshevLaplaceZeroWindow T := by
  intro hm
  obtain ⟨rho, _, hrho⟩ := Finset.mem_image.mp hm
  have hre := NontrivialZetaZero.re_lt_one rho
  rw [← hrho] at hz
  norm_num [suzukiChebyshevLaplaceZeroCoordinate] at hz
  linarith

private theorem ball_subset_slab {d T : ℝ} (hT : d + 1 / 4 ≤ T) :
    closedBall (d : ℂ) (d + 1 / 4) ⊆ suzukiChebyshevLaplaceFiniteSlab T := by
  intro z hz
  have hn : ‖z - (d : ℂ)‖ ≤ d + 1 / 4 := by simpa only [mem_closedBall, dist_eq_norm] using hz
  have hr := (abs_re_le_norm (z - (d : ℂ))).trans hn
  have hi := (abs_im_le_norm (z - (d : ℂ))).trans hn
  simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero] at hr hi
  constructor
  · norm_num [Complex.add_re]
    linarith [(abs_le.mp hr).1]
  · exact hi.trans hT

/-- Every safe real damping retains the full central double-pole source
after exact cancellation of a sufficiently large genuine zero window. -/
theorem exists_suzukiDampedDelayMoment_uniform_error {d T : ℝ}
    (hd : 1 / 2 < d) (hT : d + 1 / 4 ≤ T) (L : List ℂ)
    (hcover : ∀ rho ∈ spectralZetaZeroWindow T,
      suzukiChebyshevLaplaceZeroCoordinate rho ∈ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ‖(d : ℂ) ^ (n + 2) * signedTaylorMoment n (suzukiPositiveDelayResponse L) d -
        ((n + 1 : ℕ) : ℂ) * suzukiChebyshevLogAverageLaplacePoleClearedContinuation 0‖ ≤ C := by
  obtain ⟨Q, hQ, heq⟩ := exists_suzukiPositiveDelay_analyticNumerator
    (by linarith : 0 ≤ T) L hcover
  have hQ0 : Q 0 = suzukiChebyshevLogAverageLaplacePoleClearedContinuation 0 := by
    rw [heq 0, positiveDelayMultiplier_zero, one_mul]
    intro hm
    obtain ⟨rho, _, hrho⟩ := Finset.mem_image.mp hm
    have hn := suzukiChebyshevLaplaceZeroCoordinate_im_ne_zero rho
    apply hn
    rw [hrho]
    rfl
  have hagree : (fun z : ℂ => Q z / (z - 0) ^ 2) =ᶠ[𝓝 (d : ℂ)]
      suzukiPositiveDelayResponse L := by
    have hopen : IsOpen {z : ℂ | 1 / 2 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.eventually_mem hd] with z hz
    have hz0 : z ≠ 0 := by intro he; subst z; norm_num at hz
    rw [heq z (safe_not_mem_zeroWindow hz),
      suzukiChebyshevLogAverageLaplacePoleClearedContinuation_eq_sq_mul_completed hz0]
    unfold suzukiPositiveDelayResponse
    simp only [sub_zero]
    field_simp
  have hnorm : ‖(d : ℂ) - 0‖ < d + 1 / 4 := by
    rw [sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (by linarith : 0 < d))
  obtain ⟨C, hC, hb⟩ := exists_doublePoleMoment_uniform_error
    (hQ.mono (ball_subset_slab hT)) hnorm hd0
  refine ⟨C, hC, fun n => ?_⟩
  have hn := hb n
  rw [signedTaylorMoment_congr n hagree] at hn
  simpa only [sub_zero, hQ0] using hn

private theorem aemeasurable_signal (L : List ℂ) : AEMeasurable (suzukiPositiveDelaySignal L) volume := by
  have h := ((integrable_suzukiPositiveDelaySignal_real_laplace L (x := 1) (by norm_num)).aemeasurable.mul
    Real.continuous_exp.aemeasurable)
  apply h.congr
  filter_upwards with t
  change suzukiPositiveDelaySignal L t * Real.exp (-1 * t) * Real.exp t = _
  rw [mul_assoc, ← Real.exp_add]
  simp

private theorem real_moment_integrable (L : List ℂ) {d : ℝ} (hd : 1 / 2 < d) (n : ℕ) :
    Integrable (fun t : ℝ => suzukiPositiveDelaySignal L t * t ^ n *
      Real.exp (-d * t) / (n.factorial : ℝ)) := by
  have hm := ((signed_real_laplace_moments (aemeasurable_signal L)
    (fun _ hx => integrable_suzukiPositiveDelaySignal_real_laplace L hx) (z := d) hd).2 n).1
  have h := (hm.div_const (n.factorial : ℂ)).re
  apply h.congr
  filter_upwards with t
  have he : ((suzukiPositiveDelaySignal L t * t ^ n * Real.exp (-d * t) /
      (n.factorial : ℝ) : ℝ) : ℂ) =
      ((suzukiPositiveDelaySignal L t : ℂ) * (t : ℂ) ^ n *
        Complex.exp (-(d : ℂ) * (t : ℂ))) / (n.factorial : ℂ) := by
    push_cast
    rfl
  rw [← he]
  rfl

/-- The literal signed moment at an arbitrary real damping. -/
def suzukiDampedDelayGammaMoment (L : List ℂ) (d : ℝ) (n : ℕ) : ℝ :=
  ∫ t : ℝ, suzukiPositiveDelaySignal L t * dampedFactorialGammaKernel d n t

/-- The entire damped moment is absolutely integrable at every safe damping. -/
theorem integrable_suzukiDampedDelayGammaMoment (L : List ℂ) {d : ℝ}
    (hd : 1 / 2 < d) (n : ℕ) :
    Integrable (fun t : ℝ => suzukiPositiveDelaySignal L t * dampedFactorialGammaKernel d n t) := by
  apply ((real_moment_integrable L hd n).const_mul (d ^ (n + 2))).congr
  filter_upwards with t
  rw [dampedFactorialGammaKernel_eq]
  ring

/-- The normalized complex derivative is exactly the complete signed
time integral, before any real-part estimate is used. -/
theorem suzukiDampedDelayGammaMoment_eq_signedTaylorMoment (L : List ℂ) {d : ℝ}
    (hd : 1 / 2 < d) (n : ℕ) :
    (suzukiDampedDelayGammaMoment L d n : ℂ) =
      (d : ℂ) ^ (n + 2) * signedTaylorMoment n (suzukiPositiveDelayResponse L) d := by
  rw [signedTaylorMoment_suzukiPositiveDelayResponse L hd,
    suzukiDampedDelayGammaMoment, ← integral_const_mul, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with t
  rw [dampedFactorialGammaKernel_eq]
  push_cast
  ring

/-- The actual damped gamma moments have the same positive linear source
at every safe damping. The constant controls their full signed error. -/
theorem exists_suzukiDampedDelayGammaMoment_uniform_error {d T : ℝ}
    (hd : 1 / 2 < d) (hT : d + 1 / 4 ≤ T) (L : List ℂ)
    (hcover : ∀ rho ∈ spectralZetaZeroWindow T,
      suzukiChebyshevLaplaceZeroCoordinate rho ∈ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      |suzukiDampedDelayGammaMoment L d n + (n + 1 : ℝ) * suzukiArchimedeanSlopeConstant| ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_suzukiDampedDelayMoment_uniform_error hd hT L hcover
  refine ⟨C, hC, fun n => ?_⟩
  have hn := (abs_re_le_norm _).trans (hb n)
  rw [← suzukiDampedDelayGammaMoment_eq_signedTaylorMoment L hd] at hn
  simpa [Complex.sub_re, Complex.mul_re, suzukiPoleClearedContinuation_zero_re] using hn

/-- A full genuine zero-window delay list discharges the cancellation
conditions at the chosen damping, so its signed moments grow unconditionally. -/
theorem tendsto_suzukiZeroWindowDampedGammaMoment_atTop {d T : ℝ}
    (hd : 1 / 2 < d) (hT : d + 1 / 4 ≤ T) :
    Tendsto (suzukiDampedDelayGammaMoment (suzukiZeroWindowDelayNodes T) d) atTop atTop := by
  obtain ⟨C, _, hC⟩ := exists_suzukiDampedDelayGammaMoment_uniform_error hd hT
    (suzukiZeroWindowDelayNodes T) (fun rho hrho => by
      apply Finset.mem_toList.mpr
      exact Finset.mem_image.mpr ⟨rho, hrho, rfl⟩)
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hl := tendsto_atTop_add_const_right atTop (-C)
    (hn.const_mul_atTop (neg_pos.mpr suzukiArchimedeanSlopeConstant_neg))
  apply tendsto_atTop_mono _ hl
  intro n
  have h := (abs_le.mp (hC n)).1
  nlinarith

end
end RiemannGaussian
