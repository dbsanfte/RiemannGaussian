/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SechVerticalFourier
import RiemannGaussian.ZetaLogPrimeSeries

/-!
# Coupled prime phases on the actual averaged right boundary

The exact vertical Fourier multiplier is positive at every prime-power
frequency. Absolute domination justifies the complete logarithmic Euler
sum--integral exchange. Common vertical averaging therefore retains the
whole phase kernel, instead of assigning an independent negative-logarithm
penalty to every channel.
-/

namespace RiemannGaussian.ZetaSechPrimeBoundary
noncomputable section
open Complex MeasureTheory Filter
open SechVerticalKernel SechVerticalMoments SechVerticalFourier ZetaLogPrimeSeries

/-- The original signed vertical mean of the actual right-boundary zeta
logarithm, with a common real vertical scale. -/
def mean (σ t b : ℝ) : ℝ :=
  ∫ u : ℝ, density u * Real.log ‖riemannZeta ((σ : ℂ) + I * ((t + b * u : ℝ) : ℂ))‖

/-- Zeta's norm logarithm is continuous on every right-half-plane
vertical parametrization; its divisor and pole are absent there. -/
theorem continuous_log_norm {σ : ℝ} (hσ : 1 < σ) (t b : ℝ) :
    Continuous (fun u : ℝ => Real.log ‖riemannZeta ((σ : ℂ) + I * ((t + b * u : ℝ) : ℂ))‖) := by
  have hpoint (u : ℝ) : ((σ : ℂ) + I * ((t + b * u : ℝ) : ℂ)).re = σ := by simp
  have hc : Continuous (fun u : ℝ => riemannZeta ((σ : ℂ) + I * ((t + b * u : ℝ) : ℂ))) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    apply (differentiableAt_riemannZeta _).continuousAt.comp
      (by fun_prop : ContinuousAt (fun u : ℝ => (σ : ℂ) + I * ((t + b * u : ℝ) : ℂ)) u)
    intro he
    have he := congrArg Complex.re he
    rw [hpoint] at he
    simp only [one_re] at he
    linarith
  exact hc.norm.log (fun u => norm_ne_zero_iff.mpr
    (riemannZeta_ne_zero_of_one_le_re (by rw [hpoint]; linarith)))

/-- The literal signed right-boundary logarithm is absolutely integrable
against the full detector density. -/
theorem integrable_log_norm {σ : ℝ} (hσ : 1 < σ) (t b : ℝ) :
    Integrable (fun u : ℝ => density u *
      Real.log ‖riemannZeta ((σ : ℂ) + I * ((t + b * u : ℝ) : ℂ))‖) := by
  apply (integrable_density.mul_const (Real.log ‖riemannZeta (σ : ℂ)‖)).mono'
    (continuous_density.mul (continuous_log_norm hσ t b)).aestronglyMeasurable
  filter_upwards [] with u
  change ‖density u * Real.log ‖riemannZeta ((σ : ℂ) + I * ((t + b * u : ℝ) : ℂ))‖‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (density_nonneg u)]
  exact mul_le_mul_of_nonneg_left (abs_log_norm_le hσ (t + b * u)) (density_nonneg u)

/-- The original prime-power mass after common vertical averaging. -/
def amplitude (σ b : ℝ) (n : ℕ) : ℝ := weight σ n * attenuation (b * Real.log n)

/-- Every averaged arithmetic amplitude is nonnegative, with no
restriction on the common scale or prime-power frequency. -/
theorem amplitude_nonneg (σ b : ℝ) (n : ℕ) : 0 ≤ amplitude σ b n :=
  mul_nonneg (weight_nonneg σ n) (attenuation_pos _).le

/-- Common averaging cannot enlarge an individual prime-power mass. -/
theorem amplitude_le (σ b : ℝ) (n : ℕ) : amplitude σ b n ≤ weight σ n :=
  mul_le_of_le_one_right (weight_nonneg σ n) (attenuation_le_one _)

/-- The full averaged arithmetic mass remains absolutely summable. -/
theorem summable_amplitude {σ : ℝ} (hσ : 1 < σ) (b : ℝ) : Summable (amplitude σ b) := by
  apply (hasSum_weight hσ).summable.of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (amplitude_nonneg σ b n)]
  exact amplitude_le σ b n

/-- The complete original zeta mean is the prime-power cosine series
with the exact common positive Fourier multiplier. Every exchange is
justified by the full summable arithmetic mass times the actual density. -/
theorem hasSum_mean {σ : ℝ} (hσ : 1 < σ) (t b : ℝ) :
    HasSum (fun n => amplitude σ b n * Real.cos (t * Real.log n)) (mean σ t b) := by
  let F (n : ℕ) (u : ℝ) := density u * (weight σ n * Real.cos ((t + b * u) * Real.log n))
  have h : HasSum (fun n => ∫ u : ℝ, F n u) (mean σ t b) := by
    apply hasSum_integral_of_dominated_convergence (fun n u => density u * weight σ n)
    · intro n
      exact (continuous_density.mul (by fun_prop)).aestronglyMeasurable
    · intro n
      apply ae_of_all
      intro u
      dsimp [F]
      rw [abs_mul, abs_of_nonneg (density_nonneg u), abs_mul,
        abs_of_nonneg (weight_nonneg σ n)]
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right (weight_nonneg σ n) (Real.abs_cos_le_one _)) (density_nonneg u)
    · exact ae_of_all _ (fun u => (hasSum_weight hσ).summable.mul_left (density u))
    · simp_rw [tsum_mul_left, (hasSum_weight hσ).tsum_eq]
      exact integrable_density.mul_const _
    · exact ae_of_all _ (fun u => (hasSum_log_norm hσ (t + b * u)).mul_left (density u))
  apply h.congr_fun
  intro n
  have he : F n = (fun u : ℝ => weight σ n *
      (density u * Real.cos (t * Real.log n + (b * Real.log n) * u))) := by
    funext u
    dsimp [F]
    rw [show (t + b * u) * Real.log n = t * Real.log n + (b * Real.log n) * u by ring]
    ring
  rw [he, integral_const_mul, integral_cos_shift]
  unfold amplitude
  ring

/-- At zero central phase the mean is exactly the complete positive
averaged arithmetic mass. -/
theorem mean_zero_eq {σ : ℝ} (hσ : 1 < σ) (b : ℝ) :
    mean σ 0 b = ∑' n, amplitude σ b n := by
  simpa only [zero_mul, Real.cos_zero, mul_one] using (hasSum_mean hσ 0 b).tsum_eq.symm

/-- The full zero-phase mean is nonnegative. -/
theorem mean_zero_nonneg {σ : ℝ} (hσ : 1 < σ) (b : ℝ) : 0 ≤ mean σ 0 b := by
  rw [mean_zero_eq hσ]
  exact tsum_nonneg (amplitude_nonneg σ b)

/-- The actual zero-phase mean costs no more than the real-axis
logarithm, while its exact smaller value remains available upstream. -/
theorem mean_zero_le {σ : ℝ} (hσ : 1 < σ) (b : ℝ) :
    mean σ 0 b ≤ Real.log ‖riemannZeta (σ : ℂ)‖ := by
  rw [mean_zero_eq hσ, ← (hasSum_weight hσ).tsum_eq]
  exact (summable_amplitude hσ b).tsum_le_tsum (amplitude_le σ b) (hasSum_weight hσ).summable

/-- Every ordinate of the original averaged logarithm is controlled by
the same complete positive zero-phase mass. -/
theorem abs_mean_le {σ : ℝ} (hσ : 1 < σ) (t b : ℝ) : |mean σ t b| ≤ mean σ 0 b := by
  have hs := hasSum_mean hσ t b
  rw [← hs.tsum_eq, mean_zero_eq hσ]
  calc
    _ ≤ ∑' n, ‖amplitude σ b n * Real.cos (t * Real.log n)‖ :=
      norm_tsum_le_tsum_norm hs.summable.norm
    _ ≤ ∑' n, amplitude σ b n := hs.summable.norm.tsum_le_tsum (fun n => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (amplitude_nonneg σ b n)]
      exact mul_le_of_le_one_right (amplitude_nonneg σ b n) (Real.abs_cos_le_one _))
      (summable_amplitude hσ b)

end
end RiemannGaussian.ZetaSechPrimeBoundary
