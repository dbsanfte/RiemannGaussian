/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaSechPrimeBoundary

/-!
# Every phase family retains positivity on the averaged right boundary

Common vertical averaging multiplies each prime-power amplitude by one
positive gamma norm square. The full countable phase kernel therefore
survives both infinite sums and the integral. Removing the constant phase
costs only its actual averaged mass, bounded by the constant coefficient
times the real-axis logarithm. No frequency support or coefficient search
is imposed, and every analytic input is proved for actual zeta.
-/

namespace RiemannGaussian.ZetaSechPhaseFamily
noncomputable section
open Complex MeasureTheory Filter
open SechVerticalKernel SechVerticalMoments ZetaLogPrimeSeries ZetaSechPrimeBoundary

/-- Every summable nonnegative family gives a genuinely convergent sum
of the actual signed vertical zeta means, at arbitrary real frequencies. -/
theorem summable_means {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    {σ : ℝ} (hσ : 1 < σ) (t b : ℝ) :
    Summable (fun n => a n * mean σ (ω n * t) b) := by
  apply (hs.mul_right (mean σ 0 b)).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha n)]
  exact mul_le_mul_of_nonneg_left (abs_mean_le hσ (ω n * t) b) (ha n)

/-- The complete actual boundary sum equals the original phase kernel
against the positively averaged prime-power amplitudes. Joint absolute
summability is proved before interchanging the two infinite sums. -/
theorem hasSum_arithmetic {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    {σ : ℝ} (hσ : 1 < σ) (t b : ℝ) :
    HasSum (fun m => amplitude σ b m * zetaPhaseKernel a ω (t * Real.log m))
      (∑' n, a n * mean σ (ω n * t) b) := by
  let f (m n : ℕ) := a n * amplitude σ b m * Real.cos ((ω n * t) * Real.log m)
  have hmajor := (summable_amplitude hσ b).mul_of_nonneg hs (amplitude_nonneg σ b) ha
  have hdouble : Summable (Function.uncurry f) := by
    apply hmajor.of_norm_bounded
    intro p
    dsimp [f, Function.uncurry]
    rw [abs_mul, abs_of_nonneg (mul_nonneg (ha p.2) (amplitude_nonneg σ b p.1))]
    calc
      _ ≤ a p.2 * amplitude σ b p.1 := mul_le_of_le_one_right
        (mul_nonneg (ha p.2) (amplitude_nonneg σ b p.1)) (Real.abs_cos_le_one _)
      _ = _ := mul_comm _ _
  have he : (∑' m, ∑' n, f m n) = ∑' n, a n * mean σ (ω n * t) b := by
    rw [← hdouble.tsum_comm]
    apply tsum_congr
    intro n
    rw [← (hasSum_mean hσ (ω n * t) b).tsum_eq, ← tsum_mul_left]
    apply tsum_congr
    intro m
    dsimp [f]
    ring
  rw [← he]
  apply hdouble.prod.hasSum.congr_fun
  intro m
  unfold zetaPhaseKernel
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  dsimp [f]
  simp only [mul_assoc]
  ring

/-- Nonnegativity of the original full phase kernel implies a signed
inequality for the actual averaged zeta boundary, for every eligible family. -/
theorem means_nonneg {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hp : ∀ x, 0 ≤ zetaPhaseKernel a ω x) {σ : ℝ} (hσ : 1 < σ) (t b : ℝ) :
    0 ≤ ∑' n, a n * mean σ (ω n * t) b := by
  rw [← (hasSum_arithmetic ha hs hσ t b).tsum_eq]
  exact tsum_nonneg (fun m => mul_nonneg (amplitude_nonneg σ b m) (hp _))

/-- The entire negative right-boundary contribution of all nonconstant
channels costs only the constant channel's exact averaged mass. -/
theorem right_boundary_le_exact {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hp : ∀ x, 0 ≤ zetaPhaseKernel a ω x) (hω0 : ω 0 = 0)
    {σ : ℝ} (hσ : 1 < σ) (t b : ℝ) :
    -(∑' n, if n = 0 then 0 else a n * mean σ (ω n * t) b) ≤ a 0 * mean σ 0 b := by
  have h := means_nonneg ha hs hp hσ t b
  rw [(summable_means ha hs hσ t b).tsum_eq_add_tsum_ite 0, hω0, zero_mul] at h
  linarith

/-- The usual real-axis allowance is paid once with the constant phase
coefficient, rather than independently by the whole nonconstant mass. -/
theorem right_boundary_le {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hp : ∀ x, 0 ≤ zetaPhaseKernel a ω x) (hω0 : ω 0 = 0)
    {σ : ℝ} (hσ : 1 < σ) (t b : ℝ) :
    -(∑' n, if n = 0 then 0 else a n * mean σ (ω n * t) b) ≤
      a 0 * Real.log ‖riemannZeta (σ : ℂ)‖ :=
  (right_boundary_le_exact ha hs hp hω0 hσ t b).trans
    (mul_le_mul_of_nonneg_left (mean_zero_le hσ b) (ha 0))

private theorem summable_logs {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    {σ : ℝ} (hσ : 1 < σ) (t b u : ℝ) :
    Summable (fun n => a n *
      Real.log ‖riemannZeta ((σ : ℂ) + I * ((ω n * t + b * u : ℝ) : ℂ))‖) := by
  apply (hs.mul_right (Real.log ‖riemannZeta (σ : ℂ)‖)).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha n)]
  exact mul_le_mul_of_nonneg_left (abs_log_norm_le hσ (ω n * t + b * u)) (ha n)

/-- The full countable coupled logarithm is genuinely absolutely integrable
against the original density; the common integral is not a totalized
divergent expression. -/
theorem integrable_sum {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    {σ : ℝ} (hσ : 1 < σ) (t b : ℝ) :
    Integrable (fun u : ℝ => density u * ∑' n, a n *
      Real.log ‖riemannZeta ((σ : ℂ) + I * ((ω n * t + b * u : ℝ) : ℂ))‖) := by
  have hm : Measurable (fun u : ℝ => ∑' n, a n *
      Real.log ‖riemannZeta ((σ : ℂ) + I * ((ω n * t + b * u : ℝ) : ℂ))‖) :=
    Measurable.tsum (fun n => (continuous_const.mul (continuous_log_norm hσ (ω n * t) b)).measurable)
  apply (integrable_density.mul_const ((∑' n, a n) * Real.log ‖riemannZeta (σ : ℂ)‖)).mono'
    (continuous_density.measurable.mul hm).aestronglyMeasurable
  filter_upwards [] with u
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (density_nonneg u)]
  apply mul_le_mul_of_nonneg_left _ (density_nonneg u)
  have hf := summable_logs (ω := ω) ha hs hσ t b u
  calc
    _ ≤ ∑' n, ‖a n * Real.log ‖riemannZeta ((σ : ℂ) + I * ((ω n * t + b * u : ℝ) : ℂ))‖‖ :=
      norm_tsum_le_tsum_norm hf.norm
    _ ≤ ∑' n, a n * Real.log ‖riemannZeta (σ : ℂ)‖ := hf.norm.tsum_le_tsum (fun n => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha n)]
      exact mul_le_mul_of_nonneg_left (abs_log_norm_le hσ (ω n * t + b * u)) (ha n))
      (hs.mul_right _)
    _ = _ := tsum_mul_right

/-- The original common integral and the sum of actual channel means
agree exactly. This preserves the common vertical variable until the full
phase kernel has been used, including for infinite support. -/
theorem integral_sum_eq {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    {σ : ℝ} (hσ : 1 < σ) (t b : ℝ) :
    (∫ u : ℝ, density u * ∑' n, a n *
      Real.log ‖riemannZeta ((σ : ℂ) + I * ((ω n * t + b * u : ℝ) : ℂ))‖) =
      ∑' n, a n * mean σ (ω n * t) b := by
  let F (n : ℕ) (u : ℝ) := density u * (a n *
    Real.log ‖riemannZeta ((σ : ℂ) + I * ((ω n * t + b * u : ℝ) : ℂ))‖)
  have h : HasSum (fun n => ∫ u : ℝ, F n u)
      (∫ u : ℝ, density u * ∑' n, a n *
        Real.log ‖riemannZeta ((σ : ℂ) + I * ((ω n * t + b * u : ℝ) : ℂ))‖) := by
    apply hasSum_integral_of_dominated_convergence
      (fun n u => density u * (a n * Real.log ‖riemannZeta (σ : ℂ)‖))
    · intro n
      exact (continuous_density.mul (continuous_const.mul
        (continuous_log_norm hσ (ω n * t) b))).aestronglyMeasurable
    · intro n
      apply ae_of_all
      intro u
      dsimp [F]
      rw [abs_mul, abs_of_nonneg (density_nonneg u), abs_mul, abs_of_nonneg (ha n)]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (abs_log_norm_le hσ (ω n * t + b * u)) (ha n))
        (density_nonneg u)
    · exact ae_of_all _ (fun u => (hs.mul_right _).mul_left (density u))
    · simp_rw [tsum_mul_left, tsum_mul_right]
      exact integrable_density.mul_const _
    · exact ae_of_all _ (fun u => (summable_logs ha hs hσ t b u).hasSum.mul_left (density u))
  rw [← h.tsum_eq]
  apply tsum_congr
  intro n
  rw [show F n = (fun u : ℝ => a n * (density u *
      Real.log ‖riemannZeta ((σ : ℂ) + I * ((ω n * t + b * u : ℝ) : ℂ))‖)) by
      funext u; dsimp [F]; ring, integral_const_mul]
  rfl

/-- The full literal common right-boundary integral is nonnegative
whenever the original phase kernel is nonnegative. -/
theorem integral_sum_nonneg {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hp : ∀ x, 0 ≤ zetaPhaseKernel a ω x) {σ : ℝ} (hσ : 1 < σ) (t b : ℝ) :
    0 ≤ ∫ u : ℝ, density u * ∑' n, a n *
      Real.log ‖riemannZeta ((σ : ℂ) + I * ((ω n * t + b * u : ℝ) : ℂ))‖ := by
  rw [integral_sum_eq ha hs hσ]
  exact means_nonneg ha hs hp hσ t b

private theorem summable_nonconstant {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : Summable a) : Summable (fun n => if n = 0 then 0 else a n) := by
  apply hs.of_norm_bounded
  intro n
  split_ifs
  · simpa only [norm_zero] using ha n
  · rw [Real.norm_eq_abs, abs_of_nonneg (ha n)]

/-- Removing the constant phase still leaves a genuinely absolutely
integrable common right-boundary logarithm, even for infinite support. -/
theorem integrable_nonconstant {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    {σ : ℝ} (hσ : 1 < σ) (t b : ℝ) :
    Integrable (fun u : ℝ => density u * ∑' n, if n = 0 then 0 else a n *
      Real.log ‖riemannZeta ((σ : ℂ) + I * ((ω n * t + b * u : ℝ) : ℂ))‖) := by
  simpa only [ite_mul, zero_mul] using
    integrable_sum (ω := ω) (fun n => by split_ifs; exact le_rfl; exact ha n)
      (summable_nonconstant ha hs) hσ t b

/-- The original single integral of all nonconstant phases is exactly
their sum of means; both infinite operations have been justified. -/
theorem integral_nonconstant_eq {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    {σ : ℝ} (hσ : 1 < σ) (t b : ℝ) :
    (∫ u : ℝ, density u * ∑' n, if n = 0 then 0 else a n *
      Real.log ‖riemannZeta ((σ : ℂ) + I * ((ω n * t + b * u : ℝ) : ℂ))‖) =
      ∑' n, if n = 0 then 0 else a n * mean σ (ω n * t) b := by
  simpa only [ite_mul, zero_mul] using
    integral_sum_eq (ω := ω) (fun n => by split_ifs; exact le_rfl; exact ha n)
      (summable_nonconstant ha hs) hσ t b

/-- The literal negative boundary integral costs only the constant
phase's exact positive averaged mass. No channelwise logarithmic lower
bound is substituted before the common phase cancellation. -/
theorem right_boundary_integral_le_exact {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : Summable a) (hp : ∀ x, 0 ≤ zetaPhaseKernel a ω x) (hω0 : ω 0 = 0)
    {σ : ℝ} (hσ : 1 < σ) (t b : ℝ) :
    -(∫ u : ℝ, density u * ∑' n, if n = 0 then 0 else a n *
      Real.log ‖riemannZeta ((σ : ℂ) + I * ((ω n * t + b * u : ℝ) : ℂ))‖) ≤
      a 0 * mean σ 0 b := by
  rw [integral_nonconstant_eq ha hs hσ]
  exact right_boundary_le_exact ha hs hp hω0 hσ t b

/-- The complete right-boundary integral satisfies the classical
constant-channel allowance for every summable nonnegative phase family
with a nonnegative full kernel, at arbitrary real frequencies. -/
theorem right_boundary_integral_le {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : Summable a) (hp : ∀ x, 0 ≤ zetaPhaseKernel a ω x) (hω0 : ω 0 = 0)
    {σ : ℝ} (hσ : 1 < σ) (t b : ℝ) :
    -(∫ u : ℝ, density u * ∑' n, if n = 0 then 0 else a n *
      Real.log ‖riemannZeta ((σ : ℂ) + I * ((ω n * t + b * u : ℝ) : ℂ))‖) ≤
      a 0 * Real.log ‖riemannZeta (σ : ℂ)‖ := by
  rw [integral_nonconstant_eq ha hs hσ]
  exact right_boundary_le ha hs hp hω0 hσ t b

end
end RiemannGaussian.ZetaSechPhaseFamily
