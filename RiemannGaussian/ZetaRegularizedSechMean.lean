/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RationalVerticalCorrection
import RiemannGaussian.ZetaSechPhaseFamily
import RiemannGaussian.ZetaAngularPhaseAllowance
import RiemannGaussian.ZetaStripDisc

/-!
# The full coupled right boundary after actual pole clearing

The signed logarithm of the actual regularized zeta is split exactly into
the original zeta logarithm and its rational profile. All integral and
countable-family exchanges are justified. The prime phases therefore
still charge only the constant channel, while the complete rational mass
is retained before its uniform decaying estimate is applied.
-/

namespace RiemannGaussian.ZetaRegularizedSechMean
noncomputable section
open Complex MeasureTheory
open ZetaGaussianLocalizer SechVerticalKernel SechVerticalMoments ZetaAngularPhaseAllowance

/-- The exact signed logarithm after pole clearing on the Euler half-plane. -/
theorem log_regularized_eq {s : ℂ} (hs : 1 < s.re) :
    Real.log ‖regularized s‖ = Real.log ‖riemannZeta s‖ - RationalVerticalCorrection.profile s.re s.im := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  have hm : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hp : s + 1 ≠ 0 := add_one_ne_zero (by linarith)
  have hg := ZetaStripDisc.regularized_ne_zero hs.le
  have he : riemannZeta s = (s + 1) / (s - 1) * regularized s := by
    rw [regularized_eq hs1]
    field_simp
  have h := congrArg (fun z : ℂ => Real.log ‖z‖) he
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (div_ne_zero hp hm)) (norm_ne_zero_iff.mpr hg),
    ← RationalVerticalCorrection.profile_eq_log_ratio hs.ne'] at h
  linarith

/-- The same exact logarithm identity in the original vertical coordinates. -/
theorem log_regularized_vertical {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    Real.log ‖regularized ((σ : ℂ) + I * (y : ℂ))‖ =
      Real.log ‖riemannZeta ((σ : ℂ) + I * (y : ℂ))‖ - RationalVerticalCorrection.profile σ y := by
  have h := log_regularized_eq (s := (σ : ℂ) + I * (y : ℂ)) (by simpa using hσ)
  simpa using h

/-- The complete signed mean of the actual pole-cleared right logarithm. -/
def mean (σ t b : ℝ) : ℝ :=
  ∫ u : ℝ, density u * Real.log ‖regularized ((σ : ℂ) + I * ((t + b * u : ℝ) : ℂ))‖

/-- The right regularized logarithm has a genuine full signed integral. -/
theorem integrable_log_norm {σ : ℝ} (hσ : 1 < σ) (t b : ℝ) :
    Integrable (fun u : ℝ => density u *
      Real.log ‖regularized ((σ : ℂ) + I * ((t + b * u : ℝ) : ℂ))‖) := by
  have h := (ZetaSechPrimeBoundary.integrable_log_norm hσ t b).sub
    (RationalVerticalCorrection.integrable_profile (by linarith) hσ.ne' t b)
  convert! h using 1
  ext u
  simp only [Pi.sub_apply, log_regularized_vertical hσ, mul_sub]

/-- The original zeta mean and the full rational mass recover the actual
right-boundary mean exactly, before either receives an estimate. -/
theorem mean_eq {σ : ℝ} (hσ : 1 < σ) (t b : ℝ) :
    mean σ t b = ZetaSechPrimeBoundary.mean σ t b - RationalVerticalCorrection.mass σ t b := by
  unfold mean
  simp_rw [log_regularized_vertical hσ, mul_sub]
  rw [integral_sub (ZetaSechPrimeBoundary.integrable_log_norm hσ t b)
    (RationalVerticalCorrection.integrable_profile (by linarith) hσ.ne' t b)]
  rfl

/-- A height-independent bound supplies summability of the actual signed
right means without being substituted for their coupled arithmetic value. -/
theorem abs_mean_le {σ : ℝ} (hσ : 1 < σ) (t b : ℝ) :
    |mean σ t b| ≤ ZetaSechPrimeBoundary.mean σ 0 b + RationalVerticalCorrection.profile σ 0 := by
  rw [mean_eq hσ]
  have h := abs_sub (ZetaSechPrimeBoundary.mean σ t b) (RationalVerticalCorrection.mass σ t b)
  rw [abs_of_nonneg (RationalVerticalCorrection.mass_nonneg (by linarith) hσ.ne' t b)] at h
  linarith [ZetaSechPrimeBoundary.abs_mean_le hσ t b,
    RationalVerticalCorrection.mass_le_zero (by linarith) hσ.ne' t b]

/-- All actual signed right means are summable for an arbitrary summable
nonnegative family, without a frequency-moment assumption. -/
theorem summable_means {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    {σ : ℝ} (hσ : 1 < σ) (t b : ℝ) : Summable (fun n => a n * mean σ (ω n * t) b) := by
  apply (hs.mul_right (ZetaSechPrimeBoundary.mean σ 0 b + RationalVerticalCorrection.profile σ 0)).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha n)]
  exact mul_le_mul_of_nonneg_left (abs_mean_le hσ (ω n * t) b) (ha n)

/-- The complete rational mass of the nonconstant channels, kept separately
from the common prime-phase kernel. -/
def rationalTotal (σ t b : ℝ) (a ω : ℕ → ℝ) : ℝ :=
  ∑' n, tail a n * RationalVerticalCorrection.mass σ (ω n * t) b

/-- The complete nonconstant rational masses are genuinely summable. -/
theorem summable_rational {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    {σ : ℝ} (hσ : 1 < σ) (t b : ℝ) :
    Summable (fun n => tail a n * RationalVerticalCorrection.mass σ (ω n * t) b) := by
  apply ((tail_summable ha hs).mul_right (RationalVerticalCorrection.profile σ 0)).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (tail_nonneg ha n)
    (RationalVerticalCorrection.mass_nonneg (by linarith) hσ.ne' _ _))]
  exact mul_le_mul_of_nonneg_left (RationalVerticalCorrection.mass_le_zero (by linarith) hσ.ne' _ _)
    (tail_nonneg ha n)

/-- The exact common signed right boundary costs the constant channel's
averaged prime mass plus the complete retained rational correction. -/
theorem negative_nonconstant_le_exact {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hp : ∀ x, 0 ≤ zetaPhaseKernel a ω x) (hω0 : ω 0 = 0)
    {σ : ℝ} (hσ : 1 < σ) (t b : ℝ) :
    -(∑' n, tail a n * mean σ (ω n * t) b) ≤
      a 0 * ZetaSechPrimeBoundary.mean σ 0 b + rationalTotal σ t b a ω := by
  have hz := ZetaSechPhaseFamily.summable_means (tail_nonneg ha) (tail_summable ha hs) (ω := ω) hσ t b
  have hr := summable_rational (ω := ω) ha hs hσ t b
  have he : (∑' n, tail a n * mean σ (ω n * t) b) =
      (∑' n, tail a n * ZetaSechPrimeBoundary.mean σ (ω n * t) b) - rationalTotal σ t b a ω := by
    simp_rw [mean_eq hσ, mul_sub]
    exact hz.tsum_sub hr
  have hp := ZetaSechPhaseFamily.right_boundary_le_exact ha hs hp hω0 hσ t b
  have hp' : -(∑' n, tail a n * ZetaSechPrimeBoundary.mean σ (ω n * t) b) ≤
      a 0 * ZetaSechPrimeBoundary.mean σ 0 b := by
    simpa only [tail, ite_mul, zero_mul] using hp
  rw [he]
  linarith

/-- The real-axis logarithm remains a constant-channel cost after pole clearing. -/
theorem negative_nonconstant_le {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hp : ∀ x, 0 ≤ zetaPhaseKernel a ω x) (hω0 : ω 0 = 0)
    {σ : ℝ} (hσ : 1 < σ) (t b : ℝ) :
    -(∑' n, tail a n * mean σ (ω n * t) b) ≤
      a 0 * Real.log ‖riemannZeta (σ : ℂ)‖ + rationalTotal σ t b a ω := by
  have h := mul_le_mul_of_nonneg_left (ZetaSechPrimeBoundary.mean_zero_le hσ b) (ha 0)
  exact (negative_nonconstant_le_exact ha hs hp hω0 hσ t b).trans (add_le_add h le_rfl)

/-- The complete rational correction has the same decaying allowance for
every nonconstant frequency at least one, with only the original mass cost. -/
theorem rationalTotal_le {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hω : ∀ n, n ≠ 0 → 1 ≤ ω n) {σ t b : ℝ} (hσ : 1 < σ) (ht : t ≠ 0) (hb : b ≠ 0) :
    rationalTotal σ t b a ω ≤ mass a *
      (8 * σ / t ^ 2 + 2 * RationalVerticalCorrection.profile σ 0 * Real.exp (-|t| / |b|)) := by
  have h := (summable_rational (ω := ω) ha hs hσ t b).tsum_le_tsum (fun n => show
      tail a n * RationalVerticalCorrection.mass σ (ω n * t) b ≤
      tail a n * (8 * σ / t ^ 2 + 2 * RationalVerticalCorrection.profile σ 0 * Real.exp (-|t| / |b|)) from by
    by_cases hn : n = 0
    · simp [tail, hn]
    · exact mul_le_mul_of_nonneg_left
        (RationalVerticalCorrection.mass_mul_le (by linarith) hσ.ne' ht hb (hω n hn))
        (tail_nonneg ha n)) ((tail_summable ha hs).mul_right _)
  simpa only [rationalTotal, mass, tsum_mul_right] using h

end
end RiemannGaussian.ZetaRegularizedSechMean
