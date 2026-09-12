/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianPrimeAverage
import RiemannGaussian.ZetaGaussianPoissonAverage
import RiemannGaussian.ZetaGaussianCompletionAverage
import RiemannGaussian.ZetaGaussianNearCancellation

/-!
# The exact original Gaussian prime identity with its full divisor correction

The actual Euler series, every complex zero pole and the complete
Archimedean response share one normalized Gaussian average. The resulting
complex identity is proved on the genuine Euler half-plane before taking
real parts. Its real projection connects the original ordinary prime sum
to the complete cubic remainder and the compensated nearby source.
-/

namespace RiemannGaussian.ZetaGaussianSmoothedIdentity
noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology
open GaussianVerticalAverage

private theorem point_shift (σ t y : ℝ) :
    (σ : ℂ) + I * t - I * y = (σ : ℂ) + I * (t - y) := by ring

/-- The literal zeta pole at one is integrable against the full Gaussian
at every center in the genuine Euler half-plane. -/
theorem integrable_pole {B : ℝ} (hB : 0 < B) {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun y : ℝ => (density B y : ℂ) * (1 / (s - I * y - 1))) := by
  apply (GaussianComplexPoleAverage.integrable_pole hB (z := s - 1) (by simpa using hs)).congr
  filter_upwards with y
  rw [show s - 1 - I * y = s - I * y - 1 by ring, one_div]

/-- The full zeta-pole average is the original complex Gaussian transform
at the distance from one, with every ordinate retained. -/
theorem average_pole {B : ℝ} (hB : 0 < B) {s : ℂ} (hs : 1 < s.re) :
    GaussianVerticalAverage.average B (fun y => 1 / (s - I * y - 1)) =
      GaussianComplexHalfMoments.transform B (s - 1) := by
  have he (y : ℝ) : 1 / (s - I * y - 1) = (s - 1 - I * y)⁻¹ := by
    rw [one_div]
    congr 1
    ring
  simp only [he]
  exact GaussianComplexPoleAverage.average_pole hB (by simpa using hs)

/-- The complete complex xi response is Gaussian-integrable on the Euler
half-plane, by the exact pole, arithmetic and completion identity. -/
theorem integrable_logDeriv_xi {σ B : ℝ} (hσ : 1 < σ) (hB : 0 < B) (t : ℝ) :
    Integrable (fun y : ℝ => (density B y : ℂ) * logDeriv riemannXi ((σ : ℂ) + I * t - I * y)) := by
  let s : ℂ := (σ : ℂ) + I * t
  have hs : 1 < s.re := by simpa [s] using hσ
  have hp := integrable_pole hB hs
  have hc := ZetaGaussianCompletionAverage.integrable_response hB (by linarith : 0 < s.re)
  have ha : Integrable (fun y : ℝ => (density B y : ℂ) * (-logDeriv riemannZeta (s - I * y))) := by
    simpa only [s, point_shift] using ZetaGaussianPrimeAverage.integrable_neg_logDeriv hσ hB t
  apply ((hp.add hc).sub ha).congr
  filter_upwards with y
  have hh := zeta_global_complex_budget (s := s - I * y) (by simpa using hs)
  change (density B y : ℂ) * (1 / (s - I * y - 1)) +
      (density B y : ℂ) * zetaGlobalRegularCorrection (s - I * y) -
      (density B y : ℂ) * (-logDeriv riemannZeta (s - I * y)) =
    (density B y : ℂ) * logDeriv riemannXi (s - I * y)
  linear_combination -(density B y : ℂ) * hh

/-- The actual complete complex smoothed Euler identity retains the
original prime series, full xi response, true pole and entire completion. -/
theorem complex_identity {σ B : ℝ} (hσ : 1 < σ) (hB : 0 < B) (t : ℝ) :
    ZetaGaussianPrimeAverage.primeSum σ B t +
      GaussianVerticalAverage.average B (fun y => logDeriv riemannXi ((σ : ℂ) + I * t - I * y)) =
        GaussianComplexHalfMoments.transform B ((σ : ℂ) + I * t - 1) +
          ZetaGaussianCompletionAverage.response B ((σ : ℂ) + I * t) := by
  let s : ℂ := (σ : ℂ) + I * t
  have hs : 1 < s.re := by simpa [s] using hσ
  have ha : Integrable (fun y : ℝ => (density B y : ℂ) * (-logDeriv riemannZeta (s - I * y))) := by
    simpa only [s, point_shift] using ZetaGaussianPrimeAverage.integrable_neg_logDeriv hσ hB t
  have he : GaussianVerticalAverage.average B (fun y => -logDeriv riemannZeta (s - I * y)) =
      ZetaGaussianPrimeAverage.primeSum σ B t := by
    simpa only [s, point_shift] using ZetaGaussianPrimeAverage.average_neg_logDeriv hσ hB t
  rw [← he, ← average_add B ha (integrable_logDeriv_xi hσ hB t)]
  have heq : (fun y : ℝ => -logDeriv riemannZeta (s - I * y) + logDeriv riemannXi (s - I * y)) =
      (fun y : ℝ => 1 / (s - I * y - 1) + zetaGlobalRegularCorrection (s - I * y)) :=
    funext fun y => zeta_global_complex_budget (by simpa using hs)
  change GaussianVerticalAverage.average B
    (fun y => -logDeriv riemannZeta (s - I * y) + logDeriv riemannXi (s - I * y)) = _
  rw [heq, average_add B (integrable_pole hB hs)
    (ZetaGaussianCompletionAverage.integrable_response hB (by linarith : 0 < s.re)), average_pole hB hs]
  rfl

/-- The real projection is the exact original ordinary Gaussian prime sum
plus the complete multiplicity-weighted Gaussian zero mass. -/
theorem prime_add_zero_mass {σ B : ℝ} (hσ : 1 < σ) (hB : 0 < B) (t : ℝ) :
    GaussianFermiPrimeComparison.ordinarySum σ B t +
      (∑' ρ : NontrivialZetaZero, ZetaGaussianLaplaceMass.mass B ((σ : ℂ) + I * t) ρ) =
        (GaussianComplexHalfMoments.transform B ((σ : ℂ) + I * t - 1)).re +
          (ZetaGaussianCompletionAverage.response B ((σ : ℂ) + I * t)).re := by
  have h := congrArg Complex.re (complex_identity hσ hB t)
  rw [Complex.add_re, Complex.add_re,
    ZetaGaussianPrimeAverage.primeSum_re (σ₀ := σ) (by linarith) le_rfl hB,
    average_re (integrable_logDeriv_xi hσ hB t),
    ZetaGaussianPoissonAverage.integral_logDeriv_xi hB (by simpa using hσ.le)] at h
  exact h

/-- The same actual prime identity keeps the unsmoothed xi center and
the complete original complex cubic remainder, without changing the divisor. -/
theorem prime_add_center_add_remainder {σ B : ℝ} (hσ : 1 < σ) (hB : 0 < B) (t : ℝ) :
    GaussianFermiPrimeComparison.ordinarySum σ B t +
      (logDeriv riemannXi ((σ : ℂ) + I * t)).re +
      (∑' ρ : NontrivialZetaZero, ZetaGaussianPoleRemainder.term B ((σ : ℂ) + I * t) ρ).re =
        (GaussianComplexHalfMoments.transform B ((σ : ℂ) + I * t - 1)).re +
          (ZetaGaussianCompletionAverage.response B ((σ : ℂ) + I * t)).re := by
  have h := prime_add_zero_mass hσ hB t
  rw [ZetaGaussianLaplaceMass.tsum_mass_eq hB (by simpa using hσ.le)] at h
  linarith

/-- The signed difference from the original Euler response is exactly
the smoothed pole correction plus the complete Archimedean error minus
the full complex zero remainder's real part. -/
theorem prime_sub_euler {σ B : ℝ} (hσ : 1 < σ) (hB : 0 < B) (t : ℝ) :
    GaussianFermiPrimeComparison.ordinarySum σ B t - (-logDeriv riemannZeta ((σ : ℂ) + I * t)).re =
      (GaussianLaplacePoleRemainder.remainder B ((σ : ℂ) + I * t - 1)).re +
        (ZetaGaussianCompletionAverage.response B ((σ : ℂ) + I * t) -
          zetaGlobalRegularCorrection ((σ : ℂ) + I * t)).re -
        (∑' ρ : NontrivialZetaZero, ZetaGaussianPoleRemainder.term B ((σ : ℂ) + I * t) ρ).re := by
  have h := prime_add_center_add_remainder hσ hB t
  have he := congrArg Complex.re (zeta_global_complex_budget
    (s := (σ : ℂ) + I * t) (by simpa using hσ))
  simp only [Complex.add_re] at he
  simp only [GaussianLaplacePoleRemainder.remainder, Complex.sub_re]
  linarith

/-- The exact ordinary Gaussian prime sum reaches the compensated
nearby-zero bound. The unsmoothed strip functional, smoothed pole and
Archimedean difference remain signed and explicit. -/
theorem prime_add_selected_le {σ B η : ℝ} (hσ : 1 < σ) (hB : 0 < B) (hη : 0 < η)
    (t : ℝ) (S : Finset NontrivialZetaZero) :
    GaussianFermiPrimeComparison.ordinarySum σ B t +
        (∑ ρ ∈ S, ZetaGaussianNearCancellation.compensated B η ((σ : ℂ) + I * t) ρ) ≤
      (-logDeriv riemannZeta ((σ : ℂ) + I * t)).re +
        (∑' ρ : NontrivialZetaZero, ZetaGaussianNearCancellation.nearCotangent η ((σ : ℂ) + I * t) ρ).re +
        (GaussianLaplacePoleRemainder.remainder B ((σ : ℂ) + I * t - 1)).re +
        (ZetaGaussianCompletionAverage.response B ((σ : ℂ) + I * t) -
          zetaGlobalRegularCorrection ((σ : ℂ) + I * t)).re +
        (24 * B / η ^ 2) * (logDeriv riemannXi ((σ : ℂ) + I * t + (η : ℂ))).re := by
  have h := prime_sub_euler hσ hB t
  have hc := ZetaGaussianNearCancellation.neg_re_tsum_le_sub_sum hB hη
    (s := (σ : ℂ) + I * t) (by simpa using hσ.le) S
  rw [Complex.add_re] at hc
  linarith

end
end RiemannGaussian.ZetaGaussianSmoothedIdentity
