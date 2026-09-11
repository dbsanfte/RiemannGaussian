/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaCompletionHalfLogBound
import RiemannGaussian.GaussianArchimedeanContour

/-!
# A logarithmic tangent bound for the actual Gaussian digamma term

The proved horizontal completion comparison bounds the real quarter-line
digamma by one logarithm. Keeping a chosen comparison center before
Gaussian integration gives an explicit inverse-height error. The exact
full-line identity and Gaussian absolute first moment justify every term.
-/

namespace RiemannGaussian.GaussianDigammaLogEnvelope

noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology

/-- The actual Archimedean density has one-logarithm growth, with an
explicit shift and no unspecified constant. -/
theorem archimedeanDensity_le_log (r : ℝ) :
    riemannArchimedeanDensity r ≤ Real.log (5 / 4 + |r|) := by
  have h := re_zetaGlobalRegularCorrection_le_shifted_half_log
    (σ := 1 / 2) (by norm_num) r
  have hrec : 0 ≤ (1 / ((1 / 2 : ℂ) + I * (r : ℂ))).re := by
    rw [one_div, Complex.inv_re]
    apply div_nonneg
    · norm_num
    · exact Complex.normSq_nonneg _
  have he : ((1 / 2 : ℂ) + I * (r : ℂ)) / 2 = 1 / 4 + I * ((r / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  unfold zetaGlobalRegularCorrection at h
  push_cast at h
  rw [he] at h
  simp only [Complex.add_re, Complex.sub_re, Complex.div_ofNat_re, Complex.log_re,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos] at h
  rw [show ((1 / 2 : ℝ) + 2 + 2 * |r|) / 2 = 5 / 4 + |r| by ring] at h
  unfold riemannArchimedeanDensity
  push_cast at h
  linarith

/-- Conjugation gives the even real Archimedean density. -/
theorem archimedeanDensity_even (r : ℝ) :
    riemannArchimedeanDensity (-r) = riemannArchimedeanDensity r := by
  unfold riemannArchimedeanDensity
  rw [digamma_quarter_line_neg]
  simp

/-- The half-line symmetric digamma term is exactly one full translated
Gaussian integral. Its convergence and reflection are explicit. -/
theorem gaussianDigammaIntegral_eq_full {ε : ℝ} (hε : 0 < ε) (v : ℝ) :
    gaussianDigammaIntegral ε v = (1 / Real.pi) *
      ∫ r : ℝ, translatedGaussian ε v r * riemannArchimedeanDensity r := by
  have hG := integrable_translatedGaussian_mul_riemannArchimedeanDensity hε v
  have hS := integrable_symmetricGaussian_mul_riemannArchimedeanDensity hε v
  have heven (r : ℝ) : symmetricGaussian ε v (-r) * riemannArchimedeanDensity (-r) =
      symmetricGaussian ε v r * riemannArchimedeanDensity r := by
    rw [symmetricGaussian_even, archimedeanDensity_even]
  have hhalf := integral_even_eq_two_mul_integral_Ioi hS heven
  have hneg : Integrable (fun r : ℝ => translatedGaussian ε v (-r) *
      riemannArchimedeanDensity r) := by
    simpa only [archimedeanDensity_even] using hG.comp_neg
  have hfull : (∫ r : ℝ, symmetricGaussian ε v r * riemannArchimedeanDensity r) =
      2 * ∫ r : ℝ, translatedGaussian ε v r * riemannArchimedeanDensity r := by
    simp_rw [symmetricGaussian, add_mul]
    rw [integral_add hG hneg]
    have hn : (∫ r : ℝ, translatedGaussian ε v (-r) * riemannArchimedeanDensity r) =
        ∫ r : ℝ, translatedGaussian ε v r * riemannArchimedeanDensity r := by
      conv_lhs => enter [2, r]; rw [← archimedeanDensity_even r]
      exact integral_neg_eq_self (fun r : ℝ =>
        translatedGaussian ε v r * riemannArchimedeanDensity r) volume
    rw [hn]
    ring
  unfold gaussianDigammaIntegral
  congr 1
  linarith

/-- The full Gaussian absolute first moment is integrable. -/
theorem integrable_abs_mul_gaussian {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun u : ℝ => |u| * Real.exp (-ε * u ^ 2)) := by
  simpa only [abs_mul, abs_of_pos (Real.exp_pos _)] using
    (integrable_mul_exp_neg_mul_sq hε).abs

/-- Exact full-line Gaussian absolute first moment. -/
theorem integral_abs_mul_gaussian {ε : ℝ} (hε : 0 < ε) :
    (∫ u : ℝ, |u| * Real.exp (-ε * u ^ 2)) = 1 / ε := by
  have hc := integral_mul_cexp_neg_mul_sq (b := (ε : ℂ)) (by simpa using hε)
  have hi := (integrable_mul_cexp_neg_mul_sq (b := (ε : ℂ)) (by simpa using hε)).integrableOn
    (s := Ioi (0 : ℝ))
  have hr : (∫ u : ℝ in Ioi 0, ((u : ℂ) * Complex.exp (-(ε : ℂ) * (u : ℂ) ^ 2)).re) =
      (∫ u : ℝ in Ioi 0, (u : ℂ) * Complex.exp (-(ε : ℂ) * (u : ℂ) ^ 2)).re := integral_re hi
  have he : (((1 / (2 * ε) : ℝ) : ℂ)) = (2 * (ε : ℂ))⁻¹ := by
    push_cast
    rw [one_div]
  rw [hc, ← he] at hr
  have hhalf : (∫ u : ℝ in Ioi 0, u * Real.exp (-ε * u ^ 2)) = 1 / (2 * ε) := by
    simpa [← Complex.ofReal_pow, Complex.mul_re, Complex.exp_re] using hr
  rw [integral_even_eq_two_mul_integral_Ioi (integrable_abs_mul_gaussian hε)
    (fun u => by simp)]
  have habs : (∫ u : ℝ in Ioi 0, |u| * Real.exp (-ε * u ^ 2)) =
      ∫ u : ℝ in Ioi 0, u * Real.exp (-ε * u ^ 2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp only
    rw [abs_of_pos (show 0 < u from hu)]
  rw [habs, hhalf]
  ring

/-- Translation retains the exact first absolute Gaussian moment and its
integrability at every center. -/
theorem translated_gaussian_abs_moment {ε : ℝ} (hε : 0 < ε) (v : ℝ) :
    Integrable (fun r : ℝ => translatedGaussian ε v r * |r - v|) ∧
      (∫ r : ℝ, translatedGaussian ε v r * |r - v|) = 1 / ε := by
  have hi := (integrable_abs_mul_gaussian hε).comp_sub_right v
  constructor
  · apply hi.congr
    filter_upwards with r
    unfold translatedGaussian
    ring
  · calc
      _ = ∫ r : ℝ, |r - v| * Real.exp (-ε * (r - v) ^ 2) := by
        apply integral_congr_ae
        filter_upwards with r
        unfold translatedGaussian
        ring
      _ = ∫ u : ℝ, |u| * Real.exp (-ε * u ^ 2) :=
        integral_sub_right_eq_self (fun u : ℝ => |u| * Real.exp (-ε * u ^ 2)) v
      _ = _ := integral_abs_mul_gaussian hε

/-- A logarithmic tangent bound keeps both the comparison center and the
displacement before the Gaussian and spectral averages are taken. -/
theorem archimedeanDensity_le_tangent (t y r : ℝ) :
    riemannArchimedeanDensity r ≤ Real.log (5 / 4 + |t|) +
      (|r - (t - y)| + |y|) / (5 / 4 + |t|) := by
  let A := 5 / 4 + |t|
  let d := |r - (t - y)| + |y|
  have hA : 0 < A := by dsimp [A]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have htriangle : 5 / 4 + |r| ≤ A + d := by
    have h1 := abs_add_le (r - (t - y)) (t - y)
    have h2 := abs_sub t y
    rw [sub_add_cancel] at h1
    dsimp [A, d]
    linarith
  have hl := Real.log_le_log (by positivity : 0 < (5 / 4 : ℝ) + |r|) htriangle
  have ht := Real.log_le_sub_one_of_pos (div_pos (add_pos_of_pos_of_nonneg hA hd) hA)
  rw [Real.log_div (by positivity : A + d ≠ 0) hA.ne'] at ht
  have he : (A + d) / A - 1 = d / A := by field_simp; ring
  rw [he] at ht
  have hp := archimedeanDensity_le_log r
  change _ ≤ Real.log A + d / A
  linarith

/-- The actual Gaussian digamma integral has an explicit logarithmic
upper envelope at any separately retained comparison center. -/
theorem gaussianDigammaIntegral_le_tangent {ε : ℝ} (hε : 0 < ε) (t y : ℝ) :
    gaussianDigammaIntegral ε (t - y) ≤ (1 / Real.pi) *
      (Real.sqrt (Real.pi / ε) * (Real.log (5 / 4 + |t|) + |y| / (5 / 4 + |t|)) +
        (1 / ε) / (5 / 4 + |t|)) := by
  let A := 5 / 4 + |t|
  have hA : 0 < A := by dsimp [A]; positivity
  have h0 := integrable_translatedGaussian hε (t - y)
  have h1 := translated_gaussian_abs_moment hε (t - y)
  rw [gaussianDigammaIntegral_eq_full hε]
  apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc
    _ ≤ ∫ r : ℝ, translatedGaussian ε (t - y) r * (Real.log A + |y| / A) +
        (translatedGaussian ε (t - y) r * |r - (t - y)|) / A := by
      apply integral_mono (integrable_translatedGaussian_mul_riemannArchimedeanDensity hε (t - y))
        ((h0.mul_const _).add (h1.1.div_const A))
      intro r
      dsimp only [Pi.add_apply]
      have hg : 0 ≤ translatedGaussian ε (t - y) r := by
        unfold translatedGaussian
        positivity
      have h := mul_le_mul_of_nonneg_left (archimedeanDensity_le_tangent t y r)
        hg
      convert h using 1
      ring
    _ = _ := by
      rw [integral_add (h0.mul_const _) (h1.1.div_const A), integral_mul_const,
        integral_div, integral_translatedGaussian hε, h1.2]

end
end RiemannGaussian.GaussianDigammaLogEnvelope
