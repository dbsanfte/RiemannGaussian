/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.EtaCurvatureGaussianLimit
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Signed curvature with its complete complex weight

The quartic curvature retains a signed derivative and a negative square.
A variable complex weight contributes its actual derivative and phase.
No normalization is frozen, and the resulting bound does not assume a
sign for the full normalized reflection source.
-/

open Complex Filter MeasureTheory Set Topology
namespace RiemannGaussian
noncomputable section

/-- The complex quartic current whose vertical derivative occurs in
the signed curvature. No real projection has yet been taken. -/
def complexQuarticCurrent (f g : ℝ → ℂ) (t : ℝ) : ℂ :=
  f t ^ 2 * starRingEnd ℂ (f t) * starRingEnd ℂ (g t)

/-- Differentiation of the actual complex current along a vertical
holomorphic parameter. The two derivative hypotheses retain the factor i. -/
theorem hasDerivAt_complexQuarticCurrent {f g : ℝ → ℂ} {h : ℂ} {t : ℝ}
    (hf : HasDerivAt f (I * g t) t) (hg : HasDerivAt g (I * h) t) :
    HasDerivAt (complexQuarticCurrent f g)
      (I * (2 * ((normSq (f t * starRingEnd ℂ (g t)) : ℝ) : ℂ) -
        (f t * starRingEnd ℂ (g t)) ^ 2 -
        f t ^ 2 * starRingEnd ℂ (f t) * starRingEnd ℂ h)) t := by
  have ht := ((hf.pow 2).fun_mul hf.star).fun_mul hg.star
  convert! ht using 1
  rw [← mul_conj (f t * starRingEnd ℂ (g t))]
  simp only [star_def, map_mul, conj_I, starRingEnd_self_apply, Pi.pow_apply]
  ring

/-- The full complex curvature numerator equals its phase interaction
minus a norm square and the signed current derivative. -/
theorem complexSignedCurvature_eq_current {f g : ℝ → ℂ} {h : ℂ} {t : ℝ}
    (hf : HasDerivAt f (I * g t) t) (hg : HasDerivAt g (I * h) t) :
    f t ^ 2 * starRingEnd ℂ (g t ^ 2 - f t * h) =
      2 * (f t * starRingEnd ℂ (g t)) ^ 2 -
        2 * ((normSq (f t * starRingEnd ℂ (g t)) : ℝ) : ℂ) -
          I * deriv (complexQuarticCurrent f g) t := by
  rw [(hasDerivAt_complexQuarticCurrent hf hg).deriv]
  simp only [map_sub, map_pow, map_mul]
  ring_nf
  simp only [I_sq]
  ring

/-- The exact weighted signed identity retains both real and imaginary
weight channels and the full derivative of that same weight. -/
theorem complexSignedCurvature_weighted_re {f g K : ℝ → ℂ} {h K' : ℂ} {t : ℝ}
    (hf : HasDerivAt f (I * g t) t) (hg : HasDerivAt g (I * h) t)
    (hK : HasDerivAt K K' t) :
    (K t * (f t ^ 2 * starRingEnd ℂ (g t ^ 2 - f t * h))).re =
      (deriv (fun u => K u * complexQuarticCurrent f g u) t).im -
        (K' * complexQuarticCurrent f g t).im -
        4 * (f t * starRingEnd ℂ (g t)).im *
          ((K t).re * (f t * starRingEnd ℂ (g t)).im +
            (K t).im * (f t * starRingEnd ℂ (g t)).re) := by
  rw [complexSignedCurvature_eq_current hf hg,
    (hK.fun_mul (hasDerivAt_complexQuarticCurrent hf hg)).deriv]
  rw [← (hasDerivAt_complexQuarticCurrent hf hg).deriv]
  simp only [mul_sub, mul_add, Complex.sub_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.normSq_apply, pow_two, Complex.re_ofNat, Complex.im_ofNat]
  ring

/-- With a real weight the phase interaction is one exact negative
square. The derivative of the weight is still retained. -/
theorem complexSignedCurvature_real_weight {f g : ℝ → ℂ} {w : ℝ → ℝ}
    {h : ℂ} {w' t : ℝ} (hf : HasDerivAt f (I * g t) t)
    (hg : HasDerivAt g (I * h) t) (hw : HasDerivAt w w' t) :
    w t * (f t ^ 2 * starRingEnd ℂ (g t ^ 2 - f t * h)).re =
      (deriv (fun u => (w u : ℂ) * complexQuarticCurrent f g u) t).im -
        w' * (complexQuarticCurrent f g t).im -
        4 * w t * (f t * starRingEnd ℂ (g t)).im ^ 2 := by
  have hk : HasDerivAt (fun u => (w u : ℂ)) (w' : ℂ) t := hw.ofReal_comp
  have he := complexSignedCurvature_weighted_re hf hg hk
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero] at he ⊢
  nlinarith [he]

/-- A general complex weight has a precise phase-defect upper bound.
For nonnegative real weights that defect vanishes. -/
theorem complexSignedCurvature_weighted_re_le {f g K : ℝ → ℂ} {h K' : ℂ} {t : ℝ}
    (hf : HasDerivAt f (I * g t) t) (hg : HasDerivAt g (I * h) t)
    (hK : HasDerivAt K K' t) :
    (K t * (f t ^ 2 * starRingEnd ℂ (g t ^ 2 - f t * h))).re ≤
      (deriv (fun u => K u * complexQuarticCurrent f g u) t).im -
        (K' * complexQuarticCurrent f g t).im +
        2 * (‖K t‖ - (K t).re) * normSq (f t * starRingEnd ℂ (g t)) := by
  let J := f t * starRingEnd ℂ (g t)
  have hreal : (K t * J ^ 2).re ≤ ‖K t‖ * normSq J := by
    apply (Complex.re_le_norm _).trans_eq
    rw [norm_mul, Complex.norm_pow, ← Complex.normSq_eq_norm_sq]
  have ha : -4 * J.im * ((K t).re * J.im + (K t).im * J.re) ≤
      2 * (‖K t‖ - (K t).re) * normSq J := by
    simp only [Complex.mul_re, pow_two, Complex.mul_im, Complex.normSq_apply] at hreal ⊢
    nlinarith
  rw [complexSignedCurvature_weighted_re hf hg hK]
  dsimp only [J] at ha
  linarith

end
end RiemannGaussian
