/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.EtaDyadicPhaseBounds

/-!
# Retaining the imaginary dyadic completion in signed contour tests

Negative cosine controls the real completion term. A one-sided sine
condition also controls its imaginary part, which is needed by the
oriented vertical reflection weights. The estimates are uniform over
the whole closed half strip and retain the exact sine identity.
-/

open Complex
namespace RiemannGaussian
noncomputable section

/-- Exact sine component of the original complex dyadic term. -/
theorem pairedEtaDyadicTerm_im (s : ℂ) :
    (pairedEtaDyadicTerm s).im =
      -(2 * Real.exp (-s.re * Real.log 2) * Real.sin (s.im * Real.log 2)) := by
  unfold pairedEtaDyadicTerm
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0),
    show Complex.log (2 : ℂ) = (Real.log 2 : ℂ) from
      (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm]
  simp only [mul_im, re_ofNat, im_ofNat, zero_mul, add_zero, Complex.exp_im,
    mul_re, ofReal_re, neg_re, ofReal_im, neg_im, sub_zero]
  rw [show Real.log 2 * -s.im = -(s.im * Real.log 2) by ring, Real.sin_neg]
  rw [show Real.log 2 * -s.re = -s.re * Real.log 2 by ring]
  ring

/-- The exact dyadic logarithmic derivative keeps its imaginary phase
over the same squared denominator as its real part. -/
theorem pairedEtaFactorLogDerivative_im (s : ℂ) :
    (pairedEtaFactorLogDerivative s).im =
      Real.log 2 * (pairedEtaDyadicTerm s).im / normSq (pairedEtaFactor s) := by
  rw [pairedEtaFactorLogDerivative_eq_dyadic]
  simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, Complex.div_im,
    sub_re, sub_im, one_re, one_im]
  change _ = Real.log 2 * (pairedEtaDyadicTerm s).im / normSq (1 - pairedEtaDyadicTerm s)
  ring

/-- The completion denominator squared is at most six on the entire
closed half strip, independently of its phase. -/
theorem normSq_pairedEtaFactor_strip_le_six {s : ℂ}
    (hlo : 1 / 2 ≤ s.re) (hhi : s.re ≤ 1) : normSq (pairedEtaFactor s) ≤ 6 := by
  have hq := (normSq_pairedEtaDyadicTerm_strip_bounds hlo hhi).2
  have hre : -(3 / 2 : ℝ) ≤ (pairedEtaDyadicTerm s).re := by
    nlinarith [Complex.re_sq_le_normSq (pairedEtaDyadicTerm s)]
  change normSq (1 - pairedEtaDyadicTerm s) ≤ 6
  rw [Complex.normSq_sub]
  simp only [normSq_one, one_mul, conj_re]
  linarith

private lemma amplitude_ge_one {s : ℂ} (hlo : 1 / 2 ≤ s.re) (hhi : s.re ≤ 1) :
    1 ≤ 2 * Real.exp (-s.re * Real.log 2) := by
  have hq := (normSq_pairedEtaDyadicTerm_strip_bounds hlo hhi).1
  have he : (2 * Real.exp (-s.re * Real.log 2)) ^ 2 = normSq (pairedEtaDyadicTerm s) := by
    rw [normSq_pairedEtaDyadicTerm, mul_pow, ← Real.exp_nat_mul _ 2]
    norm_num only [Nat.cast_ofNat]
    congr 2
    ring
  rw [← he] at hq
  nlinarith [Real.exp_pos (-s.re * Real.log 2)]

/-- A negative sine bounded away from zero gives a uniform positive
imaginary completion derivative on the full closed strip. -/
theorem pairedEtaFactorLogDerivative_im_phase_lower {s : ℂ}
    (hlo : 1 / 2 ≤ s.re) (hhi : s.re ≤ 1)
    (hcos : Real.cos (s.im * Real.log 2) ≤ 0)
    (hsin : Real.sin (s.im * Real.log 2) ≤ -1 / 2) :
    Real.log 2 / 12 ≤ (pairedEtaFactorLogDerivative s).im := by
  have ha := amplitude_ge_one hlo hhi
  have him : 1 / 2 ≤ (pairedEtaDyadicTerm s).im := by
    rw [pairedEtaDyadicTerm_im]
    nlinarith [mul_le_mul_of_nonneg_left hsin
      (show 0 ≤ 2 * Real.exp (-s.re * Real.log 2) by positivity)]
  have hd : 0 < normSq (pairedEtaFactor s) :=
    Complex.normSq_pos.mpr (pairedEtaFactor_ne_zero_of_nonpos_cos hcos)
  have hu := normSq_pairedEtaFactor_strip_le_six hlo hhi
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [pairedEtaFactorLogDerivative_im]
  apply (le_div_iff₀ hd).mpr
  nlinarith [mul_le_mul_of_nonneg_left him hl.le, mul_le_mul_of_nonneg_left hu hl.le]

/-- A positive sine bounded away from zero gives the reflected negative
imaginary derivative, preserving the orientation of the phase. -/
theorem pairedEtaFactorLogDerivative_im_phase_upper {s : ℂ}
    (hlo : 1 / 2 ≤ s.re) (hhi : s.re ≤ 1)
    (hcos : Real.cos (s.im * Real.log 2) ≤ 0)
    (hsin : 1 / 2 ≤ Real.sin (s.im * Real.log 2)) :
    (pairedEtaFactorLogDerivative s).im ≤ -Real.log 2 / 12 := by
  have ha := amplitude_ge_one hlo hhi
  have him : (pairedEtaDyadicTerm s).im ≤ -1 / 2 := by
    rw [pairedEtaDyadicTerm_im]
    nlinarith [mul_le_mul_of_nonneg_left hsin
      (show 0 ≤ 2 * Real.exp (-s.re * Real.log 2) by positivity)]
  have hd : 0 < normSq (pairedEtaFactor s) :=
    Complex.normSq_pos.mpr (pairedEtaFactor_ne_zero_of_nonpos_cos hcos)
  have hu := normSq_pairedEtaFactor_strip_le_six hlo hhi
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [pairedEtaFactorLogDerivative_im]
  apply (div_le_iff₀ hd).mpr
  nlinarith [mul_le_mul_of_nonneg_left him hl.le, mul_le_mul_of_nonneg_left hu hl.le]

end
end RiemannGaussian
