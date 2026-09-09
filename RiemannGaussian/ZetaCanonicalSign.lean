/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaSignedLocalEstimate

/-!
# Signed canonical zero responses and their boundary weights

A canonical zero contributes its singular Cauchy term together with its
regular correction. Their complete real response can be negative, even
when the zero lies to the left of the evaluation point. An exact identity
retains the radial boundary factor. The negative part is controlled by a
logarithmic boundary weight rather than an unweighted zero count.
-/

open Complex
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- The complete canonical response of one zero, before separating its
singular term from its sign-bearing regular correction. -/
def zetaCanonicalZeroResponse (R : ℝ) (i z : ℂ) : ℂ :=
  1 / (z - i) + conj i / ((R : ℂ) ^ 2 - conj i * z)

/-- The complete response keeps its radial boundary factor exactly. -/
theorem zetaCanonicalZeroResponse_eq_radial {R v : ℝ} {i : ℂ}
    (hi : (v : ℂ) ≠ i) (hd : (R : ℂ) ^ 2 - conj i * v ≠ 0) :
    zetaCanonicalZeroResponse R i v =
      ((R ^ 2 - Complex.normSq i) /
        Complex.normSq ((R : ℂ) ^ 2 - conj i * v) : ℝ) *
        (((R ^ 2 - v ^ 2 : ℝ) : ℂ) / ((v : ℂ) - i) + v) := by
  have hnum : (Complex.normSq i : ℂ) = i * conj i := (Complex.mul_conj i).symm
  have hden : (Complex.normSq ((R : ℂ) ^ 2 - conj i * v) : ℂ) =
      ((R : ℂ) ^ 2 - conj i * v) * ((R : ℂ) ^ 2 - i * v) := by
    rw [← Complex.mul_conj]
    simp
  have hd' : (R : ℂ) ^ 2 - i * v ≠ 0 := by
    have h := (map_ne_zero (starRingEnd ℂ)).mpr hd
    simpa using h
  unfold zetaCanonicalZeroResponse
  push_cast
  rw [hnum, hden]
  have hdc : (R : ℂ) ^ 2 - (v : ℂ) * conj i ≠ 0 := by simpa [mul_comm] using hd
  have hdc' : (R : ℂ) ^ 2 - (v : ℂ) * i ≠ 0 := by simpa [mul_comm] using hd'
  field_simp [sub_ne_zero.mpr hi, hd, hd', hdc, hdc']
  ring

/-- At real evaluation points the full complex identity gives an exact
signed expression, including the radial factor that vanishes at the boundary. -/
theorem zetaCanonicalZeroResponse_re_eq_radial {R v : ℝ} {i : ℂ}
    (hi : (v : ℂ) ≠ i) (hd : (R : ℂ) ^ 2 - conj i * v ≠ 0) :
    (zetaCanonicalZeroResponse R i v).re =
      (R ^ 2 - Complex.normSq i) / Complex.normSq ((R : ℂ) ^ 2 - conj i * v) *
        ((R ^ 2 - v ^ 2) * (1 / ((v : ℂ) - i)).re + v) := by
  rw [zetaCanonicalZeroResponse_eq_radial hi hd]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.add_re, div_eq_mul_inv, one_mul]

private theorem canonical_denominator_lower {R v : ℝ} {i : ℂ}
    (hR : (3 / 4 : ℝ) ≤ R) (hi : ‖i‖ < R) (hv : |v| ≤ 1 / 2) :
    (3 / 16 : ℝ) ≤ ‖(R : ℂ) ^ 2 - conj i * v‖ := by
  have hRp : 0 < R := by linarith
  have h := norm_sub_norm_le ((R : ℂ) ^ 2) (conj i * v)
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRp,
    norm_mul, norm_conj, Complex.norm_real, Real.norm_eq_abs] at h
  have hp := mul_le_mul hi.le hv (abs_nonneg v) hRp.le
  nlinarith

/-- The radial boundary factor controls the entire negative response;
the singular Cauchy contribution keeps its nonnegative sign. -/
theorem zetaCanonicalZeroResponse_re_lower_radial {R v : ℝ} {i : ℂ}
    (hR : (3 / 4 : ℝ) ≤ R) (hi : ‖i‖ < R) (hv : |v| ≤ 1 / 2) (hre : i.re < v) :
    -(16 : ℝ) * (R ^ 2 - Complex.normSq i) ≤ (zetaCanonicalZeroResponse R i v).re := by
  have hn := canonical_denominator_lower hR hi hv
  have hd : (R : ℂ) ^ 2 - conj i * v ≠ 0 := norm_ne_zero_iff.mp (by linarith)
  have hvi : (v : ℂ) ≠ i := by
    intro he
    have he' := congrArg Complex.re he
    simp only [Complex.ofReal_re] at he'
    linarith
  have hsq : (1 / 32 : ℝ) ≤ Complex.normSq ((R : ℂ) ^ 2 - conj i * v) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith
  have hdiff : 0 ≤ R ^ 2 - Complex.normSq i := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg i]
  have hpole : 0 ≤ (1 / ((v : ℂ) - i)).re := by
    rw [one_div, Complex.inv_re]
    exact div_nonneg (by simpa using sub_nonneg.mpr hre.le) (Complex.normSq_nonneg _)
  have hrz : 0 ≤ R ^ 2 - v ^ 2 := by
    nlinarith [(abs_le.mp hv).1, (abs_le.mp hv).2]
  have hbr : -(1 / 2 : ℝ) ≤ (R ^ 2 - v ^ 2) * (1 / ((v : ℂ) - i)).re + v := by
    linarith [mul_nonneg hrz hpole, (abs_le.mp hv).1]
  have hq : 0 ≤ (R ^ 2 - Complex.normSq i) / Complex.normSq ((R : ℂ) ^ 2 - conj i * v) :=
    div_nonneg hdiff (Complex.normSq_nonneg _)
  have hqu : (R ^ 2 - Complex.normSq i) / Complex.normSq ((R : ℂ) ^ 2 - conj i * v) ≤
      32 * (R ^ 2 - Complex.normSq i) := by
    rw [div_le_iff₀ (by linarith : 0 < Complex.normSq ((R : ℂ) ^ 2 - conj i * v))]
    nlinarith [mul_nonneg hdiff (show 0 ≤ Complex.normSq ((R : ℂ) ^ 2 - conj i * v) - 1 / 32 by linarith)]
  rw [zetaCanonicalZeroResponse_re_eq_radial hvi hd]
  nlinarith [mul_le_mul_of_nonneg_left hbr hq]

private theorem radial_deficit_le_log {R q : ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (hq : 0 < q) (hqR : q < R) : R ^ 2 - q ^ 2 ≤ 2 * Real.log (R / q) := by
  have hl := Real.one_sub_inv_le_log_of_pos (div_pos hR hq)
  rw [inv_div] at hl
  have hlpos : 0 ≤ Real.log (R / q) := Real.log_nonneg ((one_le_div hq).mpr hqR.le)
  have hmul : R - q ≤ R * Real.log (R / q) := by
    have h := mul_le_mul_of_nonneg_left hl hR.le
    rw [mul_sub, mul_one, ← mul_div_assoc, mul_div_cancel_left₀ q hR.ne'] at h
    exact h
  have hmul' := mul_le_mul_of_nonneg_left hmul (show 0 ≤ 2 * R by positivity)
  nlinarith [sq_nonneg (R - q), mul_nonneg
    (show 0 ≤ 1 - R ^ 2 by nlinarith) hlpos]

/-- A zero's negative canonical response is paid by its Jensen boundary
weight. This estimate is uniform as the disc radius approaches one, where
an unweighted zero count would lose that control. -/
theorem zetaCanonicalZeroResponse_re_add_log_nonneg {R v : ℝ} {i : ℂ}
    (hR : (3 / 4 : ℝ) ≤ R) (hR1 : R ≤ 1) (hi : ‖i‖ < R) (hi0 : i ≠ 0)
    (hv : |v| ≤ 1 / 2) (hre : i.re < v) :
    0 ≤ (zetaCanonicalZeroResponse R i v).re + 32 * Real.log (R / ‖i‖) := by
  have h := zetaCanonicalZeroResponse_re_lower_radial hR hi hv hre
  have hl := radial_deficit_le_log (by linarith : 0 < R) hR1 (norm_pos_iff.mpr hi0) hi
  rw [← Complex.normSq_eq_norm_sq] at hl
  linarith

/-- The two geometrically admissible terms need not have a nonnegative
sum. This exact example prevents an invalid positivity shortcut. -/
theorem zetaCanonicalZeroResponse_negative_example :
    (zetaCanonicalZeroResponse 1 ((-(5 / 8 : ℝ) : ℂ) + ((3 / 4 : ℝ) : ℂ) * I)
      (-(3 / 8 : ℂ))).re =
      -(6 / 2725 : ℝ) := by
  norm_num [zetaCanonicalZeroResponse, Complex.conj_ofNat, Complex.div_re, Complex.normSq_apply]

end

end RiemannGaussian
