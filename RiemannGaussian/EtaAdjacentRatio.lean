/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.EtaCenteredEulerExpansion
import Mathlib.Analysis.Complex.Convex

/-!
# Exact adjacent eta ratios and their total variation

The complex ratio of consecutive power terms is retained before taking a
norm. Outside the range where a single step can rotate by a large angle,
the inverse of one plus this ratio is bounded by one. Its variation is
controlled by the difference of consecutive logarithmic steps, which
telescopes along the whole tail.
-/

namespace RiemannGaussian
noncomputable section
open Complex Set
open scoped Classical

/-- The exact positive logarithmic step between neighboring positive
arguments. -/
def pairedEtaStepLog (x : ℝ) : ℝ := Real.log ((x + 1) / x)

/-- The complete complex ratio between neighboring eta power terms. -/
def pairedEtaAdjacentRatio (s : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-s * (pairedEtaStepLog x : ℂ))

/-- The exact inverse adjacent multiplier used in the signed tail sum. -/
def pairedEtaAdjacentInverse (s : ℂ) (x : ℝ) : ℂ :=
  (1 + pairedEtaAdjacentRatio s x)⁻¹

/-- Every positive logarithmic step lies below its reciprocal argument. -/
theorem pairedEtaStepLog_bounds {x : ℝ} (hx : 0 < x) :
    0 ≤ pairedEtaStepLog x ∧ pairedEtaStepLog x ≤ 1 / x := by
  have hr : 1 ≤ (x + 1) / x := (le_div_iff₀ hx).mpr (by linarith)
  constructor
  · exact Real.log_nonneg hr
  · have h := Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one hr)
    apply h.trans_eq
    field_simp
    ring

/-- The exact step decreases with the positive argument. -/
theorem pairedEtaStepLog_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    pairedEtaStepLog y ≤ pairedEtaStepLog x := by
  have hy : 0 < y := hx.trans_le hxy
  apply Real.log_le_log (by positivity)
  rw [div_le_div_iff₀ (hx.trans_le hxy) hx]
  nlinarith

/-- The exponential is contractive between two points of the closed left
half-plane; the entire complex difference is retained. -/
theorem norm_exp_sub_exp_le_of_re_nonpos {z w : ℂ} (hz : z.re ≤ 0) (hw : w.re ≤ 0) :
    ‖Complex.exp w - Complex.exp z‖ ≤ ‖w - z‖ := by
  have h := (convex_halfSpace_re_le 0).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ => (Complex.hasDerivAt_exp u).hasDerivWithinAt)
    (fun u hu => show ‖Complex.exp u‖ ≤ (1 : ℝ) by
      rw [Complex.norm_exp]
      exact Real.exp_le_one_iff.mpr hu) hz hw
  simpa using h

/-- The actual neighboring ratio has norm at most one on the positive
real half-plane, at every positive physical argument. -/
theorem norm_pairedEtaAdjacentRatio_le_one {s : ℂ} (hs : 0 ≤ s.re)
    {x : ℝ} (hx : 0 < x) : ‖pairedEtaAdjacentRatio s x‖ ≤ 1 := by
  rw [pairedEtaAdjacentRatio, Complex.norm_exp, Real.exp_le_one_iff]
  simp only [neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  exact neg_nonpos.mpr (mul_nonneg hs (pairedEtaStepLog_bounds hx).1)

/-- Before the adjacent phase step reaches one radian, the ratio remains
in the closed right half-plane. -/
theorem re_pairedEtaAdjacentRatio_nonneg {s : ℂ} {x : ℝ}
    (hx : 0 < x) (hscale : ‖s‖ ≤ x) : 0 ≤ (pairedEtaAdjacentRatio s x).re := by
  have hlog := pairedEtaStepLog_bounds hx
  have hangle : |s.im * pairedEtaStepLog x| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hlog.1]
    calc
      |s.im| * pairedEtaStepLog x ≤ ‖s‖ * pairedEtaStepLog x :=
        mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm s) hlog.1
      _ ≤ x * (1 / x) := mul_le_mul hscale hlog.2 hlog.1 (by positivity)
      _ = 1 := by field_simp
  have hcos : 0 ≤ Real.cos (s.im * pairedEtaStepLog x) := by
    apply Real.cos_nonneg_of_mem_Icc
    have hpi := Real.pi_gt_three
    constructor <;> linarith [(abs_le.mp hangle).1, (abs_le.mp hangle).2]
  rw [pairedEtaAdjacentRatio, Complex.exp_re]
  simp only [neg_mul, neg_im, mul_im, ofReal_re, ofReal_im, mul_zero, zero_add, Real.cos_neg]
  exact mul_nonneg (Real.exp_pos _).le hcos

/-- The denominator has norm at least one at every safely separated
physical cutoff, with no loss of its complex phase in its definition. -/
theorem one_le_norm_one_add_pairedEtaAdjacentRatio {s : ℂ} {x : ℝ}
    (hx : 0 < x) (hscale : ‖s‖ ≤ x) : 1 ≤ ‖1 + pairedEtaAdjacentRatio s x‖ := by
  have h := re_pairedEtaAdjacentRatio_nonneg hx hscale
  have hn := Complex.re_le_norm (1 + pairedEtaAdjacentRatio s x)
  simp only [Complex.add_re, Complex.one_re] at hn
  linarith

/-- The exact inverse adjacent multiplier is uniformly bounded by one. -/
theorem norm_pairedEtaAdjacentInverse_le_one {s : ℂ} {x : ℝ}
    (hx : 0 < x) (hscale : ‖s‖ ≤ x) : ‖pairedEtaAdjacentInverse s x‖ ≤ 1 := by
  rw [pairedEtaAdjacentInverse, norm_inv]
  exact inv_le_one_of_one_le₀ (one_le_norm_one_add_pairedEtaAdjacentRatio hx hscale)

/-- The full complex ratio varies by at most the norm of `s` times the
decrease in the exact logarithmic step. -/
theorem norm_pairedEtaAdjacentRatio_sub_le {s : ℂ} (hs : 0 ≤ s.re)
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    ‖pairedEtaAdjacentRatio s y - pairedEtaAdjacentRatio s x‖ ≤
      ‖s‖ * (pairedEtaStepLog x - pairedEtaStepLog y) := by
  have hleft (u : ℝ) (hu : 0 < u) : (-s * (pairedEtaStepLog u : ℂ)).re ≤ 0 := by
    simp only [neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    exact neg_nonpos.mpr (mul_nonneg hs (pairedEtaStepLog_bounds hu).1)
  have h := norm_exp_sub_exp_le_of_re_nonpos (hleft x hx) (hleft y (hx.trans_le hxy))
  unfold pairedEtaAdjacentRatio
  apply h.trans_eq
  rw [show -s * (pairedEtaStepLog y : ℂ) - -s * (pairedEtaStepLog x : ℂ) =
    s * ((pairedEtaStepLog x - pairedEtaStepLog y : ℝ) : ℂ) by push_cast; ring,
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr (pairedEtaStepLog_antitone hx hxy))]

/-- The inverse multiplier has the same telescoping variation bound.
This estimate keeps the neighboring phases coupled until their difference
has been taken. -/
theorem norm_pairedEtaAdjacentInverse_sub_le {s : ℂ} (hs : 0 ≤ s.re)
    {x y : ℝ} (hx : 0 < x) (hscale : ‖s‖ ≤ x) (hxy : x ≤ y) :
    ‖pairedEtaAdjacentInverse s y - pairedEtaAdjacentInverse s x‖ ≤
      ‖s‖ * (pairedEtaStepLog x - pairedEtaStepLog y) := by
  have hx1 := one_le_norm_one_add_pairedEtaAdjacentRatio hx hscale
  have hy1 := one_le_norm_one_add_pairedEtaAdjacentRatio (hx.trans_le hxy) (hscale.trans hxy)
  have hx0 : 1 + pairedEtaAdjacentRatio s x ≠ 0 := by
    intro h; rw [h, norm_zero] at hx1; linarith
  have hy0 : 1 + pairedEtaAdjacentRatio s y ≠ 0 := by
    intro h; rw [h, norm_zero] at hy1; linarith
  have he : pairedEtaAdjacentInverse s y - pairedEtaAdjacentInverse s x =
      (pairedEtaAdjacentRatio s x - pairedEtaAdjacentRatio s y) /
        ((1 + pairedEtaAdjacentRatio s y) * (1 + pairedEtaAdjacentRatio s x)) := by
    unfold pairedEtaAdjacentInverse
    field_simp
    ring
  rw [he, norm_div, norm_mul, norm_sub_rev]
  calc
    _ ≤ ‖pairedEtaAdjacentRatio s y - pairedEtaAdjacentRatio s x‖ :=
      div_le_self (norm_nonneg _) (one_le_mul_of_one_le_of_one_le hy1 hx1)
    _ ≤ _ := norm_pairedEtaAdjacentRatio_sub_le hs hx hxy

/-- The exponential ratio is exactly the ratio of the actual adjacent
complex power terms, including their argument. -/
theorem cpow_add_one_eq_pairedEtaAdjacentRatio_mul (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ((x + 1 : ℝ) : ℂ) ^ (-s) = pairedEtaAdjacentRatio s x * (x : ℂ) ^ (-s) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (by linarith)),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log (by linarith : 0 ≤ x + 1), ← Complex.ofReal_log hx.le,
    pairedEtaAdjacentRatio, ← Complex.exp_add]
  congr 1
  unfold pairedEtaStepLog
  rw [Real.log_div (by linarith : x + 1 ≠ 0) hx.ne']
  push_cast
  ring

/-- The exact multiplier splits one power term across its two adjacent
values. Its nonzero denominator is proved on the stated physical range. -/
theorem pairedEtaAdjacentInverse_mul_add (s : ℂ) {x : ℝ}
    (hx : 0 < x) (hscale : ‖s‖ ≤ x) :
    pairedEtaAdjacentInverse s x *
        ((x : ℂ) ^ (-s) + ((x + 1 : ℝ) : ℂ) ^ (-s)) = (x : ℂ) ^ (-s) := by
  rw [cpow_add_one_eq_pairedEtaAdjacentRatio_mul s hx]
  have hn := one_le_norm_one_add_pairedEtaAdjacentRatio hx hscale
  have hz : 1 + pairedEtaAdjacentRatio s x ≠ 0 := by
    intro h; rw [h, norm_zero] at hn; linarith
  unfold pairedEtaAdjacentInverse
  rw [show (x : ℂ) ^ (-s) + pairedEtaAdjacentRatio s x * (x : ℂ) ^ (-s) =
    (1 + pairedEtaAdjacentRatio s x) * (x : ℂ) ^ (-s) by ring,
    ← mul_assoc, inv_mul_cancel₀ hz, one_mul]

/-- The complex adjacent ratio approaches one at a cost linear in the
norm of the argument and the exact logarithmic step. -/
theorem norm_pairedEtaAdjacentRatio_sub_one_le {s : ℂ} (hs : 0 ≤ s.re)
    {x : ℝ} (hx : 0 < x) :
    ‖pairedEtaAdjacentRatio s x - 1‖ ≤ ‖s‖ * pairedEtaStepLog x := by
  have hr : (-s * (pairedEtaStepLog x : ℂ)).re ≤ 0 := by
    simp only [neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    exact neg_nonpos.mpr (mul_nonneg hs (pairedEtaStepLog_bounds hx).1)
  have h := norm_exp_sub_exp_le_of_re_nonpos (z := 0) (by simp) hr
  simpa [pairedEtaAdjacentRatio, norm_mul,
    abs_of_nonneg (pairedEtaStepLog_bounds hx).1] using h

/-- The exact complex boundary multiplier is within a linear step cost
of the classical Euler half endpoint. -/
theorem norm_pairedEtaAdjacentInverse_sub_half_le {s : ℂ} (hs : 0 ≤ s.re)
    {x : ℝ} (hx : 0 < x) (hscale : ‖s‖ ≤ x) :
    ‖pairedEtaAdjacentInverse s x - 1 / 2‖ ≤ ‖s‖ * pairedEtaStepLog x / 2 := by
  have hn := one_le_norm_one_add_pairedEtaAdjacentRatio hx hscale
  have hz : 1 + pairedEtaAdjacentRatio s x ≠ 0 := by
    intro h; rw [h, norm_zero] at hn; linarith
  have he : pairedEtaAdjacentInverse s x - 1 / 2 =
      (1 - pairedEtaAdjacentRatio s x) / (2 * (1 + pairedEtaAdjacentRatio s x)) := by
    unfold pairedEtaAdjacentInverse
    field_simp
    ring
  rw [he, norm_div, norm_mul, norm_sub_rev]
  norm_num only [norm_ofNat]
  calc
    _ ≤ ‖pairedEtaAdjacentRatio s x - 1‖ / 2 :=
      div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) (by linarith)
    _ ≤ _ := div_le_div_of_nonneg_right (norm_pairedEtaAdjacentRatio_sub_one_le hs hx) (by norm_num)

end
end RiemannGaussian
