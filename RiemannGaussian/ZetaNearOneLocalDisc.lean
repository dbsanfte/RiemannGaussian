/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianStrip

/-!
# Actual zeta bounds on shrinking discs near the one-line

The exact complex Gaussian carrier is inverted with bounded local cost.
The resulting zeta estimate applies throughout a height-one window of
the whole near-one strip and on every eligible shrinking disc. Zeros
are allowed in these discs; only the original pole is excluded, using
the actual ordinate. The height exponent is unchanged.
-/

namespace RiemannGaussian.ZetaNearOneLocalDisc
noncomputable section
open Complex Metric Set ZetaGaussianLocalizer ZetaGaussianStrip
open ZetaNearOneLogProfile DirichletPowerParameters DerivativeOrderComparison

/-- Exact recovery of zeta from its Gaussian carrier, with both complex
normalization factors retained. -/
theorem reconstruction (t : ℝ) {s : ℂ} (hs : s ≠ 1) (hs' : s + 1 ≠ 0) :
    riemannZeta s = carrier t s * Complex.exp (-((s - Complex.I * (t : ℂ)) ^ 2)) *
      ((s + 1) / (s - 1)) := by
  have hcancel : carrier t s * Complex.exp (-((s - Complex.I * (t : ℂ)) ^ 2)) =
      regularized s := by
    rw [carrier, mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  rw [hcancel, regularized_eq hs]
  field_simp [hs', sub_ne_zero.mpr hs]

/-- The inverse Gaussian costs at most one exponential unit in a
height-one window, regardless of the central height. -/
theorem inverse_gaussian_bound (t : ℝ) {s : ℂ} (h : |s.im - t| ≤ 1) :
    ‖Complex.exp (-((s - Complex.I * (t : ℂ)) ^ 2))‖ ≤ Real.exp 1 := by
  have he : ((s - Complex.I * (t : ℂ)) ^ 2).re = s.re ^ 2 - (s.im - t) ^ 2 := by
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, one_mul, sub_zero, zero_add]
  rw [Complex.norm_exp, Complex.neg_re, he]
  apply Real.exp_le_exp.mpr
  have hsq : (s.im - t) ^ 2 ≤ 1 := by
    have h' := (sq_le_sq₀ (abs_nonneg (s.im - t)) (by norm_num : (0 : ℝ) ≤ 1)).mpr h
    simpa only [sq_abs, one_pow] using h'
  nlinarith [sq_nonneg s.re]

/-- The exact inverse rational normalization has uniformly bounded
norm when the imaginary part stays away from the pole's ordinate. -/
theorem inverse_ratio_bound {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 3 / 2)
    (hy : 1 ≤ |s.im|) : ‖(s + 1) / (s - 1)‖ ≤ 4 := by
  have hden : |s.im| ≤ ‖s - 1‖ := by
    simpa only [Complex.sub_im, Complex.one_im, sub_zero] using Complex.abs_im_le_norm (s - 1)
  have hnum := Complex.norm_le_abs_re_add_abs_im (s + 1)
  simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, add_zero] at hnum
  rw [abs_of_nonneg (by linarith : 0 ≤ s.re + 1)] at hnum
  rw [norm_div]
  apply (div_le_iff₀ (by linarith : 0 < ‖s - 1‖)).mpr
  linarith

/-- A height-one window around an ordinate of absolute value at least
two stays at least one unit away from height zero. -/
theorem one_le_abs_im {t : ℝ} (ht : 2 ≤ |t|) {s : ℂ} (hs : |s.im - t| ≤ 1) :
    1 ≤ |s.im| := by
  have h : |t| ≤ |s.im| + |s.im - t| := by
    calc
      |t| = |s.im + (t - s.im)| := by congr 1; ring
      _ ≤ |s.im| + |t - s.im| := abs_add_le _ _
      _ = _ := by rw [abs_sub_comm t s.im]
  linarith

/-- The actual pole is excluded by the window's height, independently
of every zeta-zero question. -/
theorem ne_one_of_window {t : ℝ} (ht : 2 ≤ |t|) {s : ℂ} (hs : |s.im - t| ≤ 1) :
    s ≠ 1 := by
  have h := one_le_abs_im ht hs
  intro he
  norm_num [he] at h

/-- The near-one line profile controls the actual zeta norm throughout
the complete local strip, with a constant additive logarithmic cost. -/
theorem local_norm_bound (k : ℕ) (hk : 1 ≤ k) {t : ℝ} (ht : 2 ≤ |t|) {s : ℂ}
    (hlo : line k ≤ s.re) (hhi : s.re ≤ 3 / 2) (hwindow : |s.im - t| ≤ 1) :
    ‖riemannZeta s‖ ≤ Real.exp (profile k t + 14) := by
  have hs : 1 / 2 ≤ s.re := (half_le_line k hk).trans hlo
  rw [reconstruction t (ne_one_of_window ht hwindow) (add_one_ne_zero (by linarith)),
    norm_mul, norm_mul]
  have hm := mul_le_mul
    (mul_le_mul (carrier_bound k hk t hlo hhi) (inverse_gaussian_bound t hwindow)
      (norm_nonneg _) (Real.exp_pos _).le)
    (inverse_ratio_bound hs hhi (one_le_abs_im ht hwindow)) (norm_nonneg _)
    (by positivity)
  apply hm.trans
  have h4 : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  calc
    Real.exp (profile k t + 10) * Real.exp 1 * 4 ≤
        Real.exp (profile k t + 10) * Real.exp 1 * Real.exp 3 :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = Real.exp (profile k t + 14) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

/-- The same local-strip estimate controls the positive logarithm
continuously through every zeta zero in the window. -/
theorem local_posLog_bound (k : ℕ) (hk : 1 ≤ k) {t : ℝ} (ht : 2 ≤ |t|) {s : ℂ}
    (hlo : line k ≤ s.re) (hhi : s.re ≤ 3 / 2) (hwindow : |s.im - t| ≤ 1) :
    Real.posLog ‖riemannZeta s‖ ≤ profile k t + 14 := by
  have h := Real.posLog_le_posLog (norm_nonneg _) (local_norm_bound k hk ht hlo hhi hwindow)
  have he : Real.posLog (Real.exp (profile k t + 14)) = profile k t + 14 := by
    rw [Real.posLog_eq_log (by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.one_le_exp_iff.mpr (by linarith [profile_nonneg k t])), Real.log_exp]
  rwa [he] at h

/-- Recentring at the actual ordinate gives the same logarithmic
profile on the full strip of real coordinates, not only the original line. -/
theorem full_strip_posLog_bound (k : ℕ) (hk : 1 ≤ k) {s : ℂ}
    (ht : 2 ≤ |s.im|) (hlo : line k ≤ s.re) (hhi : s.re ≤ 3 / 2) :
    Real.posLog ‖riemannZeta s‖ ≤ profile k s.im + 14 :=
  local_posLog_bound k hk ht hlo hhi (by simp)

/-- The safe local center retains the independent horizontal shift. -/
def center (x t : ℝ) : ℂ := ((1 + x : ℝ) : ℂ) + Complex.I * (t : ℂ)

/-- Every shrinking disc stays inside the proved near-one local strip.
The shift may be arbitrarily small and is not tied to a fixed fraction of the width. -/
theorem disc_geometry (k : ℕ) (hk : 1 ≤ k) (t : ℝ) {x : ℝ}
    (hx : 0 < x) (hx' : x ≤ delta k / 4) {s : ℂ}
    (hs : s ∈ closedBall (center x t) (delta k / 2)) :
    line k ≤ s.re ∧ s.re ≤ 3 / 2 ∧ |s.im - t| ≤ 1 := by
  have hn : ‖s - center x t‖ ≤ delta k / 2 := by
    simpa only [mem_closedBall, dist_eq_norm] using hs
  have hre := (Complex.abs_re_le_norm (s - center x t)).trans hn
  have him := (Complex.abs_im_le_norm (s - center x t)).trans hn
  simp only [center, Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, add_zero] at hre
  simp only [center, Complex.sub_im, Complex.add_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, one_mul, zero_add] at him
  have hδ : delta k ≤ 1 / 2 := by
    rw [delta_eq_one_sub_line]
    linarith [half_le_line k hk]
  have hline : line k = 1 - delta k := by rw [delta_eq_one_sub_line]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hline]
    linarith [(abs_le.mp hre).1, delta_pos k]
  · linarith [(abs_le.mp hre).2]
  · linarith

/-- The actual zeta function is analytic on a neighborhood of each
entire selected closed disc; zeros inside are allowed. -/
theorem analyticOnNhd_disc (k : ℕ) (hk : 1 ≤ k) {t x : ℝ}
    (ht : 2 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta k / 4) :
    AnalyticOnNhd ℂ riemannZeta (closedBall (center x t) (delta k / 2)) := by
  intro s hs
  exact analyticOn_riemannZeta s (ne_one_of_window ht (disc_geometry k hk t hx hx' hs).2.2)

/-- A genuine uniform positive-log estimate on every shrinking local
disc, with no zero-free-disc or unproved analytic-growth premise. -/
theorem disc_posLog_bound (k : ℕ) (hk : 1 ≤ k) {t x : ℝ}
    (ht : 2 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta k / 4) {s : ℂ}
    (hs : s ∈ closedBall (center x t) (delta k / 2)) :
    Real.posLog ‖riemannZeta s‖ ≤ profile k t + 14 := by
  obtain ⟨hlo, hhi, him⟩ := disc_geometry k hk t hx hx' hs
  exact local_posLog_bound k hk ht hlo hhi him

end
end RiemannGaussian.ZetaNearOneLocalDisc
