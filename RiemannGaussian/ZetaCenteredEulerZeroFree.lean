/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.EtaCenteredEulerExpansion
import RiemannGaussian.ZetaHalfLogZeroFree

/-!
# Low-height zero exclusion from the centered Euler eta expansion

The actual eta function cannot vanish when its complex Euler center dominates
the independently bounded remainder. Squaring this comparison gives an
explicit polynomial region. Reflection then excludes every nontrivial zeta
zero with squared ordinate at most three, and removes the height restriction
from the previously proved reciprocal-logarithm edge strip.

This is an unconditional partial zero exclusion, not a proof of RH or a claim
of a new best classical zero-free region.
-/

namespace RiemannGaussian
noncomputable section
open Complex
open scoped Classical

/-- The full complex Euler center supplies a lower bound for the actual eta
value after the explicit analytic remainder has been paid. -/
theorem norm_pairedEtaCore_ge_centered_euler {s : ℂ} (hs : 0 < s.re) :
    ‖1 / 2 + s / 4‖ - ‖s‖ * ‖s + 1‖ / (4 * (s.re + 1)) ≤ ‖pairedEtaCore s‖ := by
  have h := norm_pairedEtaCore_sub_centered_euler_le hs
  have htri := norm_sub_norm_le (1 / 2 + s / 4) (pairedEtaCore s)
  rw [norm_sub_rev] at htri
  linarith

private theorem centered_euler_square_identity (s : ℂ) :
    (4 * (s.re + 1)) ^ 2 * ‖1 / 2 + s / 4‖ ^ 2 - (‖s‖ * ‖s + 1‖) ^ 2 =
      4 * (s.re + 1) ^ 3 - s.re ^ 2 * s.im ^ 2 - s.im ^ 4 := by
  simp only [mul_pow, Complex.sq_norm]
  norm_num [Complex.normSq_apply]
  ring

/-- A general explicit polynomial region where the actual eta function is
nonzero, obtained by retaining the complex center before estimating. -/
theorem pairedEtaCore_ne_zero_of_centered_euler {s : ℂ} (hs : 0 < s.re)
    (hregion : s.im ^ 4 + s.re ^ 2 * s.im ^ 2 < 4 * (s.re + 1) ^ 3) :
    pairedEtaCore s ≠ 0 := by
  intro hz
  have h := norm_pairedEtaCore_ge_centered_euler hs
  rw [hz, norm_zero] at h
  have hle : 4 * (s.re + 1) * ‖1 / 2 + s / 4‖ ≤ ‖s‖ * ‖s + 1‖ := by
    have h' : ‖1 / 2 + s / 4‖ ≤ ‖s‖ * ‖s + 1‖ / (4 * (s.re + 1)) := by linarith
    have := (le_div_iff₀ (show 0 < 4 * (s.re + 1) by positivity)).mp h'
    linarith
  have hsq := mul_self_le_mul_self (show 0 ≤ 4 * (s.re + 1) * ‖1 / 2 + s / 4‖ by positivity) hle
  have hid := centered_euler_square_identity s
  nlinarith

private theorem low_height_mem_centered_euler {s : ℂ} (hs : 1 / 2 ≤ s.re)
    (ht : s.im ^ 2 ≤ 3) :
    s.im ^ 4 + s.re ^ 2 * s.im ^ 2 < 4 * (s.re + 1) ^ 3 := by
  have hσsq : (1 / 4 : ℝ) ≤ s.re ^ 2 := by nlinarith
  have hσcube : (1 / 8 : ℝ) ≤ s.re ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hs 3
    norm_num at this
    exact this
  have ht4 := mul_self_le_mul_self (sq_nonneg s.im) ht
  have hmix := mul_le_mul_of_nonneg_left ht (sq_nonneg s.re)
  nlinarith

/-- The actual eta function is nonzero at every point to the right of the
critical line whose squared ordinate is at most three, including the line. -/
theorem pairedEtaCore_ne_zero_of_im_sq_le_three {s : ℂ}
    (hs : 1 / 2 ≤ s.re) (ht : s.im ^ 2 ≤ 3) : pairedEtaCore s ≠ 0 :=
  pairedEtaCore_ne_zero_of_centered_euler (by linarith)
    (low_height_mem_centered_euler hs ht)

/-- Every actual nontrivial zero obeys the polynomial constraint obtained
from the complex Euler center, with its real coordinate retained. -/
theorem nontrivialZetaZero_centered_euler_constraint (rho : NontrivialZetaZero) :
    4 * (rho.1.re + 1) ^ 3 ≤ rho.1.im ^ 4 + rho.1.re ^ 2 * rho.1.im ^ 2 := by
  by_contra h
  have hne := pairedEtaCore_ne_zero_of_centered_euler
    (NontrivialZetaZero.zero_lt_re rho) (lt_of_not_ge h)
  apply hne
  rw [pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one
    (NontrivialZetaZero.zero_lt_re rho) rho.2.2.2, rho.2.1, mul_zero]

/-- Every genuine nontrivial zeta zero has squared ordinate strictly
greater than three; functional-equation reflection covers the left half. -/
theorem nontrivialZetaZero_im_sq_gt_three (rho : NontrivialZetaZero) :
    3 < rho.1.im ^ 2 := by
  have hright (ρ : NontrivialZetaZero) (hρ : 1 / 2 ≤ ρ.1.re) : 3 < ρ.1.im ^ 2 := by
    by_contra h
    exact (not_lt_of_ge (nontrivialZetaZero_centered_euler_constraint ρ))
      (low_height_mem_centered_euler hρ (le_of_not_gt h))
  by_cases hρ : 1 / 2 ≤ rho.1.re
  · exact hright rho hρ
  · have h := hright (NontrivialZetaZero.conjugatePartner rho) (by
      simp only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_re,
        Complex.one_re, Complex.conj_re]
      linarith)
    simpa only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_im,
      Complex.one_im, Complex.conj_im, zero_sub, neg_neg] using h

/-- The previous edge estimate's height-one premise now follows from the
actual zero equation, with no finite numerical zero certificate. -/
theorem nontrivialZetaZero_one_lt_abs_im (rho : NontrivialZetaZero) :
    1 < |rho.1.im| := by
  have h := nontrivialZetaZero_im_sq_gt_three rho
  nlinarith [sq_abs rho.1.im, abs_nonneg rho.1.im]

/-- Literal zeta is nonzero throughout the positive half-plane at squared
ordinate at most three, away from its pole. -/
theorem riemannZeta_ne_zero_of_im_sq_le_three {s : ℂ} (hs : 0 < s.re)
    (hs1 : s ≠ 1) (ht : s.im ^ 2 ≤ 3) : riemannZeta s ≠ 0 := by
  intro hz
  have hpole : riemannZeta₁ s = 0 := by rw [riemannZeta₁_eq_sub_one_mul hs1, hz, mul_zero]
  let rho : NontrivialZetaZero := ⟨s, isNontrivialZetaZero_of_poleRemoved_eq_zero hs hpole⟩
  exact (not_le_of_gt (nontrivialZetaZero_im_sq_gt_three rho)) ht

/-- The reciprocal-logarithm edge exclusion now holds for every genuine
nontrivial zero, without an ordinate restriction. -/
theorem nontrivialZetaZero_mem_half_log_strip_all_heights (rho : NontrivialZetaZero) :
    rho.1.re ∈ Set.Ioo (zetaHalfLogZeroMargin rho.1.im) (1 - zetaHalfLogZeroMargin rho.1.im) :=
  nontrivialZetaZero_mem_half_log_strip rho (nontrivialZetaZero_one_lt_abs_im rho).le

/-- Literal zeta nonvanishing on the wider closed right edge at every
ordinate. The pole is excluded explicitly from the analytic domain. -/
theorem riemannZeta_ne_zero_of_half_log_margin_all_heights {s : ℂ} (hs1 : s ≠ 1)
    (hs : 1 - zetaHalfLogZeroMargin s.im ≤ s.re) : riemannZeta s ≠ 0 := by
  intro hz
  have hspos : 0 < s.re := by linarith [zetaHalfLogZeroMargin_lt s.im]
  have hpole : riemannZeta₁ s = 0 := by rw [riemannZeta₁_eq_sub_one_mul hs1, hz, mul_zero]
  let rho : NontrivialZetaZero :=
    ⟨s, isNontrivialZetaZero_of_poleRemoved_eq_zero hspos hpole⟩
  have h := (nontrivialZetaZero_mem_half_log_strip_all_heights rho).2
  change s.re < 1 - zetaHalfLogZeroMargin s.im at h
  linarith

end
end RiemannGaussian
