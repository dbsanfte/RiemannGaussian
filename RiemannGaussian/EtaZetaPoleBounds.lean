import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaHorizontalDefectGapFinite
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Eta bounds for the zeta function with its pole removed

The literal eta support gives a positive-half-plane bound without a
Dirichlet-series convergence restriction. Its factor identity is retained
after removing the zeta pole. Quantitative lower bounds for the elementary
dyadic factor will then allow a maximum-modulus argument across its zeros.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The literal eta support has Laplace mass at most that of the positive
half-line. This bound holds throughout the positive half-plane. -/
theorem norm_pairedEtaCore_le_div_re {s : ℂ} (hs : 0 < s.re) :
    ‖pairedEtaCore s‖ ≤ ‖s‖ / s.re := by
  simpa [pairedEtaCorePartialSum, div_eq_mul_inv] using
    norm_pairedEtaCore_sub_partialSum_le hs 0

/-- The pole-removed zeta function retains the exact eta factor identity,
including the removable point at one. -/
theorem pairedEtaCore_mul_sub_one_eq_factor_riemannZeta₁ {s : ℂ} (hs : 0 < s.re) :
    pairedEtaCore s * (s - 1) =
      (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta₁ s := by
  by_cases hs1 : s = 1
  · subst s
    norm_num [Complex.cpow_neg_one]
  · rw [pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one hs hs1,
      riemannZeta_eq_inv_sub_mul hs1]
    field_simp

/-- A quantitative lower bound for the dyadic factor controls the
pole-removed zeta function by the original eta support mass. -/
theorem norm_riemannZeta₁_le_of_etaFactor_lower {s : ℂ} (hs : 0 < s.re)
    (hfactor : (1 / 4 : ℝ) ≤ ‖1 - 2 * (2 : ℂ) ^ (-s)‖) :
    ‖riemannZeta₁ s‖ ≤ 4 * ‖s - 1‖ * ‖s‖ / s.re := by
  have he := congrArg norm (pairedEtaCore_mul_sub_one_eq_factor_riemannZeta₁ hs)
  simp only [norm_mul] at he
  have hm := mul_le_mul_of_nonneg_right (norm_pairedEtaCore_le_div_re hs) (norm_nonneg (s - 1))
  have hf := mul_le_mul_of_nonneg_right hfactor (norm_nonneg (riemannZeta₁ s))
  calc
    ‖riemannZeta₁ s‖ ≤ 4 * (‖s‖ / s.re * ‖s - 1‖) := by nlinarith
    _ = _ := by ring

/-- The norm of the complete dyadic term retains its real exponent. -/
theorem norm_two_mul_two_cpow_neg (s : ℂ) :
    ‖2 * (2 : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (1 - s.re) := by
  have hp := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2) (-s)
  norm_num only [Complex.ofReal_ofNat, Complex.neg_re] at hp
  rw [norm_mul, Complex.norm_ofNat, hp]
  rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv]

/-- On either vertical edge of the half-to-three-halves strip, the
dyadic factor has a common explicit lower bound. -/
theorem quarter_le_norm_etaFactor_of_re_boundary {s : ℂ}
    (hs : s.re = 1 / 2 ∨ s.re = 3 / 2) :
    (1 / 4 : ℝ) ≤ ‖1 - 2 * (2 : ℂ) ^ (-s)‖ := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rcases hs with hs | hs
  · have h := norm_sub_norm_le (2 * (2 : ℂ) ^ (-s)) (1 : ℂ)
    rw [norm_two_mul_two_cpow_neg, hs, show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num,
      ← Real.sqrt_eq_rpow, norm_one, norm_sub_rev] at h
    nlinarith
  · have h := norm_sub_norm_le (1 : ℂ) (2 * (2 : ℂ) ^ (-s))
    rw [norm_one, norm_two_mul_two_cpow_neg, hs,
      show (1 - 3 / 2 : ℝ) = -(1 / 2) by norm_num,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← Real.sqrt_eq_rpow] at h
    have hi : (Real.sqrt 2)⁻¹ ≤ 3 / 4 := by
      rw [inv_eq_one_div, div_le_iff₀ hsqrt]
      nlinarith
    linarith

/-- On a horizontal edge whose dyadic phase is minus one, the real
part alone bounds the complete factor away from zero. -/
theorem one_le_norm_etaFactor_of_cos_eq_neg_one {s : ℂ}
    (hcos : Real.cos (Real.log 2 * s.im) = -1) :
    (1 : ℝ) ≤ ‖1 - 2 * (2 : ℂ) ^ (-s)‖ := by
  have hre : (1 - 2 * (2 : ℂ) ^ (-s)).re =
      1 + 2 * Real.exp (-(Real.log 2 * s.re)) := by
    have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) :=
      (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
    simp only [hlog, Complex.sub_re, Complex.one_re, Complex.mul_re,
      Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero, Complex.exp_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
      Complex.mul_im, mul_neg, Real.cos_neg]
    ring_nf
    rw [hcos]
    ring
  have h := Complex.re_le_norm (1 - 2 * (2 : ℂ) ^ (-s))
  rw [hre] at h
  linarith [Real.exp_pos (-(Real.log 2 * s.re))]

end

end RiemannGaussian
