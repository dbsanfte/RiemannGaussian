/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.DigammaLogarithmicBound
import RiemannGaussian.ZetaGlobalPoisson
import RiemannGaussian.RiemannXiSuzukiRealAxisCompletedLog
import RiemannGaussian.ZetaPhaseArithmetic

/-!
# A global signed zeta budget with an explicit logarithmic allowance

The full positive xi Poisson mass and the signed prime work share the
exact completed-zeta identity. The only regular contribution is the
literal Gamma correction, whose real part has a proved logarithmic upper
bound. There is no local divisor radius or local analytic remainder.

All genuine zeros and their multiplicities are retained before selecting
any of them. The estimates require only the known Euler half-plane.
-/

namespace RiemannGaussian
noncomputable section
open Complex
open scoped Topology

/-- The full complex completion correction after separating the pole at
one. Its phase is retained before the real-part bound. -/
def zetaGlobalRegularCorrection (s : ℂ) : ℂ :=
  1 / s - Complex.log Real.pi / 2 + Complex.digamma (s / 2) / 2

/-- The actual complex logarithmic derivatives satisfy the complete
source budget on the Euler half-plane, before any sign is used. -/
theorem zeta_global_complex_budget {s : ℂ} (hs : 1 < s.re) :
    -logDeriv riemannZeta s + logDeriv riemannXi s =
      1 / (s - 1) + zetaGlobalRegularCorrection s := by
  have hs1 : s ≠ 1 := by intro he; rw [he] at hs; norm_num at hs
  rw [logDeriv_riemannXi_of_re_pos_of_riemannZeta_ne_zero (by linarith) hs1
    (riemannZeta_ne_zero_of_one_lt_re hs), zetaGlobalRegularCorrection]
  ring

/-- A logarithmic allowance for the literal completion correction, uniform
throughout the closed right half-plane. The coefficient of the growing
logarithm is one and has no local-radius constant. -/
theorem re_zetaGlobalRegularCorrection_le {s : ℂ} (hs : 1 ≤ s.re) :
    (zetaGlobalRegularCorrection s).re ≤ 1 + Real.log (s.re + |s.im|) := by
  have hs0 : 0 < s.re := by linarith
  have hsN : 0 < Complex.normSq s :=
    Complex.normSq_pos.mpr (Complex.ne_zero_of_re_pos hs0)
  have hsNorm : 0 < ‖s‖ := norm_pos_iff.mpr (Complex.ne_zero_of_re_pos hs0)
  have hh : 0 < (s / 2).re := by simpa using half_pos hs0
  have hpsi := re_digamma_le_log_normSq_div_re hh
  have he : Complex.normSq (s / 2) / (s / 2).re = Complex.normSq s / (2 * s.re) := by
    simp only [Complex.normSq_apply, Complex.div_ofNat_re, Complex.div_ofNat_im]
    field_simp
  rw [he] at hpsi
  have hq : Complex.normSq s / (2 * s.re) ≤ Complex.normSq s :=
    div_le_self hsN.le (by linarith)
  have hlog := Real.log_le_log (div_pos hsN (by positivity)) hq
  have hnormlog : Real.log (Complex.normSq s) = 2 * Real.log ‖s‖ := by
    rw [← Complex.sq_norm, Real.log_pow]
    norm_num
  rw [hnormlog] at hlog
  have hp : (1 / s : ℂ).re ≤ 1 := by
    rw [one_div, Complex.inv_re, div_le_one hsN]
    simp only [Complex.normSq_apply]
    nlinarith [sq_nonneg s.im]
  have hpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hn : Real.log ‖s‖ ≤ Real.log (s.re + |s.im|) :=
    Real.log_le_log hsNorm (by
      simpa only [abs_of_pos hs0] using Complex.norm_le_abs_re_add_abs_im s)
  unfold zetaGlobalRegularCorrection
  simp only [Complex.add_re, Complex.sub_re, Complex.div_ofNat_re, Complex.log_re,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  linarith

/-- The full signed prime response and every genuine zero share one exact
budget. All analytic remainder terms have been removed by the global xi
expansion, leaving the actual complex completion correction. -/
theorem zeta_global_real_budget {s : ℂ} (hs : 1 < s.re) :
    (-logDeriv riemannZeta s).re +
      (∑' rho : NontrivialZetaZero, zetaGlobalPoissonSummand s rho) =
        (1 / (s - 1) : ℂ).re + (zetaGlobalRegularCorrection s).re := by
  rw [tsum_zetaGlobalPoissonSummand hs.le]
  simpa only [Complex.add_re] using congrArg Complex.re (zeta_global_complex_budget hs)

/-- An independent signed upper budget for the actual arithmetic response
plus the entire zero mass, with the exact pole at one left uncompressed. -/
theorem zeta_global_real_budget_le {s : ℂ} (hs : 1 < s.re) :
    (-logDeriv riemannZeta s).re +
      (∑' rho : NontrivialZetaZero, zetaGlobalPoissonSummand s rho) ≤
        (1 / (s - 1) : ℂ).re + 1 + Real.log (s.re + |s.im|) := by
  rw [zeta_global_real_budget hs]
  linarith [re_zetaGlobalRegularCorrection_le hs.le]

/-- At any positive displacement from one the exact nonreal pole and the
full zero mass obey a logarithmic budget, with no small-displacement
restriction. -/
theorem zeta_global_vertical_budget_le {x : ℝ} (hx : 0 < x) (y : ℝ) :
    (-logDeriv riemannZeta (((1 + x : ℝ) : ℂ) + I * y)).re +
      (∑' rho : NontrivialZetaZero,
        zetaGlobalPoissonSummand (((1 + x : ℝ) : ℂ) + I * y) rho) ≤
      x / (x ^ 2 + y ^ 2) + 1 + Real.log (1 + x + |y|) := by
  have h := zeta_global_real_budget_le
    (s := ((1 + x : ℝ) : ℂ) + I * y) (by simp; linarith)
  have hp : (1 / ((((1 + x : ℝ) : ℂ) + I * y) - 1) : ℂ).re =
      x / (x ^ 2 + y ^ 2) := by
    simp [Complex.normSq_apply, pow_two]
  simpa only [hp, Complex.add_re, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, mul_zero, sub_zero, add_zero, Complex.add_im, zero_add] using h

/-- A selected actual zero contributes its full multiplicity to the
global inequality at its ordinate. This holds for every nontrivial zero,
without a preliminary restriction to the right quarter of the strip. -/
theorem zeta_global_selected_zero_budget (rho : NontrivialZetaZero)
    {x : ℝ} (hx : 0 < x) :
    (-logDeriv riemannZeta (((1 + x : ℝ) : ℂ) + I * rho.1.im)).re +
      (analyticZetaZeroMultiplicity rho : ℝ) / (1 + x - rho.1.re) ≤
        x / (x ^ 2 + rho.1.im ^ 2) + 1 + Real.log (1 + x + |rho.1.im|) := by
  have hs : 1 ≤ 1 + x := by linarith
  have hsingle := (summable_zetaGlobalPoissonSummand (s := ((1 + x : ℝ) : ℂ) + I * rho.1.im)
    (by simpa using hs)).le_tsum rho
      (fun _ _ => zetaGlobalPoissonSummand_nonneg (by simpa using hs) _)
  rw [zetaGlobalPoissonSummand_at_ordinate rho hs] at hsingle
  linarith [zeta_global_vertical_budget_le hx rho.1.im]

end
end RiemannGaussian
