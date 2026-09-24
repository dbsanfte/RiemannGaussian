/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldEulerConstant
import RiemannGaussian.RiemannXiGlobalLogDerivative
import RiemannGaussian.SuzukiGammaShift
import RiemannGaussian.ZetaFirstZeroCompleteness
import RiemannGaussian.ZetaElevenZeroCompleteness

/-!
# The classical reciprocal-square sum over all nontrivial zeros

The complete xi logarithmic-derivative identity evaluates the positive
reflected Poisson mass at one. The proved critical-line verification through
height 54 and the absence of zeros through height 14 compare this exact
mass with the full inverse-square ordinate sum. This yields the classical
0.0463 constant, with every analytic multiplicity and both ordinate signs.

The norm-square version is the m=1 constant of Rosser (1941), Lemma 17,
used for instance in Helfgott, arXiv:1312.7748, Appendix A, (A.4).
The proof here obtains the stronger ordinate-square bound from the repo's
proved global expansion and finite verification; it assumes no zero table,
RH, prime-count bound or short-prime supply.
-/

open Complex Filter Topology
namespace RiemannGaussian.RosserSchoenfeldZeroMass
noncomputable section
open RosserSchoenfeldEulerConstant

/-- Pole-removed xi factorization, including the removable point at one. -/
theorem xi_factor {s : ℂ} (hs : 0 < s.re) :
    riemannXi s = -s * Complex.Gammaℝ s * riemannZeta₁ s := by
  have h2 : s + 2 ≠ 0 := ne_zero_of_re_pos (by simp; linarith)
  have h4 : s + 4 ≠ 0 := ne_zero_of_re_pos (by simp; linarith)
  rw [← suzukiGammaShiftFactor_mul_numerator hs,
    suzukiGammaShiftFactor_eq_polynomial hs, suzukiGammaShiftNumerator]
  field_simp

/-- The exact complex logarithmic derivative of xi at one. -/
theorem xi_log_one : logDeriv riemannXi 1 =
    1 + (Real.eulerMascheroniConstant : ℂ) / 2 - Complex.log 2 - Complex.log Real.pi / 2 := by
  have he : riemannXi =ᶠ[𝓝 (1 : ℂ)]
      (fun s => -s * Complex.Gammaℝ s * riemannZeta₁ s) := by
    filter_upwards [(Complex.isOpen_re_gt 0).mem_nhds (show 0 < (1 : ℂ).re by norm_num)] with s hs
    exact xi_factor hs
  rw [(logDeriv_congr_nhds he).eq_of_nhds,
    logDeriv_mul (f := fun s : ℂ => -s * Complex.Gammaℝ s) (g := riemannZeta₁) (1 : ℂ) (by simp [Complex.Gammaℝ_one]) (by simp)
      ((differentiableAt_id.neg).mul (differentiableAt_Gammaℝ_of_re_pos (by norm_num)))
      (differentiable_riemannZeta₁ 1),
    logDeriv_mul (f := fun s : ℂ => -s) (g := Complex.Gammaℝ) (1 : ℂ) (by norm_num) (by simp [Complex.Gammaℝ_one])
      (by fun_prop) (differentiableAt_Gammaℝ_of_re_pos (by norm_num)),
    logDeriv_Gammaℝ (by norm_num)]
  rw [Complex.digamma_one_half]
  have hn : logDeriv (fun s : ℂ => -s) 1 = 1 := by simp [logDeriv_apply]
  have hz : logDeriv riemannZeta₁ 1 = (Real.eulerMascheroniConstant : ℂ) := by simp [logDeriv_apply]
  rw [hn, hz]
  ring

/-- The positive reflected Poisson weight at one for one genuine zero. -/
def poisson (ρ : NontrivialZetaZero) : ℝ :=
  (1 - ρ.1.re) / ((1 - ρ.1.re)^2 + ρ.1.im^2) +
    ρ.1.re / (ρ.1.re^2 + ρ.1.im^2)

/-- The complete multiplicity-weighted Poisson series has the exact constant. -/
theorem hasSum_poisson : HasSum
    (fun ρ : NontrivialZetaZero => (analyticZetaZeroMultiplicity ρ : ℝ) * poisson ρ)
    massConstant := by
  have hh := Complex.hasSum_re (hasSum_zetaLogDeriv_reflection
    (s := 1) (by simp [riemannXi_one]))
  rw [xi_log_one] at hh
  convert hh using 1
  · ext ρ
    rw [zetaLogDerivDifferenceSummand_reflection_re]
    simp [poisson, Complex.normSq_apply, pow_two]
  · norm_num [massConstant, Complex.mul_re, Complex.log_re,
      Complex.norm_real, abs_of_pos Real.pi_pos]
    ring

/-- A comparison retaining both real-part numerators of the reflected pair. -/
theorem poisson_lower (ρ : NontrivialZetaZero) :
    1 / (1 + ρ.1.im ^ 2) ≤ poisson ρ := by
  have hb0 := NontrivialZetaZero.zero_lt_re ρ
  have hb1 := NontrivialZetaZero.re_lt_one ρ
  have hy := ZetaFirstZeroCompleteness.no_zero_through_fourteen ρ
  have hsq : 196 < ρ.1.im ^ 2 := by nlinarith [sq_abs ρ.1.im]
  have ha : (1 - ρ.1.re) / (1 + ρ.1.im ^ 2) ≤
      (1 - ρ.1.re) / ((1 - ρ.1.re)^2 + ρ.1.im^2) :=
    div_le_div_of_nonneg_left (by linarith) (by nlinarith) (by nlinarith)
  have hb : ρ.1.re / (1 + ρ.1.im ^ 2) ≤
      ρ.1.re / (ρ.1.re^2 + ρ.1.im^2) :=
    div_le_div_of_nonneg_left hb0.le (by nlinarith) (by nlinarith)
  have hh := add_le_add ha hb
  calc
    1 / (1 + ρ.1.im ^ 2) =
        (1 - ρ.1.re) / (1 + ρ.1.im ^ 2) + ρ.1.re / (1 + ρ.1.im ^ 2) := by ring
    _ ≤ poisson ρ := hh

/-- Low zeros are critical; above the verified window the ordinate pays the
full discrepancy from the reciprocal square. -/
theorem ordinate_point_le (ρ : NontrivialZetaZero) :
    1 / ρ.1.im ^ 2 ≤ (785 / 784 : ℝ) * poisson ρ := by
  have hy := ZetaFirstZeroCompleteness.no_zero_through_fourteen ρ
  have hsq : 196 < ρ.1.im ^ 2 := by nlinarith [sq_abs ρ.1.im]
  by_cases hlow : |ρ.1.im| ≤ 54
  · have hb := ZetaElevenZeroCompleteness.critical_line_through_fiftyFour ρ hlow
    have he : poisson ρ = 1 / (1 / 4 + ρ.1.im^2) := by
      norm_num [poisson, hb]
      ring
    rw [he, mul_one_div]
    apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
    nlinarith
  · have hh : 54 < |ρ.1.im| := lt_of_not_ge hlow
    have hs : 2916 < ρ.1.im^2 := by nlinarith [sq_abs ρ.1.im]
    apply le_trans _ (mul_le_mul_of_nonneg_left (poisson_lower ρ) (by norm_num : (0 : ℝ) ≤ 785 / 784))
    rw [mul_one_div]
    apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
    nlinarith

/-- Summability and a bound for the complete inverse-square ordinate mass. -/
theorem ordinate_mass_le :
    Summable (fun ρ : NontrivialZetaZero => (analyticZetaZeroMultiplicity ρ : ℝ) / ρ.1.im^2) ∧
    (∑' ρ : NontrivialZetaZero, (analyticZetaZeroMultiplicity ρ : ℝ) / ρ.1.im^2) ≤
      (785 / 784 : ℝ) * massConstant := by
  have hs := hasSum_poisson.summable.mul_left (785 / 784 : ℝ)
  have hpoint (ρ : NontrivialZetaZero) :
      (analyticZetaZeroMultiplicity ρ : ℝ) / ρ.1.im^2 ≤
        (785 / 784 : ℝ) * ((analyticZetaZeroMultiplicity ρ : ℝ) * poisson ρ) := by
    have hh := mul_le_mul_of_nonneg_left (ordinate_point_le ρ)
      (Nat.cast_nonneg (analyticZetaZeroMultiplicity ρ))
    simpa only [mul_one_div, mul_left_comm] using hh
  have hsum := Summable.of_nonneg_of_le (fun ρ => by positivity) hpoint hs
  refine ⟨hsum, ?_⟩
  have hh := hsum.tsum_le_tsum hpoint hs
  simpa only [tsum_mul_left, hasSum_poisson.tsum_eq] using hh

/-- The complete inverse-square ordinate sum is strictly below 0.0463,
with analytic multiplicities and both signs of the ordinate. -/
theorem ordinate_mass_lt :
    (∑' ρ : NontrivialZetaZero, (analyticZetaZeroMultiplicity ρ : ℝ) / ρ.1.im^2) <
      (463 / 10000 : ℝ) := by
  linarith [ordinate_mass_le.2, mass_constant_upper]

/-- The complete reciprocal norm-square mass is summable. -/
theorem norm_square_mass_summable :
    Summable (fun ρ : NontrivialZetaZero =>
      (analyticZetaZeroMultiplicity ρ : ℝ) / ‖(ρ.1 : ℂ)‖^2) := by
  apply Summable.of_nonneg_of_le (fun ρ => by positivity) _ ordinate_mass_le.1
  intro ρ
  have hy := ZetaFirstZeroCompleteness.no_zero_through_fourteen ρ
  have hs : 0 < ρ.1.im^2 := by nlinarith [sq_abs ρ.1.im]
  have hn : ρ.1.im^2 ≤ ‖(ρ.1 : ℂ)‖^2 := by
    nlinarith [Complex.abs_im_le_norm (ρ.1 : ℂ), sq_abs ρ.1.im,
      norm_nonneg (ρ.1 : ℂ)]
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hs hn

/-- Rosser's reciprocal-square constant for the actual full zeta divisor. -/
theorem norm_square_mass_lt :
    (∑' ρ : NontrivialZetaZero, (analyticZetaZeroMultiplicity ρ : ℝ) / ‖(ρ.1 : ℂ)‖^2) <
      (463 / 10000 : ℝ) := by
  apply lt_of_le_of_lt (norm_square_mass_summable.tsum_le_tsum _ ordinate_mass_le.1)
    ordinate_mass_lt
  intro ρ
  have hy := ZetaFirstZeroCompleteness.no_zero_through_fourteen ρ
  have hs : 0 < ρ.1.im^2 := by nlinarith [sq_abs ρ.1.im]
  have hn : ρ.1.im^2 ≤ ‖(ρ.1 : ℂ)‖^2 := by
    nlinarith [Complex.abs_im_le_norm (ρ.1 : ℂ), sq_abs ρ.1.im,
      norm_nonneg (ρ.1 : ℂ)]
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hs hn

end
end RiemannGaussian.RosserSchoenfeldZeroMass
