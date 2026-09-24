/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldZeroMass
import RiemannGaussian.GaussianCompletedLogDerivative
import RiemannGaussian.RosserSchoenfeldSharpConstants
import RiemannGaussian.RosserSchoenfeldZetaTwo

/-!
# The complete reciprocal-fourth-power zero mass

Subtracting one third of the reflected xi Poisson mass at two from the
mass at one cancels the leading reciprocal-square term. The positive
difference pays every reciprocal-fourth-power zero weight. Checked
Archimedean constants and the actual zeta logarithmic derivative at two
recover Rosser's classical 0.0000744 constant, with both ordinate signs
and every analytic multiplicity retained.
-/

open Complex
namespace RiemannGaussian.RosserSchoenfeldFourthMass
noncomputable section
open RosserSchoenfeldZeroMass RosserSchoenfeldEulerConstant

/-- The reflected Poisson weight at the real point two. -/
def poissonTwo (ρ : NontrivialZetaZero) : ℝ :=
  (2-ρ.1.re)/((2-ρ.1.re)^2+ρ.1.im^2)+(ρ.1.re+1)/((ρ.1.re+1)^2+ρ.1.im^2)

/-- The exact difference cancelling the leading inverse-square term. -/
def difference (ρ : NontrivialZetaZero) : ℝ := poisson ρ - poissonTwo ρ / 3

/-- The full reflected mass at two equals the actual xi logarithmic derivative. -/
theorem hasSum_two : HasSum
    (fun ρ : NontrivialZetaZero => (analyticZetaZeroMultiplicity ρ : ℝ)*poissonTwo ρ)
    (2 * (logDeriv riemannXi 2).re) := by
  have hz : riemannXi (2 : ℂ) ≠ 0 := by
    intro he
    let ρ : NontrivialZetaZero := ⟨2, (riemannXi_eq_zero_iff_isNontrivialZetaZero 2).mp he⟩
    have hh := NontrivialZetaZero.re_lt_one ρ
    norm_num [ρ] at hh
  have hh := Complex.hasSum_re (hasSum_zetaLogDeriv_reflection hz)
  convert hh using 1
  · ext ρ
    rw [zetaLogDerivDifferenceSummand_reflection_re]
    simp [poissonTwo, Complex.normSq_apply, pow_two]
    ring_nf
    simp
  · simp

/-- The complete difference series is summable with its exact scalar total. -/
theorem hasSum_difference : HasSum
    (fun ρ : NontrivialZetaZero => (analyticZetaZeroMultiplicity ρ : ℝ)*difference ρ)
    (massConstant - (2 * (logDeriv riemannXi 2).re)/3) := by
  have hh := hasSum_poisson.sub (hasSum_two.div_const 3)
  convert hh using 1 <;> first | rfl | (ext ρ; dsimp [difference]; ring)

/-- A positive lower bound uniform across the entire critical strip. -/
private lemma high_lower {b t : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (ht : 0 < t) :
    2*t/((t+1)*(t+4)^2) ≤
      ((1-b)/((1-b)^2+t)+b/(b^2+t)) -
        ((2-b)/((2-b)^2+t)+(b+1)/((b+1)^2+t))/3 := by
  let a := b*(1-b)
  have ha : 0 ≤ a := mul_nonneg hb0 (by linarith)
  have h1 : 0 < (1-b)^2+t := by positivity
  have h2 : 0 < b^2+t := by positivity
  have h3 : 0 < (2-b)^2+t := by positivity
  have h4 : 0 < (b+1)^2+t := by positivity
  have he : ((1-b)/((1-b)^2+t)+b/(b^2+t)) -
      ((2-b)/((2-b)^2+t)+(b+1)/((b+1)^2+t))/3 =
      2*((t+a)^2+2*(t+a)-(1-4*a)*t)/
        (((1-b)^2+t)*(b^2+t)*((2-b)^2+t)*((b+1)^2+t)) := by
    dsimp [a]
    field_simp
    ring
  rw [he]
  have hd1 : ((1-b)^2+t)*(b^2+t) ≤ (t+1)^2 := by
    have hh := mul_le_mul (show (1-b)^2+t ≤ t+1 by nlinarith)
      (show b^2+t ≤ t+1 by nlinarith) h2.le (by positivity : (0 : ℝ) ≤ t+1)
    nlinarith
  have hd2 : ((2-b)^2+t)*((b+1)^2+t) ≤ (t+4)^2 := by
    have hh := mul_le_mul (show (2-b)^2+t ≤ t+4 by nlinarith)
      (show (b+1)^2+t ≤ t+4 by nlinarith) h4.le (by positivity : (0 : ℝ) ≤ t+4)
    nlinarith
  have hd := mul_le_mul hd1 hd2 (mul_nonneg h3.le h4.le) (sq_nonneg (t+1))
  have hn : 2*t*(t+1) ≤ 2*((t+a)^2+2*(t+a)-(1-4*a)*t) := by
    nlinarith [mul_nonneg ha ht.le, sq_nonneg a]
  calc
    _ = (2*t*(t+1))/((t+1)^2*(t+4)^2) := by field_simp
    _ ≤ (2*((t+a)^2+2*(t+a)-(1-4*a)*t))/((t+1)^2*(t+4)^2) :=
      div_le_div_of_nonneg_right hn (by positivity)
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left ((show 0 ≤ 2*t*(t+1) by positivity).trans hn) (by positivity)
      nlinarith [hd]


/-- Every nontrivial zero is paid, including those above the verified window. -/
theorem fourth_point (ρ : NontrivialZetaZero) :
    1/‖(ρ.1 : ℂ)‖^4 ≤ (793/1570 : ℝ)*difference ρ := by
  have hy := ZetaFirstZeroCompleteness.no_zero_through_fourteen ρ
  have ht : 196 < ρ.1.im^2 := by nlinarith [sq_abs ρ.1.im]
  have hb0 := NontrivialZetaZero.zero_lt_re ρ
  have hb1 := NontrivialZetaZero.re_lt_one ρ
  by_cases hlow : |ρ.1.im| ≤ 54
  · have hb := ZetaElevenZeroCompleteness.critical_line_through_fiftyFour ρ hlow
    have hn : ‖(ρ.1 : ℂ)‖^4 = (1/4+ρ.1.im^2)^2 := by
      rw [show ‖(ρ.1 : ℂ)‖^4=(‖(ρ.1 : ℂ)‖^2)^2 by ring, Complex.sq_norm]
      norm_num [Complex.normSq_apply, hb]
      ring
    have hx : 0 < 1/4+ρ.1.im^2 := by positivity
    have hz : 0 < 9/4+ρ.1.im^2 := by positivity
    have hd : difference ρ = 2/((1/4+ρ.1.im^2)*(9/4+ρ.1.im^2)) := by
      norm_num [difference, poisson, poissonTwo, hb]
      field_simp
      ring
    rw [hn, hd, ← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_nonneg (show 0 ≤ ρ.1.im^2-196 by linarith) hx.le]
  · have ht' : 2916 < ρ.1.im^2 := by
      have hh := lt_of_not_ge hlow
      nlinarith [sq_abs ρ.1.im]
    have hnorm : ρ.1.im^2 ≤ ‖(ρ.1 : ℂ)‖^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      nlinarith [sq_nonneg ρ.1.re]
    have hsmall : 1/‖(ρ.1 : ℂ)‖^4 ≤ 1/(ρ.1.im^2)^2 := by
      rw [show ‖(ρ.1 : ℂ)‖^4=(‖(ρ.1 : ℂ)‖^2)^2 by ring]
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (pow_le_pow_left₀ (by positivity) hnorm 2)
    have hp : (ρ.1.im^2+1)*(ρ.1.im^2+4)^2 ≤ (793/785 : ℝ)*(ρ.1.im^2)^3 := by
      have h1 := mul_nonneg (show 0 ≤ ρ.1.im^2-25 by linarith) (sq_nonneg ρ.1.im)
      have h2 := mul_nonneg (show 0 ≤ ρ.1.im^2-1000 by linarith) (sq_nonneg (ρ.1.im^2))
      nlinarith
    have hr : 1/(ρ.1.im^2)^2 ≤ (793/1570 : ℝ)*(2*ρ.1.im^2/
        ((ρ.1.im^2+1)*(ρ.1.im^2+4)^2)) := by
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [hp]
    apply hsmall.trans (hr.trans _)
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 793/1570)
    exact high_lower hb0.le hb1.le (by linarith)

/-- Summability and an exact complete-mass comparison, including multiplicity. -/
theorem fourth_mass_le :
    Summable (fun ρ : NontrivialZetaZero => (analyticZetaZeroMultiplicity ρ : ℝ)/‖(ρ.1 : ℂ)‖^4) ∧
    (∑' ρ : NontrivialZetaZero, (analyticZetaZeroMultiplicity ρ : ℝ)/‖(ρ.1 : ℂ)‖^4) ≤
      (793/1570 : ℝ)*(massConstant-(2*(logDeriv riemannXi 2).re)/3) := by
  have hs := hasSum_difference.summable.mul_left (793/1570 : ℝ)
  have hpoint (ρ : NontrivialZetaZero) :
      (analyticZetaZeroMultiplicity ρ : ℝ)/‖(ρ.1 : ℂ)‖^4 ≤
        (793/1570 : ℝ)*((analyticZetaZeroMultiplicity ρ : ℝ)*difference ρ) := by
    have hh := mul_le_mul_of_nonneg_left (fourth_point ρ)
      (Nat.cast_nonneg (analyticZetaZeroMultiplicity ρ))
    simpa only [mul_one_div, mul_left_comm] using hh
  have hsum := Summable.of_nonneg_of_le (fun ρ => by positivity) hpoint hs
  refine ⟨hsum, ?_⟩
  have hh := hsum.tsum_le_tsum hpoint hs
  simpa only [tsum_mul_left, hasSum_difference.tsum_eq] using hh


/-- Exact evaluation of the difference total, retaining the zeta derivative. -/
theorem difference_constant_eq : massConstant-(2*(logDeriv riemannXi 2).re)/3 =
    1 + (4/3)*Real.eulerMascheroniConstant - 2*Real.log 2 - (2/3)*Real.log Real.pi -
      (2/3)*(deriv riemannZeta 2 / riemannZeta 2).re := by
  rw [logDeriv_riemannXi_of_one_lt_re (by norm_num)]
  rw [show (2 : ℂ)/2=1 by norm_num, Complex.digamma_one]
  norm_num [massConstant, Complex.add_re, Complex.sub_re, Complex.log_re,
    Complex.norm_real, abs_of_pos Real.pi_pos]
  ring

/-- The full reciprocal-fourth-power zero series is summable. -/
theorem norm_fourth_mass_summable : Summable
    (fun ρ : NontrivialZetaZero => (analyticZetaZeroMultiplicity ρ : ℝ)/‖(ρ.1 : ℂ)‖^4) :=
  fourth_mass_le.1

/-- Rosser's fourth-power constant for the actual complete zero divisor. -/
theorem norm_fourth_mass_lt :
    (∑' ρ : NontrivialZetaZero, (analyticZetaZeroMultiplicity ρ : ℝ)/‖(ρ.1 : ℂ)‖^4) <
      (744/10^7 : ℝ) := by
  have hz := RosserSchoenfeldZetaTwo.log_derivative_upper
  have hb := fourth_mass_le.2
  rw [difference_constant_eq] at hb
  have hγ := RosserSchoenfeldSharpConstants.euler_upper
  have hπ := RosserSchoenfeldSharpConstants.log_pi_lower
  have h2 := Real.log_two_gt_d9
  linarith

end
end RiemannGaussian.RosserSchoenfeldFourthMass
