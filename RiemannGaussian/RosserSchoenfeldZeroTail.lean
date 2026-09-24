/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldZeroMass
import RiemannGaussian.ZetaGlobalSignedBudget

/-!
# An explicit bound for the complete high-zero reciprocal-square tail

Each omitted zero is compared with its positive Poisson weight at the
real point `T`. The exact complete xi mass, prime-power positivity and
the proved digamma bound pay the whole tail. No finite zero table or
unproved zero-count estimate is assumed.
-/

namespace RiemannGaussian.RosserSchoenfeldZeroTail
noncomputable section
open Complex
open scoped Classical

/-- The literal multiplicity-weighted reciprocal-square tail. -/
def term (T : ℝ) (ρ : NontrivialZetaZero) : ℝ :=
  if T ≤ |ρ.1.im| then (analyticZetaZeroMultiplicity ρ : ℝ)/‖(ρ.1 : ℂ)‖^2 else 0

/-- Every zero above the cutoff, with both signs and analytic multiplicities. -/
def value (T : ℝ) : ℝ := ∑' ρ : NontrivialZetaZero, term T ρ

/-- Every omitted-zero weight is nonnegative. -/
theorem term_nonneg (T : ℝ) (ρ : NontrivialZetaZero) : 0 ≤ term T ρ := by
  unfold term
  split_ifs <;> positivity

/-- The tail has genuine absolute convergence. -/
theorem summable_term (T : ℝ) : Summable (term T) := by
  apply RosserSchoenfeldZeroMass.norm_square_mass_summable.of_nonneg_of_le (term_nonneg T)
  intro ρ
  unfold term
  split_ifs
  · exact le_rfl
  · positivity

private theorem point_comparison {T : ℝ} (hT : 2 ≤ T) (ρ : NontrivialZetaZero)
    (hρ : T ≤ |ρ.1.im|) :
    1/‖(ρ.1 : ℂ)‖^2 ≤ (4/T)*((T-ρ.1.re)/((T-ρ.1.re)^2+ρ.1.im^2)) := by
  have hb0 := NontrivialZetaZero.zero_lt_re ρ
  have hb1 := NontrivialZetaZero.re_lt_one ρ
  have hT0 : 0 < T := by linarith
  have hy : T^2 ≤ ρ.1.im^2 := by nlinarith [sq_abs ρ.1.im]
  have hy0 : 0 < ρ.1.im^2 := by nlinarith
  have ha0 : 0 < T-ρ.1.re := by linarith
  have ha : (T-ρ.1.re)^2 ≤ T^2 := by nlinarith
  have hn : ‖(ρ.1 : ℂ)‖^2 = ρ.1.re^2+ρ.1.im^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [hn]
  calc
    _ ≤ 1/ρ.1.im^2 := div_le_div_of_nonneg_left (by norm_num) hy0 (by nlinarith)
    _ ≤ 2/((T-ρ.1.re)^2+ρ.1.im^2) := by
      apply (div_le_div_iff₀ hy0 (by positivity)).mpr
      nlinarith
    _ ≤ _ := by
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (by positivity)
      calc
        (2 : ℝ) ≤ 4*(T-ρ.1.re)/T := (le_div_iff₀ hT0).mpr (by linarith)
        _ = _ := by ring

/-- Every literal tail atom is paid by the original positive Poisson atom. -/
theorem term_le_poisson {T : ℝ} (hT : 2 ≤ T) (ρ : NontrivialZetaZero) :
    term T ρ ≤ (4/T)*zetaGlobalPoissonSummand (T : ℂ) ρ := by
  by_cases hρ : T ≤ |ρ.1.im|
  · have hh := mul_le_mul_of_nonneg_left (point_comparison hT ρ hρ)
      (Nat.cast_nonneg (analyticZetaZeroMultiplicity ρ) : (0 : ℝ) ≤ analyticZetaZeroMultiplicity ρ)
    simp only [term, if_pos hρ, zetaGlobalPoissonSummand, Complex.ofReal_re,
      Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_im, zero_sub]
    convert! hh using 1 <;> ring
  · rw [term, if_neg hρ]
    exact mul_nonneg (by positivity) (zetaGlobalPoissonSummand_nonneg (by simpa using (show 1 ≤ T by linarith)) ρ)

/-- An explicit upper bound for the complete xi Poisson mass on the real axis. -/
theorem logDeriv_xi_real_le {T : ℝ} (hT : 2 ≤ T) :
    (logDeriv riemannXi (T : ℂ)).re ≤ 2+Real.log T/2 := by
  have hT1 : 1 < T := by linarith
  have hT0 : 0 < T := by linarith
  have hprime := neg_logDeriv_riemannZeta_three_height_nonneg hT1 0
  simp only [Complex.ofReal_zero, mul_zero, add_zero] at hprime
  have hpsi := re_digamma_le_log_normSq_div_re (z := (T : ℂ)/2)
    (by simpa using half_pos hT0)
  have he : Complex.normSq ((T : ℂ)/2)/((T : ℂ)/2).re = T/2 := by
    simp only [Complex.normSq_apply, Complex.div_ofNat_re, Complex.div_ofNat_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_div]
    field_simp
    ring
  rw [he] at hpsi
  have hlog := Real.log_le_log (half_pos hT0) (show T/2 ≤ T by linarith)
  have hpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hbudget := congrArg Complex.re (zeta_global_complex_budget (s := (T : ℂ)) (by simpa using hT1))
  have hp : (1/((T : ℂ)-1)).re = 1/(T-1) := by norm_cast
  have hi : (1/(T : ℂ)).re = 1/T := by norm_cast
  simp only [zetaGlobalRegularCorrection, Complex.add_re, Complex.sub_re, Complex.neg_re,
    Complex.div_ofNat_re, Complex.log_re, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, hp, hi] at hbudget
  have h1 : 1/(T-1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  have h2 : 1/T ≤ 1 := (div_le_one hT0).mpr (by linarith)
  simp only [Complex.neg_re] at hprime
  linarith

/-- A quantitative bound for the complete high-zero tail at every `T >= 2`. -/
theorem value_le {T : ℝ} (hT : 2 ≤ T) : value T ≤ (8+2*Real.log T)/T := by
  have hT1 : 1 ≤ (T : ℂ).re := by simpa using (show 1 ≤ T by linarith)
  have hh := (summable_term T).tsum_le_tsum (term_le_poisson hT)
    ((summable_zetaGlobalPoissonSummand hT1).mul_left (4/T))
  rw [tsum_mul_left, tsum_zetaGlobalPoissonSummand hT1] at hh
  have hb := mul_le_mul_of_nonneg_left (logDeriv_xi_real_le hT) (show 0 ≤ 4/T by positivity)
  apply hh.trans
  convert! hb using 1
  ring

end
end RiemannGaussian.RosserSchoenfeldZeroTail
