/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRegularCorrectionVariation

/-!
# A signed zeta budget between two horizontal abscissae

The complete global identity is subtracted before either zero sum or
Gamma correction is estimated. The Gamma difference has a favorable
sign and a height-independent bound. The paired zero contribution is
signed: its exact numerator records where it changes sign. No negative
zero contribution may be discarded when selecting a source.
-/

namespace RiemannGaussian
noncomputable section
open Complex

/-- The literal difference of the two prime-power amplitudes. -/
def zetaHorizontalPrimeWeight (σ τ : ℝ) (m : ℕ) : ℝ :=
  zetaPhasePrimeWeight σ m - zetaPhasePrimeWeight τ m

/-- Increasing the abscissa decreases every actual prime amplitude. -/
theorem zetaHorizontalPrimeWeight_nonneg {σ τ : ℝ} (hστ : σ ≤ τ) (m : ℕ) :
    0 ≤ zetaHorizontalPrimeWeight σ τ m := by
  unfold zetaHorizontalPrimeWeight zetaPhasePrimeWeight
  apply sub_nonneg.mpr
  apply mul_le_mul_of_nonneg_left _ ArithmeticFunction.vonMangoldt_nonneg
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hστ (Real.log_natCast_nonneg m)]

/-- Both original evaluation points and the actual multiplicity remain
inside each signed zero term. -/
def zetaHorizontalPoissonSummand (σ τ y : ℝ) (rho : NontrivialZetaZero) : ℝ :=
  zetaGlobalPoissonSummand ((σ : ℂ) + I * y) rho -
    zetaGlobalPoissonSummand ((τ : ℂ) + I * y) rho

/-- The complete horizontal zero difference is absolutely summable
at each fixed ordinate, before any family of ordinates is considered. -/
theorem summable_zetaHorizontalPoissonSummand {σ τ : ℝ}
    (hσ : 1 ≤ σ) (hτ : 1 ≤ τ) (y : ℝ) :
    Summable (zetaHorizontalPoissonSummand σ τ y) :=
  (summable_zetaGlobalPoissonSummand (by simpa using hσ)).sub
    (summable_zetaGlobalPoissonSummand (by simpa using hτ))

/-- The exact pole-at-one difference, with its ordinate retained. -/
def zetaHorizontalPoleBudget (σ τ y : ℝ) : ℝ :=
  (σ - 1) / ((σ - 1) ^ 2 + y ^ 2) -
    (τ - 1) / ((τ - 1) ^ 2 + y ^ 2)

private theorem pole_bounds {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    0 ≤ (σ - 1) / ((σ - 1) ^ 2 + y ^ 2) ∧
      (σ - 1) / ((σ - 1) ^ 2 + y ^ 2) ≤ 1 / (σ - 1) := by
  have hx : 0 < σ - 1 := sub_pos.mpr hσ
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ (σ - 1) / (σ - 1) ^ 2 :=
      div_le_div_of_nonneg_left hx.le (sq_pos_of_pos hx) (by nlinarith [sq_nonneg y])
    _ = _ := by field_simp

/-- The exact elementary pole difference has a uniform height bound. -/
theorem abs_zetaHorizontalPoleBudget_le {σ τ : ℝ}
    (hσ : 1 < σ) (hτ : 1 < τ) (y : ℝ) :
    |zetaHorizontalPoleBudget σ τ y| ≤ 1 / (σ - 1) + 1 / (τ - 1) := by
  unfold zetaHorizontalPoleBudget
  have hs := pole_bounds hσ y
  have ht := pole_bounds hτ y
  exact (abs_sub _ _).trans (by rw [abs_of_nonneg hs.1, abs_of_nonneg ht.1]; linarith)

/-- The complete Gamma difference has no logarithmic height cost. -/
theorem abs_re_zetaGlobalRegularCorrection_sub_le {σ τ : ℝ}
    (hσ : 0 < σ) (hστ : σ ≤ τ) (y : ℝ) :
    |(zetaGlobalRegularCorrection ((σ : ℂ) + I * y) -
      zetaGlobalRegularCorrection ((τ : ℂ) + I * y)).re| ≤ τ - σ := by
  have h := norm_zetaGlobalRegularCorrection_sub_le
    (s := (σ : ℂ) + I * y) (w := (τ : ℂ) + I * y)
    (by simpa using hσ) (by simpa using hσ.trans_le hστ)
  have he : ‖((τ : ℂ) + I * y) - ((σ : ℂ) + I * y)‖ = τ - σ := by
    rw [add_sub_add_right_eq_sub, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hστ)]
  rw [he, norm_sub_rev] at h
  exact (Complex.abs_re_le_norm _).trans h

/-- The complete signed arithmetic and zero differences have an exact
common budget. The two original global zero sums are subtracted before
their full paired series is used. -/
theorem zeta_horizontal_real_budget {σ τ : ℝ}
    (hσ : 1 < σ) (hτ : 1 < τ) (y : ℝ) :
    (-logDeriv riemannZeta ((σ : ℂ) + I * y)).re -
      (-logDeriv riemannZeta ((τ : ℂ) + I * y)).re +
        (∑' rho : NontrivialZetaZero, zetaHorizontalPoissonSummand σ τ y rho) =
      zetaHorizontalPoleBudget σ τ y +
        (zetaGlobalRegularCorrection ((σ : ℂ) + I * y) -
          zetaGlobalRegularCorrection ((τ : ℂ) + I * y)).re := by
  have hs := zeta_global_real_budget (s := (σ : ℂ) + I * y) (by simpa using hσ)
  have ht := zeta_global_real_budget (s := (τ : ℂ) + I * y) (by simpa using hτ)
  have hp (u : ℝ) : (1 / (((u : ℂ) + I * y) - 1) : ℂ).re =
      (u - 1) / ((u - 1) ^ 2 + y ^ 2) := by
    simp [Complex.normSq_apply, pow_two]
  rw [hp] at hs ht
  simp only [zetaHorizontalPoissonSummand]
  rw [(summable_zetaGlobalPoissonSummand (s := (σ : ℂ) + I * y)
    (by simpa using hσ.le)).tsum_sub
      (summable_zetaGlobalPoissonSummand (s := (τ : ℂ) + I * y) (by simpa using hτ.le))]
  simp only [zetaHorizontalPoleBudget, Complex.sub_re]
  linarith

/-- The entire Gamma contribution can be bounded by zero after the
horizontal subtraction. The complete signed zero difference remains. -/
theorem zeta_horizontal_real_budget_le {σ τ : ℝ}
    (hσ : 1 < σ) (hστ : σ ≤ τ) (y : ℝ) :
    (-logDeriv riemannZeta ((σ : ℂ) + I * y)).re -
      (-logDeriv riemannZeta ((τ : ℂ) + I * y)).re +
        (∑' rho : NontrivialZetaZero, zetaHorizontalPoissonSummand σ τ y rho) ≤
      zetaHorizontalPoleBudget σ τ y := by
  rw [zeta_horizontal_real_budget hσ (hσ.trans_le hστ)]
  exact add_le_of_nonpos_right
    (re_zetaGlobalRegularCorrection_sub_nonpos (by linarith) hστ y)

/-- Cancellation inside each complete zero block gives a bound uniform
in ordinate. This controls the signed block, not the sum of the absolute
values of its individual zero contributions. -/
theorem abs_tsum_zetaHorizontalPoissonSummand_le {σ τ : ℝ}
    (hσ : 1 < σ) (hστ : σ ≤ τ) (y : ℝ) :
    |∑' rho : NontrivialZetaZero, zetaHorizontalPoissonSummand σ τ y rho| ≤
      1 / (σ - 1) + 1 / (τ - 1) + (τ - σ) +
        (-logDeriv riemannZeta (σ : ℂ)).re + (-logDeriv riemannZeta (τ : ℂ)).re := by
  have hτ := hσ.trans_le hστ
  have he := zeta_horizontal_real_budget hσ hτ y
  have hp := abs_zetaHorizontalPoleBudget_le hσ hτ y
  have hr := abs_re_zetaGlobalRegularCorrection_sub_le (by linarith) hστ y
  have hdσ := norm_neg_logDeriv_riemannZeta_re_le_real_axis hσ y
  have hdτ := norm_neg_logDeriv_riemannZeta_re_le_real_axis hτ y
  rw [Real.norm_eq_abs] at hdσ hdτ
  apply abs_le.mpr
  have hp' := abs_le.mp hp
  have hr' := abs_le.mp hr
  have hdσ' := abs_le.mp hdσ
  have hdτ' := abs_le.mp hdτ
  constructor <;> linarith

/-- The selected zero's positive source is retained exactly after
horizontal subtraction, with its full analytic multiplicity. -/
theorem zetaHorizontalPoissonSummand_at_ordinate (rho : NontrivialZetaZero)
    {σ τ : ℝ} (hσ : 1 ≤ σ) (hτ : 1 ≤ τ) :
    zetaHorizontalPoissonSummand σ τ rho.1.im rho =
      (analyticZetaZeroMultiplicity rho : ℝ) * (τ - σ) /
        ((σ - rho.1.re) * (τ - rho.1.re)) := by
  unfold zetaHorizontalPoissonSummand
  rw [zetaGlobalPoissonSummand_at_ordinate rho hσ,
    zetaGlobalPoissonSummand_at_ordinate rho hτ]
  have hs : σ - rho.1.re ≠ 0 := ne_of_gt (by linarith [NontrivialZetaZero.re_lt_one rho])
  have ht : τ - rho.1.re ≠ 0 := ne_of_gt (by linarith [NontrivialZetaZero.re_lt_one rho])
  field_simp
  ring

/-- The literal sign-changing numerator of every horizontal zero term.
The distant negative zero contributions cannot be omitted merely because
the selected source is positive. -/
theorem zetaHorizontalPoissonSummand_eq_signed_fraction (rho : NontrivialZetaZero)
    {σ τ : ℝ} (hσ : 1 ≤ σ) (hτ : 1 ≤ τ) (y : ℝ) :
    zetaHorizontalPoissonSummand σ τ y rho =
      (analyticZetaZeroMultiplicity rho : ℝ) * (τ - σ) *
        ((σ - rho.1.re) * (τ - rho.1.re) - (y - rho.1.im) ^ 2) /
      ((((σ - rho.1.re) ^ 2 + (y - rho.1.im) ^ 2)) *
        (((τ - rho.1.re) ^ 2 + (y - rho.1.im) ^ 2))) := by
  have hs : 0 < σ - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have ht : 0 < τ - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hsden : (σ - rho.1.re) ^ 2 + (y - rho.1.im) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have htden : (τ - rho.1.re) ^ 2 + (y - rho.1.im) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  unfold zetaHorizontalPoissonSummand zetaGlobalPoissonSummand
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero, one_mul, add_zero, zero_add, sub_zero]
  field_simp
  ring

/-- A genuine zero contributes a strictly positive source at its own
ordinate for every nontrivial horizontal comparison. -/
theorem zetaHorizontalPoissonSummand_pos_at_ordinate (rho : NontrivialZetaZero)
    {σ τ : ℝ} (hσ : 1 ≤ σ) (hστ : σ < τ) :
    0 < zetaHorizontalPoissonSummand σ τ rho.1.im rho := by
  rw [zetaHorizontalPoissonSummand_at_ordinate rho hσ (hσ.trans hστ.le)]
  have hm : (0 : ℝ) < analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  have hs : 0 < σ - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have ht : 0 < τ - rho.1.re := by linarith
  exact div_pos (mul_pos hm (sub_pos.mpr hστ)) (mul_pos hs ht)

/-- The same genuine zero contributes negatively at sufficiently
distant observation ordinates. Removing the Gamma allowance therefore
does not justify assigning a positive sign to the omitted zero background. -/
theorem zetaHorizontalPoissonSummand_neg_of_far (rho : NontrivialZetaZero)
    {σ τ y : ℝ} (hσ : 1 ≤ σ) (hστ : σ < τ)
    (hfar : (σ - rho.1.re) * (τ - rho.1.re) < (y - rho.1.im) ^ 2) :
    zetaHorizontalPoissonSummand σ τ y rho < 0 := by
  rw [zetaHorizontalPoissonSummand_eq_signed_fraction rho hσ (hσ.trans hστ.le)]
  have hm : (0 : ℝ) < analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  have hs : 0 < σ - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have ht : 0 < τ - rho.1.re := by linarith
  apply div_neg_of_neg_of_pos
  · exact mul_neg_of_pos_of_neg (mul_pos hm (sub_pos.mpr hστ)) (sub_neg.mpr hfar)
  · positivity

end
end RiemannGaussian
