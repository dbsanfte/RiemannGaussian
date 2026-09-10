/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaStechkinComparison
import RiemannGaussian.ZetaHorizontalBudget

/-!
# Stechkin comparison for the actual complete zeta budget

The full zero sum is paired using the genuine critical reflection,
including the exact analytic multiplicities. All pairs are nonnegative
after a partial horizontal subtraction. A selected right-half pair keeps
its full original source, while the completion allowance is reduced by
`1 - zetaStechkinWeight sigma`.

The complete signed prime work remains explicit. This classical comparison
improves the analytic allowance; it does not prove the arithmetic floor
required for RH.
-/

namespace RiemannGaussian
noncomputable section
open Complex

/-- The actual nonnegative prime amplitude after partial subtraction. -/
def zetaStechkinPrimeWeight (σ : ℝ) (m : ℕ) : ℝ :=
  zetaPhasePrimeWeight σ m -
    zetaStechkinWeight σ * zetaPhasePrimeWeight (zetaStechkinAbscissa σ) m

/-- Each genuine prime-power coefficient retains its sign. -/
theorem zetaStechkinPrimeWeight_nonneg {σ : ℝ} (hσ : 1 ≤ σ) (m : ℕ) :
    0 ≤ zetaStechkinPrimeWeight σ m := by
  have h := zetaHorizontalPrimeWeight_nonneg (lt_zetaStechkinAbscissa hσ).le m
  have hc := (zetaStechkinWeight_mem_Ioo hσ).2.le
  have hp := zetaPhasePrimeWeight_nonneg (zetaStechkinAbscissa σ) m
  unfold zetaStechkinPrimeWeight
  unfold zetaHorizontalPrimeWeight at h
  nlinarith

/-- Every original nonnegative arithmetic floor transfers with the
explicit factor `1-c`; the complete new prime weight also stays below
the original one. -/
theorem zetaStechkinPrimeWeight_bounds {σ : ℝ} (hσ : 1 ≤ σ) (m : ℕ) :
    (1 - zetaStechkinWeight σ) * zetaPhasePrimeWeight σ m ≤ zetaStechkinPrimeWeight σ m ∧
      zetaStechkinPrimeWeight σ m ≤ zetaPhasePrimeWeight σ m := by
  have h := zetaHorizontalPrimeWeight_nonneg (lt_zetaStechkinAbscissa hσ).le m
  have hc := (zetaStechkinWeight_mem_Ioo hσ).1.le
  have hp := zetaPhasePrimeWeight_nonneg (zetaStechkinAbscissa σ) m
  unfold zetaHorizontalPrimeWeight at h
  unfold zetaStechkinPrimeWeight
  constructor <;> nlinarith

/-- One half of each genuine reflection pair. Summing over every zero
therefore counts every analytic multiplicity exactly once, including
fixed points on the critical line. -/
def zetaStechkinPoissonSummand (σ y : ℝ) (rho : NontrivialZetaZero) : ℝ :=
  (zetaGlobalPoissonSummand ((σ : ℂ) + I * y) rho +
    zetaGlobalPoissonSummand ((σ : ℂ) + I * y) (NontrivialZetaZero.conjugatePartner rho) -
    zetaStechkinWeight σ *
      (zetaGlobalPoissonSummand ((zetaStechkinAbscissa σ : ℝ) + I * y) rho +
        zetaGlobalPoissonSummand ((zetaStechkinAbscissa σ : ℝ) + I * y)
          (NontrivialZetaZero.conjugatePartner rho))) / 2

/-- The exact elementary pole comparison. -/
def zetaStechkinPoleBudget (σ y : ℝ) : ℝ :=
  (σ - 1) / ((σ - 1) ^ 2 + y ^ 2) - zetaStechkinWeight σ *
    ((zetaStechkinAbscissa σ - 1) / ((zetaStechkinAbscissa σ - 1) ^ 2 + y ^ 2))

private theorem actual_pair (σ y : ℝ) (rho : NontrivialZetaZero) :
    zetaGlobalPoissonSummand ((σ : ℂ) + I * y) rho +
      zetaGlobalPoissonSummand ((σ : ℂ) + I * y) (NontrivialZetaZero.conjugatePartner rho) =
        (analyticZetaZeroMultiplicity rho : ℝ) * stechkinPoissonPair σ rho.1.re (y - rho.1.im) := by
  unfold zetaGlobalPoissonSummand stechkinPoissonPair
  rw [analyticZetaZeroMultiplicity_conjugatePartner, NontrivialZetaZero.conjugatePartner_coe]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, Complex.conj_re,
    Complex.conj_im, zero_mul, mul_zero, one_mul, add_zero, zero_add, sub_zero,
    zero_sub, neg_neg]
  rw [show σ - (1 - rho.1.re) = σ - 1 + rho.1.re by ring]
  ring

/-- The full signed pair retains its exact multiplicity and displacement. -/
theorem zetaStechkinPoissonSummand_eq (σ y : ℝ) (rho : NontrivialZetaZero) :
    zetaStechkinPoissonSummand σ y rho =
      (analyticZetaZeroMultiplicity rho : ℝ) / 2 *
        (stechkinPoissonPair σ rho.1.re (y - rho.1.im) -
          zetaStechkinWeight σ *
            stechkinPoissonPair (zetaStechkinAbscissa σ) rho.1.re (y - rho.1.im)) := by
  unfold zetaStechkinPoissonSummand
  rw [actual_pair, actual_pair]
  ring

/-- Reflection preserves the entire combined summand. -/
theorem zetaStechkinPoissonSummand_partner (σ y : ℝ) (rho : NontrivialZetaZero) :
    zetaStechkinPoissonSummand σ y (NontrivialZetaZero.conjugatePartner rho) =
      zetaStechkinPoissonSummand σ y rho := by
  simp only [zetaStechkinPoissonSummand, NontrivialZetaZero.conjugatePartner_conjugatePartner]
  ring

/-- The complete reflected summand is nonnegative throughout the actual
zero strip. No RH or zero-separation hypothesis is used. -/
theorem zetaStechkinPoissonSummand_nonneg {σ : ℝ} (hσ : 1 ≤ σ)
    (y : ℝ) (rho : NontrivialZetaZero) : 0 ≤ zetaStechkinPoissonSummand σ y rho := by
  rw [zetaStechkinPoissonSummand_eq]
  apply mul_nonneg (by positivity)
  apply sub_nonneg.mpr
  apply stechkinPoissonPair_comparison hσ (lt_zetaStechkinAbscissa hσ).le
    (zetaStechkinAbscissa_quadratic σ).ge
    (NontrivialZetaZero.zero_lt_re rho) (NontrivialZetaZero.re_lt_one rho)
  rw [zetaStechkinWeight_mul hσ]
  linarith

/-- The paired series converges absolutely before its terms are selected. -/
theorem summable_zetaStechkinPoissonSummand {σ : ℝ} (hσ : 1 ≤ σ) (y : ℝ) :
    Summable (zetaStechkinPoissonSummand σ y) := by
  have hs := summable_zetaGlobalPoissonSummand (s := (σ : ℂ) + I * y) (by simpa using hσ)
  have ht := summable_zetaGlobalPoissonSummand
    (s := ((zetaStechkinAbscissa σ : ℝ) : ℂ) + I * y)
      (by simpa using hσ.trans (lt_zetaStechkinAbscissa hσ).le)
  have hsp := NontrivialZetaZero.conjugatePartnerEquiv.summable_iff.mpr hs
  have htp := NontrivialZetaZero.conjugatePartnerEquiv.summable_iff.mpr ht
  exact ((hs.add hsp).sub ((ht.add htp).mul_left (zetaStechkinWeight σ))).div_const 2

/-- Reindexing the full paired series gives exactly the two original
zero masses. In particular no factor of two or critical-line fixed point
is lost in the comparison. -/
theorem tsum_zetaStechkinPoissonSummand {σ : ℝ} (hσ : 1 ≤ σ) (y : ℝ) :
    (∑' rho : NontrivialZetaZero, zetaStechkinPoissonSummand σ y rho) =
      (∑' rho : NontrivialZetaZero, zetaGlobalPoissonSummand ((σ : ℂ) + I * y) rho) -
        zetaStechkinWeight σ * ∑' rho : NontrivialZetaZero,
          zetaGlobalPoissonSummand ((zetaStechkinAbscissa σ : ℝ) + I * y) rho := by
  have hs := summable_zetaGlobalPoissonSummand (s := (σ : ℂ) + I * y) (by simpa using hσ)
  have ht := summable_zetaGlobalPoissonSummand
    (s := ((zetaStechkinAbscissa σ : ℝ) : ℂ) + I * y)
      (by simpa using hσ.trans (lt_zetaStechkinAbscissa hσ).le)
  have hsp := NontrivialZetaZero.conjugatePartnerEquiv.summable_iff.mpr hs
  have htp := NontrivialZetaZero.conjugatePartnerEquiv.summable_iff.mpr ht
  simp only [Function.comp_def, NontrivialZetaZero.conjugatePartnerEquiv_apply] at hsp htp
  unfold zetaStechkinPoissonSummand
  rw [tsum_div_const, (hs.add hsp).tsum_sub ((ht.add htp).mul_left (zetaStechkinWeight σ)),
    hs.tsum_add hsp, tsum_mul_left, ht.tsum_add htp]
  have he (s : ℂ) : (∑' rho : NontrivialZetaZero,
      zetaGlobalPoissonSummand s (NontrivialZetaZero.conjugatePartner rho)) =
        ∑' rho : NontrivialZetaZero, zetaGlobalPoissonSummand s rho :=
    NontrivialZetaZero.conjugatePartnerEquiv.tsum_eq _
  rw [he, he]
  ring

/-- A genuine right-half zero and its distinct reflected partner retain
the full original pole source. Every omitted pair has a proved sign. -/
theorem zetaStechkin_source_le_total (rho : NontrivialZetaZero)
    (hr : 1 / 2 < rho.1.re) {σ : ℝ} (hσ : 1 ≤ σ) :
    (analyticZetaZeroMultiplicity rho : ℝ) / (σ - rho.1.re) ≤
      ∑' z : NontrivialZetaZero, zetaStechkinPoissonSummand σ rho.1.im z := by
  classical
  have hne : rho ≠ NontrivialZetaZero.conjugatePartner rho := by
    intro he
    have hh := congrArg (fun z : NontrivialZetaZero => z.1.re) he
    simp only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_re,
      Complex.one_re, Complex.conj_re] at hh
    linarith
  have hf := (summable_zetaStechkinPoissonSummand hσ rho.1.im).sum_le_tsum
    {rho, NontrivialZetaZero.conjugatePartner rho}
      (fun z _ => zetaStechkinPoissonSummand_nonneg hσ rho.1.im z)
  simp only [Finset.sum_pair hne, zetaStechkinPoissonSummand_partner] at hf
  have hb := stechkinPoissonPair_source hσ (lt_zetaStechkinAbscissa hσ).le
    (zetaStechkinAbscissa_quadratic σ).ge
    (NontrivialZetaZero.zero_lt_re rho) (NontrivialZetaZero.re_lt_one rho)
    (zetaStechkinWeight_mul hσ).le
  have hm := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (analyticZetaZeroMultiplicity rho) :
    (0 : ℝ) ≤ analyticZetaZeroMultiplicity rho)
  rw [zetaStechkinPoissonSummand_eq] at hf
  simp only [sub_self] at hf
  rw [mul_one_div] at hm
  linarith

/-- The complete signed arithmetic work and actual paired zero mass
satisfy an exact budget with the original signed completion retained. -/
theorem zeta_stechkin_real_budget {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    (-logDeriv riemannZeta ((σ : ℂ) + I * y)).re - zetaStechkinWeight σ *
      (-logDeriv riemannZeta ((zetaStechkinAbscissa σ : ℝ) + I * y)).re +
        (∑' rho : NontrivialZetaZero, zetaStechkinPoissonSummand σ y rho) =
      zetaStechkinPoleBudget σ y +
        (zetaGlobalRegularCorrection ((σ : ℂ) + I * y)).re - zetaStechkinWeight σ *
          (zetaGlobalRegularCorrection ((zetaStechkinAbscissa σ : ℝ) + I * y)).re := by
  have ht := hσ.trans (lt_zetaStechkinAbscissa hσ.le)
  have hs := zeta_global_real_budget (s := (σ : ℂ) + I * y) (by simpa using hσ)
  have hh := zeta_global_real_budget
    (s := ((zetaStechkinAbscissa σ : ℝ) : ℂ) + I * y) (by simpa using ht)
  have hp (u : ℝ) : (1 / (((u : ℂ) + I * y) - 1) : ℂ).re =
      (u - 1) / ((u - 1) ^ 2 + y ^ 2) := by simp [Complex.normSq_apply, pow_two]
  rw [hp] at hs hh
  rw [tsum_zetaStechkinPoissonSummand hσ.le]
  unfold zetaStechkinPoleBudget
  linear_combination hs - zetaStechkinWeight σ * hh

/-- The horizontal monotonicity of the actual completion reduces the
whole logarithmic allowance by the subtraction coefficient. -/
theorem zeta_stechkin_regular_le {σ : ℝ} (hσ : 1 ≤ σ) (y : ℝ) :
    (zetaGlobalRegularCorrection ((σ : ℂ) + I * y)).re - zetaStechkinWeight σ *
      (zetaGlobalRegularCorrection ((zetaStechkinAbscissa σ : ℝ) + I * y)).re ≤
        (1 - zetaStechkinWeight σ) * (1 + Real.log (σ + |y|)) := by
  have hmono := re_zetaGlobalRegularCorrection_sub_nonpos
    (by linarith : 0 < σ) (lt_zetaStechkinAbscissa hσ).le y
  simp only [Complex.sub_re] at hmono
  have hreg := re_zetaGlobalRegularCorrection_le
    (s := (σ : ℂ) + I * y) (by simpa using hσ)
  have hc := zetaStechkinWeight_mem_Ioo hσ
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, one_mul, zero_add, sub_self, add_zero] at hreg
  have hcost := mul_le_mul_of_nonneg_left hreg (sub_nonneg.mpr hc.2.le)
  have hreserve := mul_nonpos_of_nonneg_of_nonpos hc.1.le hmono
  nlinarith only [hcost, hreserve]

/-- An unconditional comparison budget with a smaller analytic allowance
and nonnegative complete paired zero mass. -/
theorem zeta_stechkin_real_budget_le {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    (-logDeriv riemannZeta ((σ : ℂ) + I * y)).re - zetaStechkinWeight σ *
      (-logDeriv riemannZeta ((zetaStechkinAbscissa σ : ℝ) + I * y)).re +
        (∑' rho : NontrivialZetaZero, zetaStechkinPoissonSummand σ y rho) ≤
      zetaStechkinPoleBudget σ y +
        (1 - zetaStechkinWeight σ) * (1 + Real.log (σ + |y|)) := by
  rw [zeta_stechkin_real_budget hσ]
  linarith [zeta_stechkin_regular_le hσ.le y]

end
end RiemannGaussian
