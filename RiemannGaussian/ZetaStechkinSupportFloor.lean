/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPhaseHalfLogZeroFree

/-!
# Prime support strengthens every positive Stechkin arithmetic floor

The exact horizontal weight ratio retains its dependence on the prime
power. Starting at two gives a larger transfer factor than `1-c`,
uniformly over all admissible finite or countable real-frequency families.
The full phase-sensitive binomial energy is transferred before its
independent uniform lower bound is used. No phase coefficients change.
-/

namespace RiemannGaussian
noncomputable section
open Complex
open scoped Classical Topology

/-- The exact transfer factor from the first available positive index.
The actual abscissa gap remains inside its exponential. -/
def zetaStechkinSupportFactor (σ : ℝ) (P : ℕ) : ℝ :=
  1 - zetaStechkinWeight σ *
    Real.exp (-(zetaStechkinAbscissa σ - σ) * Real.log P)

/-- The complete actual prime-power weight has this exact factor.
This identity retains the original two Euler weights and their relative
amplitudes, including the zero coefficients at indices zero and one. -/
theorem zetaStechkinPrimeWeight_eq_supportFactor (σ : ℝ) (m : ℕ) :
    zetaStechkinPrimeWeight σ m =
      zetaStechkinSupportFactor σ m * zetaPhasePrimeWeight σ m := by
  have he : Real.exp (-zetaStechkinAbscissa σ * Real.log m) =
      Real.exp (-(zetaStechkinAbscissa σ - σ) * Real.log m) *
        Real.exp (-σ * Real.log m) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold zetaStechkinPrimeWeight zetaStechkinSupportFactor zetaPhasePrimeWeight
  rw [he]
  ring

/-- Later arithmetic support can only improve the exact transfer
factor on the closed Euler half-plane. -/
theorem zetaStechkinSupportFactor_mono {σ : ℝ} (hσ : 1 ≤ σ)
    {P m : ℕ} (hP : 0 < P) (hPm : P ≤ m) :
    zetaStechkinSupportFactor σ P ≤ zetaStechkinSupportFactor σ m := by
  have hlog := Real.log_le_log (by exact_mod_cast hP : (0 : ℝ) < P)
    (by exact_mod_cast hPm : (P : ℝ) ≤ m)
  have hg := sub_pos.mpr (lt_zetaStechkinAbscissa hσ)
  have hexp := Real.exp_le_exp.mpr
    (mul_le_mul_of_nonpos_left hlog (neg_nonpos.mpr hg.le))
  have h := mul_le_mul_of_nonneg_left hexp (zetaStechkinWeight_mem_Ioo hσ).1.le
  unfold zetaStechkinSupportFactor
  linarith

/-- The exact support factor is positive throughout the Euler range.
At index one it is the preceding factor `1-c`. -/
theorem zetaStechkinSupportFactor_pos {σ : ℝ} (hσ : 1 ≤ σ)
    {P : ℕ} (hP : 1 ≤ P) : 0 < zetaStechkinSupportFactor σ P := by
  have h := zetaStechkinSupportFactor_mono hσ (by norm_num : 0 < (1 : ℕ)) hP
  simp only [zetaStechkinSupportFactor, Nat.cast_one, Real.log_one, mul_zero,
    Real.exp_zero, mul_one] at h
  unfold zetaStechkinSupportFactor
  linarith [(zetaStechkinWeight_mem_Ioo hσ).2]

/-- Every support threshold above one gives a strictly larger factor
than the earlier common bound, without an upper bound on the sampling line. -/
theorem one_sub_weight_lt_zetaStechkinSupportFactor {σ : ℝ} (hσ : 1 ≤ σ)
    {P : ℕ} (hP : 1 < P) :
    1 - zetaStechkinWeight σ < zetaStechkinSupportFactor σ P := by
  have hg := sub_pos.mpr (lt_zetaStechkinAbscissa hσ)
  have hl : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast hP)
  have he : Real.exp (-(zetaStechkinAbscissa σ - σ) * Real.log P) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hg) hl
  have h := mul_lt_mul_of_pos_left he (zetaStechkinWeight_mem_Ioo hσ).1
  unfold zetaStechkinSupportFactor
  linarith

/-- The actual Stechkin coefficient is below one half, retaining
strictness in the auxiliary quadratic identity. -/
theorem zetaStechkinWeight_lt_half {σ : ℝ} (hσ : 1 ≤ σ) :
    zetaStechkinWeight σ < (1 / 2 : ℝ) := by
  have hs : 0 < Real.sqrt (1 + 4 * σ ^ 2) := by positivity
  have hsq := Real.sq_sqrt (show 0 ≤ 1 + 4 * σ ^ 2 by positivity)
  have hroot : 2 * σ < Real.sqrt (1 + 4 * σ ^ 2) := by nlinarith
  have he : zetaStechkinWeight σ = σ / Real.sqrt (1 + 4 * σ ^ 2) := by
    unfold zetaStechkinWeight zetaStechkinAbscissa
    congr 1
    ring
  rw [he]
  exact (div_lt_iff₀ hs).mpr (by linarith)

/-- The actual auxiliary line keeps a uniform positive gap on the
sampling range used by the existing binomial energy estimate. -/
theorem ten_seventeenths_le_zetaStechkinGap {σ : ℝ}
    (hσ : 1 ≤ σ) (hσu : σ ≤ 5 / 4) :
    (10 / 17 : ℝ) ≤ zetaStechkinAbscissa σ - σ := by
  have hs := Real.sqrt_nonneg (1 + 4 * σ ^ 2)
  have hsq := Real.sq_sqrt (show 0 ≤ 1 + 4 * σ ^ 2 by positivity)
  unfold zetaStechkinAbscissa
  nlinarith

/-- The auxiliary exponential costs at most two thirds at the first
prime. Both the abscissa gap and the exact logarithmic phase are used. -/
theorem exp_neg_zetaStechkinGap_log_two_le {σ : ℝ}
    (hσ : 1 ≤ σ) (hσu : σ ≤ 5 / 4) :
    Real.exp (-(zetaStechkinAbscissa σ - σ) * Real.log 2) ≤ (2 / 3 : ℝ) := by
  have hg := ten_seventeenths_le_zetaStechkinGap hσ hσu
  have hm := mul_le_mul_of_nonneg_right hg (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hl : Real.log (3 / 2 : ℝ) ≤ (zetaStechkinAbscissa σ - σ) * Real.log 2 := by
    rw [Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    linarith [Real.log_two_gt_d9, Real.log_three_lt_d9]
  have he := Real.exp_le_exp.mpr (neg_le_neg hl)
  rw [Real.exp_neg (Real.log (3 / 2)),
    Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2)] at he
  norm_num at he
  simpa only [neg_mul] using he

/-- Prime support improves the transfer factor to at least two thirds
throughout the relevant sampling range. -/
theorem two_thirds_le_zetaStechkinSupportFactor {σ : ℝ}
    (hσ : 1 ≤ σ) (hσu : σ ≤ 5 / 4) :
    (2 / 3 : ℝ) ≤ zetaStechkinSupportFactor σ 2 := by
  have h := mul_le_mul (zetaStechkinWeight_lt_half hσ).le
    (exp_neg_zetaStechkinGap_log_two_le hσ hσu) (by positivity) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  unfold zetaStechkinSupportFactor
  norm_num only [Nat.cast_ofNat] at *
  linarith

/-- The support improvement is at least six fifths of the previous
transfer factor on the whole relevant sampling range. -/
theorem six_fifths_weight_gap_le_zetaStechkinSupportFactor {σ : ℝ}
    (hσ : 1 ≤ σ) (hσu : σ ≤ 5 / 4) :
    (6 / 5 : ℝ) * (1 - zetaStechkinWeight σ) ≤ zetaStechkinSupportFactor σ 2 := by
  linarith [four_ninths_le_zetaStechkinWeight hσ,
    two_thirds_le_zetaStechkinSupportFactor hσ hσu]

/-- Every actual prime-power amplitude receives the support factor at
two. The exceptional natural indices have zero von Mangoldt coefficient. -/
theorem zetaStechkinPrimeWeight_ge_supportFactor {σ : ℝ} (hσ : 1 ≤ σ) (m : ℕ) :
    zetaStechkinSupportFactor σ 2 * zetaPhasePrimeWeight σ m ≤
      zetaStechkinPrimeWeight σ m := by
  by_cases hm : 2 ≤ m
  · rw [zetaStechkinPrimeWeight_eq_supportFactor]
    exact mul_le_mul_of_nonneg_right
      (zetaStechkinSupportFactor_mono hσ (by norm_num) hm) (zetaPhasePrimeWeight_nonneg σ m)
  · have hm' : m = 0 ∨ m = 1 := by omega
    rcases hm' with rfl | rfl <;> simp [zetaStechkinPrimeWeight, zetaPhasePrimeWeight]

/-- The larger factor transfers the whole actual arithmetic work of
every admissible nonnegative phase kernel. Finite and countable spectra,
with arbitrary real frequencies, are both covered. -/
theorem zetaPhase_stechkin_primeWork_ge_supportFactor {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (hP : ∀ t, 0 ≤ zetaPhaseKernel a ω t)
    {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    zetaStechkinSupportFactor σ 2 *
      (∑' m : ℕ, zetaPhasePrimeWeight σ m * zetaPhaseKernel a ω (y * Real.log m)) ≤
      ∑' m : ℕ, zetaStechkinPrimeWeight σ m * zetaPhaseKernel a ω (y * Real.log m) := by
  rw [← tsum_mul_left]
  apply ((hasSum_zetaPhase_arithmetic (ω := ω) ha hs hσ y).summable.mul_left _).tsum_le_tsum _
    (hasSum_zetaPhase_stechkin_arithmetic (ω := ω) ha hs hσ y).summable
  intro m
  have h := mul_le_mul_of_nonneg_right (zetaStechkinPrimeWeight_ge_supportFactor hσ.le m)
    (hP (y * Real.log m))
  nlinarith only [h]

/-- For every binomial degree and any number of phases, the centered
energy has this ceiling per unit coefficient mass. This bounds the energy
test, not the complete arithmetic work that the test bounds from below. -/
theorem zetaPhase_binomial_energy_le_mass {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (N : ℕ) (θ : ℝ) :
    (∑' n, a n * (2 + 2 * Real.cos (ω n * θ)) ^ N) -
      ((2 * N).choose N : ℝ) * (∑' n, a n) ≤
        ((4 : ℝ) ^ N - ((2 * N).choose N : ℝ)) * (∑' n, a n) := by
  have he := (hasSum_zetaPhase_binomial_energy (ω := ω) ha hs N θ).summable.tsum_le_tsum
    (fun n ↦ mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (show 0 ≤ 2 + 2 * Real.cos (ω n * θ) by
          linarith [Real.neg_one_le_cos (ω n * θ)])
          (show 2 + 2 * Real.cos (ω n * θ) ≤ (4 : ℝ) by
            linarith [Real.cos_le_one (ω n * θ)]) N) (ha n)) (hs.mul_right (4 ^ N))
  rw [tsum_mul_right] at he
  nlinarith only [he]

/-- The full mixed phase energy inherits the improved transfer before
any uniform lower bound is taken. No nonnegative-energy assumption is
required for the displayed centered energy. -/
theorem zetaPhase_stechkin_binomial_energy_support_floor {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (hP : ∀ t, 0 ≤ zetaPhaseKernel a ω t)
    {σ : ℝ} (hσ : 1 < σ) (hσu : σ ≤ 5 / 4) (y : ℝ) :
    zetaStechkinSupportFactor σ 2 *
      ((Real.log 2 * Real.exp (-(4 * σ * Real.log 2)) / 77520) *
        ((∑' n, a n * (2 + 2 * Real.cos (ω n * (y * Real.log 2))) ^ 10) -
          184756 * (∑' n, a n))) ≤
      ∑' m : ℕ, zetaStechkinPrimeWeight σ m * zetaPhaseKernel a ω (y * Real.log m) :=
  (mul_le_mul_of_nonneg_left (zetaPhase_binomial_scaled_energy_le ha hs hP hσ hσu y)
    (zetaStechkinSupportFactor_pos hσ.le (by norm_num)).le).trans
      (zetaPhase_stechkin_primeWork_ge_supportFactor ha hs hP hσ y)

private theorem exact_summable : Summable phaseContactExactFamily :=
  summable_of_phaseContactBudget phaseContactExactFamily_nonneg
    phaseContactExactFamily_hasSum_budget.summable

/-- The unchanged exact family has a stronger independent arithmetic
floor at every height, retaining the full support-dependent factor. -/
theorem phaseContactExact_stechkin_support_floor {σ : ℝ}
    (hσ : 1 < σ) (hσu : σ ≤ 5 / 4) (y : ℝ) :
    zetaStechkinSupportFactor σ 2 *
      ((1 / 40 : ℝ) * Real.exp (-4 * (σ - 1) * Real.log 2)) ≤
      ∑' m : ℕ, zetaStechkinPrimeWeight σ m *
        phaseContactKernel phaseContactExactFamily (y * Real.log m) := by
  have h := zetaPhase_stechkin_primeWork_ge_supportFactor (ω := fun n ↦ (n : ℝ))
    phaseContactExactFamily_nonneg exact_summable
    (by simpa only [zetaPhaseKernel_natCast] using phaseContactExactFamily_kernel_nonneg) hσ y
  simp only [zetaPhaseKernel_natCast] at h
  exact (mul_le_mul_of_nonneg_left
    (phaseContactExact_binomial_scaled_arithmetic_floor hσ hσu y)
    (zetaStechkinSupportFactor_pos hσ.le (by norm_num)).le).trans h

/-- The actual arithmetic floor is at least `exp(-4*(sigma-1)*log 2)/60`
on the whole sampling range, independently of the ordinate. -/
theorem phaseContactExact_stechkin_one_sixtieth_floor {σ : ℝ}
    (hσ : 1 < σ) (hσu : σ ≤ 5 / 4) (y : ℝ) :
    (1 / 60 : ℝ) * Real.exp (-4 * (σ - 1) * Real.log 2) ≤
      ∑' m : ℕ, zetaStechkinPrimeWeight σ m *
        phaseContactKernel phaseContactExactFamily (y * Real.log m) := by
  have h := mul_le_mul_of_nonneg_right
    (two_thirds_le_zetaStechkinSupportFactor hσ.le hσu)
    (show 0 ≤ (1 / 40 : ℝ) * Real.exp (-4 * (σ - 1) * Real.log 2) by positivity)
  have hb := phaseContactExact_stechkin_support_floor hσ hσu y
  nlinarith only [h, hb]

end
end RiemannGaussian
