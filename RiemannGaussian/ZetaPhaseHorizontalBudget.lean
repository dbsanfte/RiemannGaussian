/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaHorizontalBudget

/-!
# Complete horizontal phase comparisons without a frequency moment

Every summable nonnegative coefficient family and arbitrary real
frequencies satisfy the horizontal comparison. The complete signed zero
block is summed first at each frequency; its cancellation gives a uniform
bound. No logarithmic frequency moment or exchange of the zero and
frequency sums is assumed.

The full Gamma difference is retained as a nonnegative reserve. For a
nonnegative phase kernel, every finite prime-power window and the whole
signed zero response fit within the exact elementary pole difference.
The negative zero background is still present: these theorems do not
establish a source-beating arithmetic estimate or RH.
-/

namespace RiemannGaussian
noncomputable section
open Complex

variable {ω : ℕ → ℝ}

/-- The actual difference of the complete prime-power works has its
convergent phase-series value. Both original arithmetic sums are retained
before taking their difference. -/
theorem hasSum_zetaPhase_horizontal_arithmetic {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    {σ τ : ℝ} (hσ : 1 < σ) (hτ : 1 < τ) (y : ℝ) :
    HasSum (fun m : ℕ => zetaHorizontalPrimeWeight σ τ m *
      zetaPhaseKernel a ω (y * Real.log m))
      (∑' n : ℕ, a n *
        ((-logDeriv riemannZeta ((σ : ℂ) + I * ((ω n * y : ℝ) : ℂ))).re -
          (-logDeriv riemannZeta ((τ : ℂ) + I * ((ω n * y : ℝ) : ℂ))).re)) := by
  have h := (hasSum_zetaPhase_arithmetic (ω := ω) ha hs hσ y).sub
    (hasSum_zetaPhase_arithmetic (ω := ω) ha hs hτ y)
  rw [← (summable_zetaPhase_logDeriv (ω := ω) ha hs hσ y).tsum_sub
    (summable_zetaPhase_logDeriv (ω := ω) ha hs hτ y)] at h
  simpa only [zetaHorizontalPrimeWeight, sub_mul, mul_sub] using h

/-- The complete signed zero block converges against every summable
nonnegative frequency family. No logarithmic frequency moment is required;
the zero sum stays inside each frequency block. -/
theorem summable_zetaPhase_horizontal_zeroMass {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    {σ τ : ℝ} (hσ : 1 < σ) (hστ : σ ≤ τ) (y : ℝ) :
    Summable (fun n : ℕ => a n *
      ∑' rho : NontrivialZetaZero, zetaHorizontalPoissonSummand σ τ (ω n * y) rho) := by
  apply (hs.mul_right (1 / (σ - 1) + 1 / (τ - 1) + (τ - σ) +
    (-logDeriv riemannZeta (σ : ℂ)).re + (-logDeriv riemannZeta (τ : ℂ)).re)).of_norm_bounded
  intro n
  rw [norm_mul, Real.norm_eq_abs (a n), abs_of_nonneg (ha n), Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (abs_tsum_zetaHorizontalPoissonSummand_le hσ hστ (ω n * y)) (ha n)

/-- The full signed elementary pole differences converge independently
of the frequency magnitudes. -/
theorem summable_zetaPhase_horizontal_pole {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    {σ τ : ℝ} (hσ : 1 < σ) (hτ : 1 < τ) (y : ℝ) :
    Summable (fun n : ℕ => a n * zetaHorizontalPoleBudget σ τ (ω n * y)) := by
  apply (hs.mul_right (1 / (σ - 1) + 1 / (τ - 1))).of_norm_bounded
  intro n
  rw [norm_mul, Real.norm_eq_abs (a n), abs_of_nonneg (ha n), Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (abs_zetaHorizontalPoleBudget_le hσ hτ (ω n * y)) (ha n)

/-- The complete favorable Gamma reserve is summable with coefficient
summability alone. Its original difference remains inside each summand. -/
theorem summable_zetaPhase_horizontal_gamma {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    {σ τ : ℝ} (hσ : 0 < σ) (hστ : σ ≤ τ) (y : ℝ) :
    Summable (fun n : ℕ => a n *
      (zetaGlobalRegularCorrection ((τ : ℂ) + I * ((ω n * y : ℝ) : ℂ)) -
        zetaGlobalRegularCorrection ((σ : ℂ) + I * ((ω n * y : ℝ) : ℂ))).re) := by
  apply (hs.mul_right (τ - σ)).of_norm_bounded
  intro n
  rw [norm_mul, Real.norm_eq_abs (a n), abs_of_nonneg (ha n), Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (ha n)
  simpa only [Complex.sub_re, abs_sub_comm] using
    abs_re_zetaGlobalRegularCorrection_sub_le hσ hστ (ω n * y)

/-- Every complete Gamma reserve has a proved favorable sign. -/
theorem zetaPhase_horizontal_gamma_nonneg {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) {σ τ : ℝ} (hσ : 0 < σ) (hστ : σ ≤ τ) (y : ℝ) :
    0 ≤ ∑' n : ℕ, a n *
      (zetaGlobalRegularCorrection ((τ : ℂ) + I * ((ω n * y : ℝ) : ℂ)) -
        zetaGlobalRegularCorrection ((σ : ℂ) + I * ((ω n * y : ℝ) : ℂ))).re := by
  apply tsum_nonneg
  intro n
  apply mul_nonneg (ha n)
  have h := re_zetaGlobalRegularCorrection_sub_nonpos hσ hστ (ω n * y)
  simp only [Complex.sub_re] at h ⊢
  linarith

/-- The exact horizontal phase identity retains the full signed zero
response and the entire favorable Gamma reserve, for arbitrary real
frequencies and finite or infinite summable coefficient families. -/
theorem zetaPhase_horizontal_primeWork_add_zeroMass_add_gamma_eq {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    {σ τ : ℝ} (hσ : 1 < σ) (hστ : σ ≤ τ) (y : ℝ) :
    (∑' m : ℕ, zetaHorizontalPrimeWeight σ τ m *
      zetaPhaseKernel a ω (y * Real.log m)) +
      (∑' n : ℕ, a n * ∑' rho : NontrivialZetaZero,
        zetaHorizontalPoissonSummand σ τ (ω n * y) rho) +
      (∑' n : ℕ, a n *
        (zetaGlobalRegularCorrection ((τ : ℂ) + I * ((ω n * y : ℝ) : ℂ)) -
          zetaGlobalRegularCorrection ((σ : ℂ) + I * ((ω n * y : ℝ) : ℂ))).re) =
      ∑' n : ℕ, a n * zetaHorizontalPoleBudget σ τ (ω n * y) := by
  have hτ := hσ.trans_le hστ
  rw [(hasSum_zetaPhase_horizontal_arithmetic (ω := ω) ha hs hσ hτ y).tsum_eq]
  have hD : Summable (fun n : ℕ => a n *
      ((-logDeriv riemannZeta ((σ : ℂ) + I * ((ω n * y : ℝ) : ℂ))).re -
        (-logDeriv riemannZeta ((τ : ℂ) + I * ((ω n * y : ℝ) : ℂ))).re)) := by
    simpa only [mul_sub] using (summable_zetaPhase_logDeriv (ω := ω) ha hs hσ y).sub
      (summable_zetaPhase_logDeriv (ω := ω) ha hs hτ y)
  have hZ := summable_zetaPhase_horizontal_zeroMass (ω := ω) ha hs hσ hστ y
  have hG := summable_zetaPhase_horizontal_gamma (ω := ω) ha hs (by linarith) hστ y
  rw [← hD.tsum_add hZ, ← (hD.add hZ).tsum_add hG]
  apply tsum_congr
  intro n
  have h := zeta_horizontal_real_budget hσ hτ (ω n * y)
  simp only [Complex.sub_re] at h ⊢
  linear_combination a n * h

/-- Every finite prime-power window and the complete signed zero
response fit inside the exact elementary pole budget, with the whole
nonnegative Gamma reserve retained on the left. No frequency moment or
local analytic allowance is required. -/
theorem zetaPhase_horizontal_finite_primeWork_add_zeroMass_add_gamma_le {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hp : ∀ t, 0 ≤ zetaPhaseKernel a ω t)
    {σ τ : ℝ} (hσ : 1 < σ) (hστ : σ ≤ τ) (y : ℝ) (S : Finset ℕ) :
    (∑ m ∈ S, zetaHorizontalPrimeWeight σ τ m *
      zetaPhaseKernel a ω (y * Real.log m)) +
      (∑' n : ℕ, a n * ∑' rho : NontrivialZetaZero,
        zetaHorizontalPoissonSummand σ τ (ω n * y) rho) +
      (∑' n : ℕ, a n *
        (zetaGlobalRegularCorrection ((τ : ℂ) + I * ((ω n * y : ℝ) : ℂ)) -
          zetaGlobalRegularCorrection ((σ : ℂ) + I * ((ω n * y : ℝ) : ℂ))).re) ≤
      ∑' n : ℕ, a n * zetaHorizontalPoleBudget σ τ (ω n * y) := by
  have hf := (hasSum_zetaPhase_horizontal_arithmetic (ω := ω) ha hs hσ
    (hσ.trans_le hστ) y).summable.sum_le_tsum S
      (fun m _ => mul_nonneg (zetaHorizontalPrimeWeight_nonneg hστ m) (hp _))
  rw [← zetaPhase_horizontal_primeWork_add_zeroMass_add_gamma_eq ha hs hσ hστ y]
  linarith

end
end RiemannGaussian
