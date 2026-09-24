/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovFordCoefficientBudget

/-!
# Ford's closed coefficient with the published constants

The exact cutoff floor(1.97*k) pays the original `2.055`, `5.91` and
`9.7278` constants. Combining this coefficient bound with the closed defect
bound yields the actual homogeneous moment estimate on the complete
published order interval, with paper index `n = J + 1`.

The scalar coefficient bound is unconditional. The actual moment theorem
still requires the explicit, unproved dense short-prime supply. It does not
assert unconditional reproduction of Lemma 3.6 or a new zeta region.

Source: Kevin Ford, *Vinogradov's integral and bounds for the Riemann
zeta function*, Lemma 3.6, arXiv:1910.08209v1.
-/

namespace RiemannGaussian.VinogradovFordClosedCoefficient
noncomputable section
open VinogradovFordSelectedIteration VinogradovFordCoefficientScale
open VinogradovFordCoefficientStep VinogradovFordEarlyDefect
open VinogradovFordCoefficientBudget

/-- The last early step used by the published coefficient argument. -/
def earlyLength (k : ℕ) : ℕ := ⌊(197 / 100 : ℝ) * (k : ℝ)⌋₊

/-- Both exact inequalities around the early cutoff are retained. -/
theorem earlyLength_bounds (k : ℕ) :
    (earlyLength k : ℝ) ≤ (197 / 100) * (k : ℝ) ∧
      (197 / 100) * (k : ℝ) < (earlyLength k : ℝ) + 1 := by
  exact ⟨Nat.floor_le (by positivity), Nat.lt_floor_add_one _⟩

/-- The paper's lower order bound is beyond the early cutoff. -/
theorem earlyLength_le {k J : ℕ} (hk : 1000 ≤ k) (hJ : 2 * k ≤ J + 1) :
    earlyLength k ≤ J := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hJR : 2 * (k : ℝ) ≤ (J : ℝ) + 1 := by exact_mod_cast hJ
  have hb := (earlyLength_bounds k).1
  have ht : (earlyLength k : ℝ) ≤ (J : ℝ) := by linarith
  exact_mod_cast ht

/-- Nonnegative defect bounds every budget by the same common prefactor. -/
theorem budget_le {k : ℕ} (hk : 1000 ≤ k) (J : ℕ) :
    defectBudget k J ≤ coefficientScale k ^ ((k : ℝ) ^ 2 / 2) := by
  apply Real.rpow_le_rpow_of_exponent_le (coefficientScale_ge_one hk)
  have hd := (selectedDefect_bounds (by omega : 26 ≤ k) J).1
  linarith

/-- The first power in the published closed coefficient, with exact floor. -/
theorem first_factor_le {k : ℕ} (hk : 1000 ≤ k) (J : ℕ) :
    coefficientScale k ^ ((k : ℝ) ^ 2 / 2) *
      (k : ℝ) ^ (3 * (k : ℝ) * ((J : ℝ) - (earlyLength k : ℝ))) ≤
        (k : ℝ) ^ ((411 / 200) * (k : ℝ) ^ 3 -
          (591 / 100) * (k : ℝ) ^ 2 + 3 * ((J : ℝ) + 1) * (k : ℝ)) := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  unfold coefficientScale
  rw [← Real.rpow_mul hkpos.le, ← Real.rpow_add hkpos]
  apply Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ k)
  have hb := (earlyLength_bounds k).2.le
  have hm := mul_le_mul_of_nonneg_left hb (show (0 : ℝ) ≤ 3 * (k : ℝ) by positivity)
  nlinarith only [hm]

/-- The exact early cutoff pays the original 9.7278*k^3 packet reserve. -/
theorem width_reserve {k : ℕ} (hk : 1000 ≤ k) :
    (48639 / 5000) * (k : ℝ) ^ 3 ≤
      ((earlyLength k : ℝ) + 1) * (k : ℝ) ^ 2 +
        2 * (k : ℝ) * ((earlyLength k : ℝ) ^ 2 + (earlyLength k : ℝ)) := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hb := (earlyLength_bounds k).2.le
  have hp := mul_nonneg (sub_nonneg.mpr hb)
    (show 0 ≤ (earlyLength k : ℝ) + 1 + (197 / 100) * (k : ℝ) - 1 by
      linarith [Nat.cast_nonneg (α := ℝ) (earlyLength k)])
  have hs : ((197 / 100) * (k : ℝ)) ^ 2 - (197 / 100) * (k : ℝ) ≤
      (earlyLength k : ℝ) ^ 2 + (earlyLength k : ℝ) := by nlinarith only [hp]
  have h1 := mul_le_mul_of_nonneg_right hb (sq_nonneg (k : ℝ))
  have h2 := mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ 2 * (k : ℝ) by positivity)
  have h3 := mul_nonneg (show (0 : ℝ) ≤ (k : ℝ) / 250 - 197 / 50 by linarith)
    (sq_nonneg (k : ℝ))
  nlinarith only [h1, h2, h3]

/-- The entire late width exponent fits the published second power. -/
theorem second_factor_le {k : ℕ} (hk : 1000 ≤ k) (J : ℕ) :
    (53 / 50 : ℝ) ^ (((J : ℝ) - (earlyLength k : ℝ)) * (k : ℝ) ^ 2 +
      2 * (k : ℝ) * ((J : ℝ) ^ 2 + (J : ℝ) -
        (earlyLength k : ℝ) ^ 2 - (earlyLength k : ℝ))) ≤
      (53 / 50 : ℝ) ^ (((J : ℝ) + 1) * (k : ℝ) ^ 2 +
        2 * (k : ℝ) * ((J : ℝ) ^ 2 + (J : ℝ)) - (48639 / 5000) * (k : ℝ) ^ 3) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 53 / 50)
  have hh := width_reserve hk
  nlinarith only [hh]

/-- Ford's original closed coefficient with all numerical constants intact.
This is an unconditional estimate on the actual recursive coefficient. -/
theorem selected_coefficient_bound {k J : ℕ} (hk : 1000 ≤ k)
    (hJ : 2 * k ≤ J + 1) :
    selectedCoefficient k (3 / 50) J ≤
      (k : ℝ) ^ ((411 / 200) * (k : ℝ) ^ 3 -
        (591 / 100) * (k : ℝ) ^ 2 + 3 * ((J : ℝ) + 1) * (k : ℝ)) *
      (53 / 50 : ℝ) ^ (((J : ℝ) + 1) * (k : ℝ) ^ 2 +
        2 * (k : ℝ) * ((J : ℝ) ^ 2 + (J : ℝ)) - (48639 / 5000) * (k : ℝ) ^ 3) := by
  have hh := coefficient_after_early hk (earlyLength_bounds k).1 (earlyLength_le hk hJ)
  have hb := mul_le_mul_of_nonneg_right (budget_le hk J) (lateCost_nonneg k (earlyLength k) J)
  refine (hh.trans hb).trans ?_
  unfold lateCost
  rw [← mul_assoc]
  exact mul_le_mul (first_factor_le hk J) (second_factor_le hk J)
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 53 / 50) _) (by positivity)

/-- The complete numerical Ford moment bound, retaining only the explicit
short-prime supply as an unproved arithmetic input. -/
theorem selected_moment_closed {k J : ℕ} (hk : 1000 ≤ k)
    (hlower : 2 * k ≤ J + 1)
    (hupper : (J : ℝ) + 1 ≤ ((k : ℝ) / 2) *
      (1 / 2 + Real.log (3 * (k : ℝ) / 8)) + 1)
    (hsupply : VinogradovFordGlobalStep.ShortPrimeSupply k (3 / 50))
    {P : ℕ} (hP : 1 ≤ P) :
    VinogradovMeanValue.meanValue (VinogradovFordMomentSequence.order k J) k P ≤
      ((k : ℝ) ^ ((411 / 200) * (k : ℝ) ^ 3 -
        (591 / 100) * (k : ℝ) ^ 2 + 3 * ((J : ℝ) + 1) * (k : ℝ)) *
      (53 / 50 : ℝ) ^ (((J : ℝ) + 1) * (k : ℝ) ^ 2 +
        2 * (k : ℝ) * ((J : ℝ) ^ 2 + (J : ℝ)) - (48639 / 5000) * (k : ℝ) ^ 3)) *
      (P : ℝ) ^ VinogradovFordScales.sourceExponent k
        (VinogradovFordMomentSequence.order k J)
        ((3 / 8) * (k : ℝ) ^ 2 *
          Real.exp (1 / 2 - 2 * ((J : ℝ) + 1) / k + 169 / (100 * (k : ℝ)))) := by
  have hh := VinogradovFordClosedDefect.selected_moment_closed_defect hk hupper
    (by norm_num : (0 : ℝ) < 3 / 50) (by norm_num : (3 / 50 : ℝ) ≤ 1 / 2) hsupply hP
  exact hh.trans (mul_le_mul_of_nonneg_right (selected_coefficient_bound hk hlower)
    (Real.rpow_nonneg (Nat.cast_nonneg P) _))


end
end RiemannGaussian.VinogradovFordClosedCoefficient
