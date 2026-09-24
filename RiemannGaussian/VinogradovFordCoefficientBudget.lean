/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovFordCoefficientStep

/-!
# Telescoping Ford's original moment coefficient

The initial factorial and every early coefficient step fit a common defect
budget. The later packet factors are multiplied exactly, including stopped
steps, before any numerical endpoint bound is applied. The estimates concern
the actual recursive coefficient and have no prime-supply premise.

Source: Kevin Ford, *Vinogradov's integral and bounds for the Riemann
zeta function*, proof of Lemma 3.6, arXiv:1910.08209v1.
-/

namespace RiemannGaussian.VinogradovFordCoefficientBudget
noncomputable section
open VinogradovFordSelectedIteration VinogradovFordCoefficientScale
open VinogradovFordCoefficientStep VinogradovFordEarlyDefect

/-- The defect budget used to telescope the original coefficient. -/
def defectBudget (k j : ℕ) : ℝ :=
  coefficientScale k ^ ((k : ℝ) ^ 2 / 2 - selectedDefect k j)

/-- The original scale is strictly positive. -/
theorem scale_pos {k : ℕ} (hk : 1000 ≤ k) : 0 < coefficientScale k :=
  lt_of_lt_of_le zero_lt_one (coefficientScale_ge_one hk)

/-- Every defect budget is positive. -/
theorem budget_pos {k : ℕ} (hk : 1000 ≤ k) (j : ℕ) : 0 < defectBudget k j :=
  Real.rpow_pos_of_pos (scale_pos hk) _

/-- One selected decrease telescopes exactly inside the budget. -/
theorem budget_step {k : ℕ} (hk : 1000 ≤ k) (j : ℕ) :
    defectBudget k j * coefficientScale k ^
      (selectedDefect k j - selectedDefect k (j + 1)) = defectBudget k (j + 1) := by
  unfold defectBudget
  rw [← Real.rpow_add (scale_pos hk)]
  congr 1
  ring

/-- The initial factorial fits the initial defect budget. -/
theorem initial_coefficient_le {k : ℕ} (hk : 1000 ≤ k) :
    selectedCoefficient k (3 / 50) 0 ≤ defectBudget k 0 := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hf : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast Nat.factorial_le_pow k
  change (k.factorial : ℝ) ≤ _
  refine hf.trans ?_
  unfold defectBudget selectedDefect coefficientScale
  have he : (k : ℝ) ^ 2 / 2 - (k : ℝ) * ((k : ℝ) - 1) / 2 = (k : ℝ) / 2 := by ring
  rw [he, ← Real.rpow_mul hkpos.le, ← Real.rpow_natCast (k : ℝ) k]
  apply Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ k)
  nlinarith [mul_nonneg hkpos.le (show 0 ≤ (k : ℝ) - 1000 by linarith)]

/-- The entire early coefficient prefix is paid by the telescoping defect. -/
theorem early_coefficient_le {k J : ℕ} (hk : 1000 ≤ k)
    (hJ : (J : ℝ) ≤ (197 / 100) * (k : ℝ)) :
    selectedCoefficient k (3 / 50) J ≤ defectBudget k J := by
  induction J with
  | zero => exact initial_coefficient_le hk
  | succ j ih =>
      have hj : (j : ℝ) + 1 ≤ (197 / 100) * (k : ℝ) := by simpa only [Nat.cast_add_one] using hJ
      have ha : (k : ℝ) - 1 < selectedDefect k j := by linarith [early_active hk hj]
      have hi := ih (show (j : ℝ) ≤ (197 / 100) * (k : ℝ) by linarith)
      rw [selectedCoefficient, if_pos ha]
      calc
        _ ≤ selectedCoefficient k (3 / 50) j * coefficientScale k ^
            (selectedDefect k j - selectedDefect k (j + 1)) :=
          mul_le_mul_of_nonneg_left (early_step_le hk hj)
            (selectedCoefficient_pos (by omega : 0 < k) (by norm_num : (0 : ℝ) < 3 / 50) j).le
        _ ≤ defectBudget k j * coefficientScale k ^
            (selectedDefect k j - selectedDefect k (j + 1)) :=
          mul_le_mul_of_nonneg_right hi (Real.rpow_nonneg (scale_pos hk).le _)
        _ = defectBudget k (j + 1) := budget_step hk j

/-- Every original coefficient step retains both independent costs. -/
theorem coefficient_step_le {k : ℕ} (hk : 1000 ≤ k) (j : ℕ) :
    selectedCoefficient k (3 / 50) (j + 1) ≤ selectedCoefficient k (3 / 50) j *
      (packetCost k j * coefficientScale k ^
        (selectedDefect k j - selectedDefect k (j + 1))) := by
  have hc := (selectedCoefficient_pos (by omega : 0 < k)
    (by norm_num : (0 : ℝ) < 3 / 50) j).le
  by_cases ha : (k : ℝ) - 1 < selectedDefect k j
  · rw [selectedCoefficient, if_pos ha]
    exact mul_le_mul_of_nonneg_left (step_le_product hk j) hc
  · have hd : selectedDefect k (j + 1) = selectedDefect k j := by
      rw [selectedDefect, if_neg ha]
    rw [selectedCoefficient, if_neg ha, hd, sub_self, Real.rpow_zero, mul_one]
    exact le_mul_of_one_le_right hc (packetCost_ge_one hk j)

/-- The exact remaining packet product in real exponents. -/
def lateCost (k T J : ℕ) : ℝ :=
  (k : ℝ) ^ (3 * (k : ℝ) * ((J : ℝ) - (T : ℝ))) *
    (53 / 50 : ℝ) ^ (((J : ℝ) - (T : ℝ)) * (k : ℝ) ^ 2 +
      2 * (k : ℝ) * ((J : ℝ) ^ 2 + (J : ℝ) - (T : ℝ) ^ 2 - (T : ℝ)))

/-- Every late packet product is nonnegative. -/
theorem lateCost_nonneg (k T J : ℕ) : 0 ≤ lateCost k T J := by
  unfold lateCost
  positivity

/-- No packet is paid at the starting index. -/
theorem lateCost_self (k T : ℕ) : lateCost k T T = 1 := by
  simp [lateCost]

/-- Exact coercion of the original packet exponents. -/
theorem packetCost_rpow (k j : ℕ) :
    packetCost k j = (k : ℝ) ^ (3 * (k : ℝ)) *
      (53 / 50 : ℝ) ^ (4 * (k : ℝ) * ((j : ℝ) + 1) + (k : ℝ) ^ 2) := by
  unfold packetCost
  rw [← Real.rpow_natCast (k : ℝ) (3 * k),
    ← Real.rpow_natCast (53 / 50 : ℝ) (4 * VinogradovFordMomentSequence.order k j + k ^ 2)]
  unfold VinogradovFordMomentSequence.order
  push_cast
  congr 2
  ring

/-- The exact late product inserts one original packet. -/
theorem lateCost_step {k : ℕ} (hk : 1000 ≤ k) (T j : ℕ) :
    lateCost k T (j + 1) = lateCost k T j * packetCost k j := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  rw [packetCost_rpow]
  unfold lateCost
  rw [mul_mul_mul_comm, ← Real.rpow_add hkpos,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 53 / 50)]
  push_cast
  congr 1 <;> congr 1 <;> ring

/-- The actual late coefficient is bounded by the exact packet product
and the same telescoping defect budget. -/
theorem coefficient_after_early {k T J : ℕ} (hk : 1000 ≤ k)
    (hT : (T : ℝ) ≤ (197 / 100) * (k : ℝ)) (hTJ : T ≤ J) :
    selectedCoefficient k (3 / 50) J ≤ defectBudget k J * lateCost k T J := by
  induction J, hTJ using Nat.le_induction with
  | base => simpa only [lateCost_self, mul_one] using early_coefficient_le hk hT
  | succ j hj ih =>
      have hfac : 0 ≤ packetCost k j * coefficientScale k ^
          (selectedDefect k j - selectedDefect k (j + 1)) := by
        exact mul_nonneg (le_trans zero_le_one (packetCost_ge_one hk j))
          (Real.rpow_nonneg (scale_pos hk).le _)
      refine (coefficient_step_le hk j).trans ((mul_le_mul_of_nonneg_right ih hfac).trans_eq ?_)
      rw [lateCost_step hk]
      calc
        _ = (defectBudget k j * coefficientScale k ^
            (selectedDefect k j - selectedDefect k (j + 1))) *
              (lateCost k T j * packetCost k j) := by ring
        _ = _ := by rw [budget_step hk]

end
end RiemannGaussian.VinogradovFordCoefficientBudget
