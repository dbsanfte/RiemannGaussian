/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszRectangleMaskError

/-!
# A discrete lower bound for the concrete rectangle's source weight

The finite integer rectangle suffices. No continuum integral, numerical
coefficient, or optimal family is used to certify the margin.
-/

namespace RiemannGaussian.ZetaRieszSkewAllocation
noncomputable section
open scoped BigOperators Classical
open ZetaRieszWideOwnerAudit

/-- The exact positive weight after all three factorial derivative
phases are normalized; the h+1 derivative cancels only its own factor. -/
def rectangleSourceWeight (u : ℝ) (N j h : ℕ) : ℝ :=
  (N + 1 : ℝ) /
    (u * SquarefreeVaughanLogSource.length u N * j * (N + 1 - j - h : ℕ))

theorem rectangleSourceWeight_nonneg {u : ℝ} (hu : 0 ≤ u) (N j h : ℕ) :
    0 ≤ rectangleSourceWeight u N j h := by
  have hL := (SquarefreeVaughanLogSource.length_pos u N).le
  unfold rectangleSourceWeight
  positivity

/-- A deliberately crude pointwise density on the whole concrete box. -/
theorem rectangleSourceWeight_lower {u : ℝ} (hu : 1 / 2 < u) (huU : u ≤ radiusCeiling)
    {N j h : ℕ} (hN : 1000 ≤ N) (hh : h ∈ rectangleOrders N j) :
    5 / (N : ℝ) ^ 2 ≤ rectangleSourceWeight u N j h := by
  have hNp : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNp
  have hu0 : 0 < u := by linarith
  have hL := SquarefreeVaughanLogSource.length_pos u N
  obtain ⟨hj, hℓ, _⟩ := rectangle_phase_orders (by omega : 20 ≤ N) hh
  have hjp : 0 < j := by omega
  have hℓp : 0 < N + 1 - j - h := by omega
  have hjr : (0 : ℝ) < j := by exact_mod_cast hjp
  have hℓr : (0 : ℝ) < (N + 1 - j - h : ℕ) := by exact_mod_cast hℓp
  have hsum : (j : ℝ) + (N + 1 - j - h : ℕ) ≤ N + 1 := by
    have hr := Finset.mem_range.mp (Finset.mem_filter.mp hh).1
    exact_mod_cast (show j + (N + 1 - j - h) ≤ N + 1 by omega)
  have hquad : 4 * (j : ℝ) * (N + 1 - j - h : ℕ) ≤ (N + 1 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((j : ℝ) - (N + 1 - j - h : ℕ))]
  have hLhi : SquarefreeVaughanLogSource.length u N ≤ (7 / 5 : ℝ) * N := by
    have h := ZetaRieszHeadOrders.length_le_two_log_two hu.le (by omega : 2 ≤ N)
    nlinarith [Real.log_two_lt_d9]
  have huhi : u ≤ 51 / 100 := huU.trans (by norm_num [radiusCeiling])
  have hD : u * SquarefreeVaughanLogSource.length u N ≤ (3 / 4 : ℝ) * N := by
    have hm := mul_le_mul huhi hLhi hL.le (by norm_num : (0 : ℝ) ≤ 51 / 100)
    nlinarith
  unfold rectangleSourceWeight
  apply (div_le_div_iff₀ (sq_pos_of_pos hNr) (by positivity)).mpr
  have h₁ := mul_le_mul_of_nonneg_left hquad (mul_pos hu0 hL).le
  have h₂ := mul_le_mul_of_nonneg_right hD (sq_nonneg (N + 1 : ℝ))
  have hN15 : (15 : ℝ) ≤ N := by exact_mod_cast (show 15 ≤ N by omega)
  have h₃ := mul_nonneg (show 0 ≤ (N : ℝ) - 15 by linarith)
    (show 0 ≤ (N : ℝ) * (N + 1) by positivity)
  nlinarith

private def rectangleJCore (N : ℕ) : Finset ℕ := Finset.Icc (21 * N / 40 + 1) (23 * N / 40)
private def rectangleHCore (N : ℕ) : Finset ℕ := Finset.Icc (N / 100) (N / 25 - 1)

private theorem rectangle_core_counts {N : ℕ} (hN : 1000 ≤ N) :
    N ≤ 21 * (rectangleJCore N).card ∧ N ≤ 35 * (rectangleHCore N).card := by
  simp only [rectangleJCore, rectangleHCore, Nat.card_Icc]
  omega

private theorem rectangle_core_subset {N j h : ℕ} (hN : 1000 ≤ N)
    (hj : j ∈ rectangleJCore N) (hh : h ∈ rectangleHCore N) :
    j ∈ Finset.range (N + 2) ∧ h ∈ rectangleOrders N j := by
  have hj' := Finset.mem_Icc.mp hj
  have hh' := Finset.mem_Icc.mp hh
  have hjlo : 21 * N ≤ 40 * j := by omega
  have hjhi : 40 * j ≤ 23 * N := by omega
  have hhhi : 100 * (h + 1) ≤ 4 * N := by omega
  refine ⟨Finset.mem_range.mpr (by omega), Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by omega), rectangle_mem_owner hjlo hjhi hhhi, hjlo, hjhi, ?_, hhhi⟩⟩
  omega

/-- An exact rational lower bound for the sum over all selected integer
orders. The successor shifts and original owner-order mask are retained. -/
theorem sum_rectangleSourceWeight_lower {u : ℝ}
    (hu : 1 / 2 < u) (huU : u ≤ radiusCeiling) {N : ℕ} (hN : 1000 ≤ N) :
    (1 / 147 : ℝ) ≤ ∑ j ∈ Finset.range (N + 2), ∑ h ∈ rectangleOrders N j,
      rectangleSourceWeight u N j h := by
  have hu0 : 0 ≤ u := by linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨hjcount, hhcount⟩ := rectangle_core_counts hN
  have hjR : (N : ℝ) ≤ 21 * (rectangleJCore N).card := by exact_mod_cast hjcount
  have hhR : (N : ℝ) ≤ 35 * (rectangleHCore N).card := by exact_mod_cast hhcount
  have hprod := mul_le_mul hjR hhR hNr.le (by positivity : (0 : ℝ) ≤ 21 * (rectangleJCore N).card)
  have hmass : (1 / 147 : ℝ) ≤
      ((rectangleJCore N).card : ℝ) * (rectangleHCore N).card * (5 / (N : ℝ) ^ 2) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (sq_pos_of_pos hNr)).mpr
    nlinarith
  apply hmass.trans
  calc
    _ ≤ ∑ j ∈ rectangleJCore N, ∑ h ∈ rectangleHCore N, rectangleSourceWeight u N j h := by
      have hs := Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun h hh =>
        rectangleSourceWeight_lower hu huU hN (rectangle_core_subset hN hj hh).2))
      simpa only [Finset.sum_const, nsmul_eq_mul, mul_assoc] using hs
    _ ≤ ∑ j ∈ rectangleJCore N, ∑ h ∈ rectangleOrders N j, rectangleSourceWeight u N j h := by
      apply Finset.sum_le_sum
      intro j hj
      exact Finset.sum_le_sum_of_subset_of_nonneg (fun h hh => (rectangle_core_subset hN hj hh).2)
        (fun h _ _ => rectangleSourceWeight_nonneg hu0 N j h)
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        have h := Finset.mem_Icc.mp hj
        simp only [Finset.mem_range]
        omega
      · intro j _ _
        exact Finset.sum_nonneg (fun h _ => rectangleSourceWeight_nonneg hu0 N j h)

end
end RiemannGaussian.ZetaRieszSkewAllocation
