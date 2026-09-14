/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovResonancePower

/-!
# Exact quadratic gain of the complete eligible degree window

Every eligible frequency degree contributes its exact integer power gain.
The complete gain is quadratic in degree and survives the two half-epsilon
moment costs. No numerical optimizer is used.
-/

namespace RiemannGaussian.VinogradovDegreeWindow
noncomputable section
open scoped BigOperators

/-- The descending sum of even degree gains has its exact triangular value. -/
theorem descending_gain_sum (m : ℕ) :
    (∑ j ∈ Finset.range m, 2 * (m - (j + 1))) = m * (m - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel, Nat.sub_self, mul_zero, add_zero]
    have he : (∑ j ∈ Finset.range m, 2 * (m + 1 - (j + 1))) =
        (∑ j ∈ Finset.range m, 2 * (m - (j + 1))) + 2 * m := by
      calc
        _ = ∑ j ∈ Finset.range m, (2 * (m - (j + 1)) + 2) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hj' := Finset.mem_range.mp hj
          omega
        _ = _ := by rw [Finset.sum_add_distrib]; simp; omega
    rw [he, ih]
    by_cases hm : m = 0
    · subst m; simp
    · have hpred := Nat.sub_add_cancel (show 1 ≤ m by omega)
      nlinarith only [hpred]

/-- The complete power gain from all and only the unwrapped high degrees. -/
def windowSaving (k : ℕ) : ℕ :=
  ∑ j : Fin k, if 2 * k < 3 * (j.val + 1) then 2 * (k - (j.val + 1)) else 0

/-- The full eligible window has an exact quadratic gain, including its endpoint of zero gain. -/
theorem windowSaving_eq (k : ℕ) :
    windowSaving k = (k - 2 * k / 3) * (k - 2 * k / 3 - 1) := by
  classical
  unfold windowSaving
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => if 2 * k < 3 * (j + 1) then 2 * (k - (j + 1)) else 0) k,
    ← Finset.sum_filter]
  have hset : (Finset.range k).filter (fun j => 2 * k < 3 * (j + 1)) =
      Finset.Ico (2 * k / 3) k := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hset, Finset.sum_Ico_eq_sum_range]
  have he (j : ℕ) : 2 * (k - (2 * k / 3 + j + 1)) =
      2 * ((k - 2 * k / 3) - (j + 1)) := by omega
  simp_rw [he]
  exact descending_gain_sum _

/-- The whole degree window saves a quadratic number of powers for every sufficiently large degree. -/
theorem square_le_twelve_windowSaving (k : ℕ) (hk : 12 ≤ k) :
    k ^ 2 ≤ 12 * windowSaving k := by
  rw [windowSaving_eq]
  have h3 : k ≤ 3 * (k - 2 * k / 3) := by omega
  have h4 : k ≤ 4 * (k - 2 * k / 3 - 1) := by omega
  have h := Nat.mul_le_mul h3 h4
  nlinarith only [h]

/-- After paying the two positive half-epsilon moments, the remaining window gain is still quadratic in degree. -/
theorem square_le_sixteen_net_windowSaving (k : ℕ) (hk : 12 ≤ k) :
    k ^ 2 ≤ 16 * (windowSaving k - 1) := by
  have hquad := square_le_twelve_windowSaving k hk
  have hm : 4 ≤ k - 2 * k / 3 := by omega
  have hsmall : 4 ≤ windowSaving k := by
    rw [windowSaving_eq]
    have hprod := Nat.mul_le_mul hm (show 3 ≤ k - 2 * k / 3 - 1 by omega)
    omega
  omega

end
end RiemannGaussian.VinogradovDegreeWindow
