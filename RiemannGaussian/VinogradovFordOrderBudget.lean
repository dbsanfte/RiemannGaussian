/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovFordClosedCoefficient

/-!
# Ford's original interpolation constants

The coefficient and defect envelopes at two adjacent multiples of k
interpolate into the original all-order bounds. The coefficient keeps
`2.055`, `5.91` and `9.7278`; the full interpolation error fits the original
`1.7/k` defect allowance. This is the numerical step in Ford's Theorem 3,
arXiv:1910.08209v1, without a change to its k>=1000 threshold.
-/

namespace RiemannGaussian.VinogradovFordOrderBudget
noncomputable section

/-- The original closed coefficient at a multiple n*k of the degree. -/
def stepCoefficient (k : ℕ) (n : ℝ) : ℝ :=
  (k : ℝ) ^ ((411 / 200) * (k : ℝ) ^ 3 - (591 / 100) * (k : ℝ) ^ 2 + 3 * n * k) *
    (53 / 50 : ℝ) ^ (n * (k : ℝ) ^ 2 + 2 * k * (n ^ 2 - n) - (48639 / 5000) * (k : ℝ) ^ 3)

/-- The original closed defect at the multiple n*k. -/
def stepDefect (k : ℕ) (n : ℝ) : ℝ :=
  (3 / 8) * (k : ℝ) ^ 2 * Real.exp (1 / 2 - 2 * n / k + 169 / (100 * (k : ℝ)))

/-- Ford's original closed coefficient at an arbitrary moment order. -/
def coefficient (k : ℕ) (s : ℝ) : ℝ :=
  (k : ℝ) ^ ((411 / 200) * (k : ℝ) ^ 3 - (591 / 100) * (k : ℝ) ^ 2 + 3 * s) *
    (53 / 50 : ℝ) ^ (s * k + 2 * s ^ 2 / k - (48639 / 5000) * (k : ℝ) ^ 3)

/-- The published all-order defect allowance, with constant 1.7. -/
def defect (k : ℕ) (s : ℝ) : ℝ :=
  (3 / 8) * (k : ℝ) ^ 2 * Real.exp (1 / 2 - 2 * s / (k : ℝ) ^ 2 + 17 / (10 * (k : ℝ)))

/-- Every coefficient at a multiple of a positive degree is positive. -/
theorem stepCoefficient_pos {k : ℕ} (hk : 0 < k) (n : ℝ) : 0 < stepCoefficient k n := by
  unfold stepCoefficient
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  positivity

/-- The final coefficient is positive at every positive degree. -/
theorem coefficient_pos {k : ℕ} (hk : 0 < k) (s : ℝ) : 0 < coefficient k s := by
  unfold coefficient
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  positivity

/-- The coefficient interpolation retains the negative linear reserve in
both adjacent packet exponents before absorbing the quadratic error. -/
theorem coefficient_interpolation {k : ℕ} (hk : 1000 ≤ k)
    {n t : ℝ} (hn : 0 ≤ n) :
    stepCoefficient k n ^ (1 - t) * stepCoefficient k (n + 1) ^ t ≤
      coefficient k ((n + t) * k) := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  unfold stepCoefficient coefficient
  rw [Real.mul_rpow (Real.rpow_nonneg hkpos.le _) (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 53 / 50) _),
    Real.mul_rpow (Real.rpow_nonneg hkpos.le _) (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 53 / 50) _),
    ← Real.rpow_mul hkpos.le, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 53 / 50),
    ← Real.rpow_mul hkpos.le, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 53 / 50),
    mul_mul_mul_comm, ← Real.rpow_add hkpos,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 53 / 50)]
  apply mul_le_mul
  · apply le_of_eq
    congr 1
    ring
  · apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 53 / 50)
    have hp := mul_nonneg (show (0 : ℝ) ≤ 2 * (k : ℝ) by positivity) (add_nonneg hn (sq_nonneg t))
    have he : 2 * ((n + t) * (k : ℝ)) ^ 2 / (k : ℝ) = 2 * (n + t) ^ 2 * (k : ℝ) := by
      field_simp
    rw [he]
    nlinarith only [hp]
  · exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 53 / 50) _
  · exact Real.rpow_nonneg hkpos.le _

private theorem exp_neg_le_quadratic {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  have hh := Real.sum_le_exp_of_nonneg hx 3
  norm_num [Finset.sum_range_succ] at hh
  have hp : 0 ≤ 1 - x + x ^ 2 / 2 := by nlinarith [sq_nonneg (x - 1)]
  have hm := mul_le_mul_of_nonneg_left hh hp
  rw [Real.exp_neg, inv_eq_one_div]
  apply (div_le_iff₀ (Real.exp_pos x)).mpr
  nlinarith [sq_nonneg (x ^ 2)]

/-- The exact geometric interpolation ratio has a quadratic exponential cost. -/
theorem exponential_interpolation {k : ℕ} (hk : 0 < k) {t : ℝ} (ht : 0 ≤ t) :
    1 - t + t * Real.exp (-2 / (k : ℝ)) ≤
      Real.exp (-2 * t / k + 2 * t / (k : ℝ) ^ 2) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hh := mul_le_mul_of_nonneg_left (exp_neg_le_quadratic
    (show (0 : ℝ) ≤ 2 / k by positivity)) ht
  have hr := Real.add_one_le_exp (-2 * t / k + 2 * t / (k : ℝ) ^ 2)
  have he : 1 - t + t * (1 - (2 / (k : ℝ)) + (2 / (k : ℝ)) ^ 2 / 2) =
      (-2 * t / k + 2 * t / (k : ℝ) ^ 2) + 1 := by ring
  rw [← neg_div] at hh
  linarith

/-- The next closed defect is exactly the preceding one times exp(-2/k). -/
theorem stepDefect_succ (k : ℕ) (n : ℝ) :
    stepDefect k (n + 1) = stepDefect k n * Real.exp (-2 / (k : ℝ)) := by
  unfold stepDefect
  conv_rhs => rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- The full interpolation error fits Ford's original 1.7/k allowance. -/
theorem defect_interpolation {k : ℕ} (hk : 1000 ≤ k)
    (n : ℝ) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * stepDefect k n + t * stepDefect k (n + 1) ≤
      defect k ((n + t) * k) := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hratio := exponential_interpolation (by omega : 0 < k) ht
  have hm := mul_le_mul_of_nonneg_left hratio
    (show 0 ≤ stepDefect k n by unfold stepDefect; positivity)
  rw [stepDefect_succ]
  have he : (1 - t) * stepDefect k n + t * (stepDefect k n * Real.exp (-2 / (k : ℝ))) =
      stepDefect k n * (1 - t + t * Real.exp (-2 / (k : ℝ))) := by ring
  rw [he]
  refine hm.trans ?_
  unfold stepDefect defect
  rw [mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  have hp : 2 * t ≤ (k : ℝ) / 100 := by linarith
  field_simp
  nlinarith only [hp]

end
end RiemannGaussian.VinogradovFordOrderBudget
