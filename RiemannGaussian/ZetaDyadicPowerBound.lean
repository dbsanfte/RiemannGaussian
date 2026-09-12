/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.DirichletBlockPowerProfile
import RiemannGaussian.ZetaDyadicTruncation

/-!
# A complete finite power bound for the actual zeta function

Every original dyadic block is bounded by the smaller of its trivial
damped estimate and the proved derivative profile. Any derivative-order
selection is allowed. The full eta reconstruction and its controlled
tail then give a zeta bound involving only explicit real powers and a
finite sum. A canonical logarithmic depth discharges the tail condition.
-/

namespace RiemannGaussian.ZetaDyadicPowerBound
noncomputable section
open DirichletDyadicBlocks DirichletBlockPowerProfile ZetaDyadicTruncation
open scoped Classical

/-- The explicit block cost, retaining the trivial fallback and an
arbitrary derivative order chosen for this particular block. -/
def blockBudget (s : ℂ) (orders : ℕ → ℕ) (j : ℕ) : ℝ :=
  min (((2 ^ j : ℕ) : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ (-s.re))
    (profile (orders j) s.re s.im ((2 ^ j : ℕ) : ℝ))

/-- The complete finite sum of proved block costs through a dyadic depth. -/
def prefixBudget (s : ℂ) (orders : ℕ → ℕ) (J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range J, blockBudget s orders j

/-- The trivial estimate keeps the whole real damping of each dyadic
block, rather than bounding its terms merely by one. -/
theorem trivial_block_bound {s : ℂ} (hσ : 0 ≤ s.re) (j : ℕ) :
    ‖block s j‖ ≤ ((2 ^ j : ℕ) : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ (-s.re) := by
  unfold block
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _n ∈ Finset.range (2 ^ j), (((2 ^ j : ℕ) : ℝ) ^ (-s.re)) := by
      apply Finset.sum_le_sum
      intro n _
      rw [norm_zetaPrimeFeature, weight_eq_rpow s.re (by positivity)]
      exact Real.rpow_le_rpow_of_nonpos (by positivity)
        (by exact_mod_cast Nat.le_add_right (2 ^ j) n) (neg_nonpos.mpr hσ)
    _ = _ := by simp

/-- Every actual block satisfies its explicit selected-order budget. -/
theorem block_bound {s : ℂ} (hσ : 0 ≤ s.re) (ht : 0 < s.im)
    (orders : ℕ → ℕ) (j : ℕ) : ‖block s j‖ ≤ blockBudget s orders j :=
  le_min (trivial_block_bound hσ j) (DirichletBlockPowerProfile.bound (orders j) j hσ ht)

/-- Every block budget is nonnegative at positive height. -/
theorem blockBudget_nonneg {s : ℂ} (ht : 0 < s.im) (orders : ℕ → ℕ) (j : ℕ) :
    0 ≤ blockBudget s orders j :=
  le_min (by positivity) (profile_nonneg _ _ ht.le (by positivity))

/-- The complete prefix budget is nonnegative. -/
theorem prefixBudget_nonneg {s : ℂ} (ht : 0 < s.im) (orders : ℕ → ℕ) (J : ℕ) :
    0 ≤ prefixBudget s orders J :=
  Finset.sum_nonneg fun j _ ↦ blockBudget_nonneg ht orders j

/-- Extending the prefix by a complete block increases its budget. -/
theorem prefixBudget_le_succ {s : ℂ} (ht : 0 < s.im) (orders : ℕ → ℕ) (J : ℕ) :
    prefixBudget s orders J ≤ prefixBudget s orders (J + 1) := by
  unfold prefixBudget
  rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right (blockBudget_nonneg ht orders J)

/-- The complete original positive prefix has the full explicit budget
for every order selection, without an unproved cancellation assumption. -/
theorem prefix_bound {s : ℂ} (hσ : 0 ≤ s.re) (ht : 0 < s.im)
    (orders : ℕ → ℕ) (J : ℕ) :
    ‖positivePrefix s (2 ^ J)‖ ≤ prefixBudget s orders J := by
  rw [prefix_pow_two]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ block_bound hσ ht orders j)

/-- The full finite eta expression is bounded with both complete
prefixes, the exact dyadic factor norm and its final endpoint paid for. -/
theorem eta_prefix_bound {s : ℂ} (hσ : 0 ≤ s.re) (ht : 0 < s.im)
    (orders : ℕ → ℕ) (J : ℕ) :
    ‖pairedEtaCorePartialSum (2 ^ J) s‖ ≤
      prefixBudget s orders (J + 1) + (2 : ℝ) ^ (1 - s.re) * prefixBudget s orders J +
        ((2 ^ (J + 1) : ℕ) : ℝ) ^ (-s.re) := by
  rw [eta_pow_two_eq_blocks, ← prefix_pow_two, ← prefix_pow_two]
  apply (norm_sub_le _ _).trans
  apply add_le_add _ (by rw [norm_zetaPrimeFeature, weight_eq_rpow _ (by positivity)])
  apply (norm_sub_le _ _).trans
  apply add_le_add (prefix_bound hσ ht orders (J + 1))
  rw [norm_mul, feature_eq_cpow s (by norm_num), Nat.cast_ofNat, norm_two_mul_two_cpow_neg]
  exact mul_le_mul_of_nonneg_left (prefix_bound hσ ht orders J) (by positivity)

/-- The actual zeta function has a complete explicit finite power bound
at every positive ordinate inside the strip, for any valid cutoff and
any derivative-order selection. -/
theorem zeta_bound {s : ℂ} (hσ : 0 < s.re) (hσ1 : s.re < 1) (ht : 0 < s.im)
    (orders : ℕ → ℕ) (J : ℕ) (hscale : ‖s‖ ≤ ((2 * 2 ^ J + 1 : ℕ) : ℝ)) :
    ‖riemannZeta s‖ ≤
      (prefixBudget s orders (J + 1) + (2 : ℝ) ^ (1 - s.re) * prefixBudget s orders J +
        ((2 ^ (J + 1) : ℕ) : ℝ) ^ (-s.re) +
          2 * (((2 * 2 ^ J + 1 : ℕ) : ℝ) ^ (-s.re))) /
            ((2 : ℝ) ^ (1 - s.re) - 1) := by
  apply (ZetaDyadicTruncation.zeta_norm_le hσ hσ1 J hscale).trans
  apply div_le_div_of_nonneg_right _ (factor_lower_pos hσ1).le
  apply add_le_add _ le_rfl
  rw [← eta_pow_two_eq_blocks]
  exact eta_prefix_bound hσ.le ht orders J

/-- The canonical logarithmic depth removes the cutoff premise from
the actual zeta estimate, still allowing every order selection. -/
theorem canonical_bound {s : ℂ} (hσ : 0 < s.re) (hσ1 : s.re < 1) (ht : 0 < s.im)
    (orders : ℕ → ℕ) :
    ‖riemannZeta s‖ ≤
      (prefixBudget s orders (depth s + 1) +
        (2 : ℝ) ^ (1 - s.re) * prefixBudget s orders (depth s) +
          ((2 ^ (depth s + 1) : ℕ) : ℝ) ^ (-s.re) +
            2 * (((2 * 2 ^ depth s + 1 : ℕ) : ℝ) ^ (-s.re))) /
              ((2 : ℝ) ^ (1 - s.re) - 1) :=
  zeta_bound hσ hσ1 ht orders (depth s) (depth_scale s)

/-- A width-normalized version of the complete zeta bound. The original
phase, exact denominator and separate endpoint costs remain upstream. -/
theorem simple_bound {s : ℂ} (hσ : 0 < s.re) (hσ1 : s.re < 1) (ht : 0 < s.im)
    (orders : ℕ → ℕ) :
    ‖riemannZeta s‖ ≤ 6 * (prefixBudget s orders (depth s + 1) + 1) / (1 - s.re) := by
  have h := (le_div_iff₀ (factor_lower_pos hσ1)).mp (canonical_bound hσ hσ1 ht orders)
  have hb0 := prefixBudget_nonneg ht orders (depth s)
  have hb1 := prefixBudget_nonneg ht orders (depth s + 1)
  have hb := prefixBudget_le_succ ht orders (depth s)
  have htwo : (2 : ℝ) ^ (1 - s.re) ≤ 2 := by
    apply (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by linarith : 1 - s.re ≤ 1)).trans_eq
    exact Real.rpow_one _
  have hm := mul_le_mul_of_nonneg_right htwo hb0
  have he : ((2 ^ (depth s + 1) : ℕ) : ℝ) ^ (-s.re) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ)))
      (by linarith)
  have he' : (((2 * 2 ^ depth s + 1 : ℕ) : ℝ) ^ (-s.re)) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_cast; omega) (by linarith)
  have hgap : (1 - s.re) / 2 ≤ (2 : ℝ) ^ (1 - s.re) - 1 := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hg := Real.add_one_le_exp (Real.log 2 * (1 - s.re))
    nlinarith [Real.log_two_gt_d9]
  have hg := mul_le_mul_of_nonneg_right hgap (norm_nonneg (riemannZeta s))
  apply (le_div_iff₀ (by linarith : 0 < 1 - s.re)).mpr
  nlinarith

end
end RiemannGaussian.ZetaDyadicPowerBound
