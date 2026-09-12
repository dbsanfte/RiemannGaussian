/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.DirichletFullRange
import RiemannGaussian.ZetaDyadicPowerBound

/-!
# Discharging the complete canonical zeta block budget

The canonical eta cutoff is below four times the height in the right
half-strip. Every original block therefore admits one of the proved
derivative orders. The full finite budget is bounded by one height power
times a logarithmic block count, with no unproved order-selection premise.
-/

namespace RiemannGaussian.ZetaNearOneLineBudget
noncomputable section
open DerivativePowerExponents DirichletPowerParameters DerivativeOrderComparison
open DirichletBlockPowerProfile ZetaDyadicTruncation ZetaDyadicPowerBound

/-- In the closed unit strip at nonnegative height the complex norm
is at most the height plus one. -/
theorem norm_le_height_add_one {s : ℂ} (hσ : 0 ≤ s.re) (hσ1 : s.re ≤ 1)
    (ht : 0 ≤ s.im) : ‖s‖ ≤ s.im + 1 := by
  have h := Complex.norm_le_abs_re_add_abs_im s
  rw [abs_of_nonneg hσ, abs_of_nonneg ht] at h
  linarith

/-- Every dyadic scale in the canonical eta prefix is at most four
times the height, throughout the closed unit strip above height two. -/
theorem canonical_scale_le {s : ℂ} (hσ : 0 ≤ s.re) (hσ1 : s.re ≤ 1)
    (ht : 2 ≤ s.im) {j : ℕ} (hj : j ≤ depth s) :
    ((2 ^ j : ℕ) : ℝ) ≤ 4 * s.im := by
  have hn := norm_le_height_add_one hσ hσ1 (by linarith)
  have hd := depth_length_lt s
  have hp : ((2 ^ j : ℕ) : ℝ) ≤ ((2 ^ depth s : ℕ) : ℝ) := by
    exact_mod_cast pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℕ)) hj
  linarith

/-- The complete canonical prefix contains at most eight natural
logarithms of the height many blocks. -/
theorem canonical_count_le {s : ℂ} (hσ : 0 ≤ s.re) (hσ1 : s.re ≤ 1)
    (ht : 2 ≤ s.im) : ((depth s + 1 : ℕ) : ℝ) ≤ 8 * Real.log s.im := by
  have htpos : 0 < s.im := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlt := Real.log_le_log (by norm_num : (0 : ℝ) < 2) ht
  have hn := norm_le_height_add_one hσ hσ1 htpos.le
  have hh : ‖s‖ + 2 ≤ 4 * s.im := by linarith
  have hl := Real.log_le_log (by positivity : 0 < ‖s‖ + 2) hh
  have hfour : Real.log 4 = 2 * Real.log 2 := by
    simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num, Nat.cast_ofNat]
      using Real.log_pow (2 : ℝ) 2
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) htpos.ne', hfour] at hl
  have hd := (le_div_iff₀ hl2).mp (depth_le_log s)
  have hc : (((depth s + 1 : ℕ) : ℝ)) * Real.log 2 ≤ 4 * Real.log s.im := by
    push_cast
    nlinarith
  have hb : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ ((depth s + 1 : ℕ) : ℝ) by positivity)
  nlinarith

/-- Every block of the actual canonical prefix has a suitable derivative
order, selected solely from the proved scale comparisons. -/
theorem exists_block_order (k : ℕ) (hk : 1 ≤ k) {s : ℂ}
    (hline : s.re = line k) (ht : 2 ≤ s.im) {j : ℕ} (hj : j ≤ depth s) :
    ∃ r ≤ k, profile r s.re s.im ((2 ^ j : ℕ) : ℝ) ≤ 512 * s.im ^ alpha k := by
  have hσ : 0 ≤ s.re := by rw [hline]; exact line_nonneg k
  have hσ1 : s.re ≤ 1 := by rw [hline]; exact (line_lt_one k).le
  have hx := canonical_scale_le hσ hσ1 ht hj
  rw [hline]
  exact DirichletFullRange.exists_order_bound k hk (by linarith) (by positivity) hx

/-- The entire finite zeta budget is discharged by proved orders no
larger than the target order, including its largest original block. -/
theorem exists_prefix_budget_bound (k : ℕ) (hk : 1 ≤ k) {s : ℂ}
    (hline : s.re = line k) (ht : 2 ≤ s.im) :
    ∃ orders : ℕ → ℕ, (∀ j, orders j ≤ k) ∧
      prefixBudget s orders (depth s + 1) ≤
        ((depth s + 1 : ℕ) : ℝ) * (512 * s.im ^ alpha k) := by
  classical
  have hex : ∀ j : ℕ, ∃ r : ℕ, r ≤ k ∧ (j ≤ depth s →
      profile r s.re s.im ((2 ^ j : ℕ) : ℝ) ≤ 512 * s.im ^ alpha k) := by
    intro j
    by_cases hj : j ≤ depth s
    · obtain ⟨r, hr, h⟩ := exists_block_order k hk hline ht hj
      exact ⟨r, hr, fun _ => h⟩
    · exact ⟨0, Nat.zero_le k, fun h => (hj h).elim⟩
  choose orders hr hb using hex
  refine ⟨orders, hr, ?_⟩
  unfold prefixBudget
  calc
    _ ≤ ∑ _j ∈ Finset.range (depth s + 1), (512 * s.im ^ alpha k) := by
      apply Finset.sum_le_sum
      intro j hj
      exact (min_le_right _ _).trans (hb j (by have h := Finset.mem_range.mp hj; omega))
    _ = _ := by simp

end
end RiemannGaussian.ZetaNearOneLineBudget
