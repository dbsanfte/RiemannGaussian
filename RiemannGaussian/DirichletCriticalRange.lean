/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.DirichletBlockPowerProfile

/-!
# Complete small-block control on every balanced near-one line

On `sigma=1-(k+2)*alpha k`, the leading power is independent of block
size. The exact transition exponent controls the complementary term.
Every complete dyadic prefix through that transition is therefore bounded
by one explicit height power times its actual number of blocks.
-/

namespace RiemannGaussian.DirichletCriticalRange
noncomputable section
open DerivativePowerExponents DirichletPowerParameters
open DirichletDyadicBlocks DirichletBlockPowerProfile

/-- On the balanced line the leading block power vanishes exactly;
the complete complementary power remains explicit. -/
theorem profile_on_line (k : ℕ) (t X : ℝ) :
    profile k (line k) t X = 256 * t ^ alpha k + 64 * t ^ (-alpha k) * X ^ slope k := by
  unfold profile line
  rw [show 1 - (1 - ((k : ℝ) + 2) * alpha k) - ((k : ℝ) + 2) * alpha k = 0 by ring,
    Real.rpow_zero, mul_one]
  rw [show beta k - (1 - ((k : ℝ) + 2) * alpha k) + ((k : ℝ) + 2) * alpha k =
    slope k by unfold beta DirichletPowerParameters.slope; ring]

/-- Through the exact transition scale, the full complementary term
costs at most one additional copy of the leading height power. -/
theorem profile_le_on_range (k : ℕ) {t X : ℝ} (ht : 0 < t) (hX : 0 < X)
    (hupper : X ≤ t ^ transition k) : profile k (line k) t X ≤ 320 * t ^ alpha k := by
  have hp := Real.rpow_le_rpow hX.le hupper (slope_pos k).le
  rw [← Real.rpow_mul ht.le, transition_balance] at hp
  have hm := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg ht.le (-alpha k))
  have he : t ^ (-alpha k) * t ^ (2 * alpha k) = t ^ alpha k := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  rw [he] at hm
  rw [profile_on_line]
  nlinarith

/-- Every original dyadic block through the transition satisfies the
same height-power bound, at every derivative order. -/
theorem block_bound (k j : ℕ) {s : ℂ} (hline : s.re = line k) (ht : 0 < s.im)
    (hupper : ((2 ^ j : ℕ) : ℝ) ≤ s.im ^ transition k) :
    ‖block s j‖ ≤ 320 * s.im ^ alpha k := by
  have hσ : 0 ≤ s.re := by rw [hline]; exact line_nonneg k
  apply (DirichletBlockPowerProfile.bound k j hσ ht).trans
  rw [hline]
  exact profile_le_on_range k ht (by positivity) hupper

/-- The entire original dyadic prefix below the transition is bounded
by its exact number of blocks times the uniform height power. -/
theorem prefix_bound (k J : ℕ) {s : ℂ} (hline : s.re = line k) (ht : 0 < s.im)
    (hupper : ((2 ^ J : ℕ) : ℝ) ≤ s.im ^ transition k) :
    ‖positivePrefix s (2 ^ J)‖ ≤ (J : ℝ) * (320 * s.im ^ alpha k) := by
  rw [prefix_pow_two]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _j ∈ Finset.range J, (320 * s.im ^ alpha k) := by
      apply Finset.sum_le_sum
      intro j hj
      apply block_bound k j hline ht
      apply le_trans _ hupper
      exact_mod_cast pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℕ)) (Finset.mem_range.mp hj).le
    _ = _ := by simp

end
end RiemannGaussian.DirichletCriticalRange
