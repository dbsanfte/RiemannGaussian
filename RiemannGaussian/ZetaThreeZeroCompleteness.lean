/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GammaThetaTwentySix
import RiemannGaussian.ZetaHeightTwentySix
import RiemannGaussian.ZetaHardySamples
import RiemannGaussian.ZetaHardyWindowCompleteness
import RiemannGaussian.ZetaCountingEndpoint

/-!
# Complete critical-line verification through height twenty-six

Four checked Hardy signs supply three disjoint positive zero windows.
Their conjugates exhaust the independently checked complete multiplicity
count of six. Thus every nontrivial zero through this height lies on the
critical line, with no assumed low-zero table or numerical premise.
-/

namespace RiemannGaussian.ZetaThreeZeroCompleteness
noncomputable section
open ZetaHardyPhase ZetaHardySamples ZetaHardyWindowCompleteness

/-- The complete symmetric zero count through height twenty-six is six,
with actual analytic multiplicities and both signs of the ordinate. -/
theorem count_twentySix : ZetaFiniteZeroCount.count 26 = 6 := by
  apply ZetaCountingEndpoint.count_eq_of_phase_sector (by norm_num)
    ZetaHeightTwentySix.horizontal_positive
    ZetaHeightTwentySix.endpoint_imaginary_positive.le 2
  · norm_num
    linarith [GammaThetaTwentySix.theta_bounds.1, Real.pi_lt_d20]
  · norm_num
    linarith [GammaThetaTwentySix.theta_bounds.2, Real.pi_gt_three]

/-- Every nontrivial zeta zero through absolute height twenty-six has
real part one half. All sign, phase, contour and count inputs are discharged. -/
theorem critical_line_through_twentySix (ρ : NontrivialZetaZero) (hρ : |ρ.1.im| ≤ 26) :
    ρ.1.re = 1 / 2 := by
  apply critical_line_of_sign_windows (by norm_num : (0 : ℝ) ≤ 26)
    ![14, 15, 22] ![15, 22, 26] ?_ ?_ ?_ ?_ ?_ ?_ ρ hρ
  · intro i
    fin_cases i <;> norm_num
  · intro i
    fin_cases i <;> norm_num
  · intro i
    fin_cases i <;> norm_num
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at *
  · intro i
    fin_cases i
    · exact mul_neg_of_neg_of_pos negative_fourteen positive_fifteen
    · exact mul_neg_of_pos_of_neg positive_fifteen negative_twentyTwo
    · exact mul_neg_of_neg_of_pos negative_twentyTwo positive_twentySix
  · rw [count_twentySix]

/-- Actual zeta is nonzero off the critical line in the positive real
half-plane through height twenty-six, with the pole at one excluded. -/
theorem nonzero_through_twentySix {s : ℂ} (hs : 0 < s.re) (hh : |s.im| ≤ 26)
    (hl : s.re ≠ 1 / 2) (h1 : s ≠ 1) : riemannZeta s ≠ 0 := by
  intro hz
  have hn : IsNontrivialZetaZero s := by
    refine ⟨hz, ?_, h1⟩
    rintro ⟨n, he⟩
    have hr := congrArg Complex.re he
    norm_num at hr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  exact hl (critical_line_through_twentySix ⟨s, hn⟩ hh)

end
end RiemannGaussian.ZetaThreeZeroCompleteness
