/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GammaThetaFiftyFour
import RiemannGaussian.ZetaHeightFiftyFour
import RiemannGaussian.ZetaHardySamples
import RiemannGaussian.ZetaHardySamplesFiftyFour
import RiemannGaussian.ZetaHardyWindowCompleteness
import RiemannGaussian.ZetaCountingEndpoint

/-!
# Complete critical-line verification through height fifty-four

Twelve checked Hardy signs supply eleven disjoint positive zero windows.
Their conjugates exhaust the independently checked complete multiplicity
count of twenty-two. No numerical zero table or simplicity premise is used.
-/

namespace RiemannGaussian.ZetaElevenZeroCompleteness
noncomputable section
open ZetaHardyPhase ZetaHardySamples ZetaHardySamplesFiftyFour ZetaHardyWindowCompleteness

/-- The complete symmetric multiplicity count through height fifty-four
is twenty-two, counting both signs of the ordinate. -/
theorem count_fiftyFour : ZetaFiniteZeroCount.count 54 = 22 := by
  apply ZetaCountingEndpoint.count_eq_of_phase_sector (by norm_num)
    ZetaHeightFiftyFour.horizontal_positive
    ZetaHeightFiftyFour.endpoint_imaginary_positive.le 10
  · norm_num
    linarith [GammaThetaFiftyFour.theta_bounds.1, Real.pi_lt_d20]
  · norm_num
    linarith [GammaThetaFiftyFour.theta_bounds.2, Real.pi_gt_d20]

/-- Every nontrivial zero through absolute height fifty-four lies on the
critical line. The signs, contour, phase and complete count are discharged. -/
theorem critical_line_through_fiftyFour (ρ : NontrivialZetaZero) (hρ : |ρ.1.im| ≤ 54) :
    ρ.1.re = 1 / 2 := by
  apply critical_line_of_sign_windows (by norm_num : (0 : ℝ) ≤ 54)
    ![14, 15, 22, 26, 31, 34, 38, 42, 44, 49, 51]
    ![15, 22, 26, 31, 34, 38, 42, 44, 49, 51, 54] ?_ ?_ ?_ ?_ ?_ ?_ ρ hρ
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
    · exact mul_neg_of_pos_of_neg positive_twentySix negative_thirtyOne
    · exact mul_neg_of_neg_of_pos negative_thirtyOne positive_thirtyFour
    · exact mul_neg_of_pos_of_neg positive_thirtyFour negative_thirtyEight
    · exact mul_neg_of_neg_of_pos negative_thirtyEight positive_fortyTwo
    · exact mul_neg_of_pos_of_neg positive_fortyTwo negative_fortyFour
    · exact mul_neg_of_neg_of_pos negative_fortyFour positive_fortyNine
    · exact mul_neg_of_pos_of_neg positive_fortyNine negative_fiftyOne
    · exact mul_neg_of_neg_of_pos negative_fiftyOne positive_fiftyFour
  · rw [count_fiftyFour]

/-- Actual zeta is nonzero off the critical line in the positive real
half-plane through height fifty-four, with the pole excluded. -/
theorem nonzero_through_fiftyFour {s : ℂ} (hs : 0 < s.re) (hh : |s.im| ≤ 54)
    (hl : s.re ≠ 1 / 2) (h1 : s ≠ 1) : riemannZeta s ≠ 0 := by
  intro hz
  have hn : IsNontrivialZetaZero s := by
    refine ⟨hz, ?_, h1⟩
    rintro ⟨n, he⟩
    have hr := congrArg Complex.re he
    norm_num at hr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  exact hl (critical_line_through_fiftyFour ⟨s, hn⟩ hh)

end
end RiemannGaussian.ZetaElevenZeroCompleteness
