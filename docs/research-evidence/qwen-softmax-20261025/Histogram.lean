import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators
namespace SoftmaxLUTAudit

/-- Histogram compression is exact for an arbitrary function on a finite alphabet. -/
theorem histogram_sum {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    (code : ι → α) (weight : α → ℝ) :
    (∑ i, weight (code i)) =
      ∑ a, ((Finset.univ.filter (fun i => code i = a)).card : ℝ) * weight a := by
  rw [← Finset.sum_fiberwise Finset.univ code (fun i => weight (code i))]
  apply Finset.sum_congr rfl
  intro a _
  calc
    (∑ i ∈ Finset.univ.filter (fun i => code i = a), weight (code i)) =
        ∑ _i ∈ Finset.univ.filter (fun i => code i = a), weight a := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := by simp

/-- Actual finite input values may be histogrammed before taking real exponentials. -/
theorem softmax_histogram_denominator {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (code : ι → α) (value : α → ℝ) (anchor : ℝ) :
    (∑ i, Real.exp (value (code i) - anchor)) =
      ∑ a, ((Finset.univ.filter (fun i => code i = a)).card : ℝ) *
        Real.exp (value a - anchor) :=
  histogram_sum code (fun a => Real.exp (value a - anchor))

/-- Splitting a dyadic value into two exact pieces supports two factor tables.
This identity asserts no equivalence after floating-point multiplication. -/
theorem two_piece_exp (u v : ℝ) : Real.exp (u+v) = Real.exp u * Real.exp v :=
  Real.exp_add u v

/-- Binary digit decomposition may be transported through exp without approximation. -/
theorem digit_factor_exp {α : Type*} (S : Finset α) (digit : α → ℝ) :
    Real.exp (∑ r ∈ S, digit r) = ∏ r ∈ S, Real.exp (digit r) :=
  Real.exp_sum S digit

/-- A positive certified exponential enclosure gives a certified normalized enclosure. -/
theorem ratio_enclosure (num den nl nu dl du : ℝ)
    (hn : 0 ≤ nl) (hnum : nl ≤ num) (hnum' : num ≤ nu)
    (hdl : 0 < dl) (hden : dl ≤ den) (hden' : den ≤ du) :
    nl / du ≤ num / den ∧ num / den ≤ nu / dl := by
  have hd : 0 < den := lt_of_lt_of_le hdl hden
  constructor
  · exact div_le_div₀ (le_trans hn hnum) hnum hd hden'
  · exact div_le_div₀ (le_trans (le_trans hn hnum) hnum') hnum' hdl hden

#print axioms histogram_sum
#print axioms softmax_histogram_denominator
#print axioms two_piece_exp
#print axioms digit_factor_exp
#print axioms ratio_enclosure
end SoftmaxLUTAudit
