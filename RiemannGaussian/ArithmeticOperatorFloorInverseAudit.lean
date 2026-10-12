/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorFloorBoundaryAudit
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Exact Gamma uniqueness does not give a polynomially stable source inverse

All finite factorial observations determine Mangoldt exactly, but a
hypothetical zero power mode has only bounded physical floor response.
Consequently no inverse allowance polynomial in logarithmic scale can
recover its exponentially growing amplitude. This is a diagnostic
operator obstruction, not an altered arithmetic measure satisfying every
exact Gamma observation, and not an RH theorem.
-/

namespace RiemannGaussian.ArithmeticOperatorFloorInverseAudit
noncomputable section
open ArithmeticOperatorFloorBoundaryAudit Filter Complex
open scoped Topology

/-- A shift of the order index does not change polynomial/geometric decay. -/
theorem tendsto_shifted_polynomial_geometric (d : ℕ) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) :
    Tendsto (fun J : ℕ => ((J+1 : ℕ) : ℝ)^d*r^J) atTop (𝓝 0) := by
  have ht := ((tendsto_pow_const_mul_const_pow_of_lt_one d hr.le hr1).comp
    (tendsto_add_atTop_nat 1)).div_const r
  simpa only [Function.comp_def,pow_succ,mul_div_assoc,
    mul_div_cancel_right₀ _ hr.ne',zero_div] using ht

/-- Sharp operator-class no-go. Complete physical boundary retention
still leaves an inverse cost larger than EVERY polynomial in log scale
if the diagnostic component is a critical-strip zeta zero. No assertion
about convergence of an actual twisted prime sum is made here. -/
theorem not_eventually_polynomial_inverse_bound {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1) (hz : riemannZeta s = 0)
    (C : ℝ) (hC : 0 ≤ C) (d : ℕ) :
    ¬∀ᶠ J : ℕ in atTop,
      (Real.exp (s.re*Real.log 2))^J ≤
        C*((J+1 : ℕ) : ℝ)^d*
          (1+‖truncatedResponse s ((J : ℝ)*Real.log 2)‖) := by
  intro hbound
  let r := Real.exp (-s.re*Real.log 2)
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by
    have hh : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    nlinarith)
  have hexact : r*Real.exp (s.re*Real.log 2) = 1 := by
    dsimp [r]
    rw [← Real.exp_add]
    simp
  have ht : Tendsto (fun J : ℕ =>
      C*(1+1/s.re)*(((J+1 : ℕ) : ℝ)^d*r^J)) atTop (𝓝 0) := by
    simpa using (tendsto_shifted_polynomial_geometric d hr hr1).const_mul
      (C*(1+1/s.re))
  have hge : ∀ᶠ J : ℕ in atTop,
      (1 : ℝ) ≤ C*(1+1/s.re)*(((J+1 : ℕ) : ℝ)^d*r^J) := by
    filter_upwards [hbound] with J hJ
    calc
      1 = r^J*(Real.exp (s.re*Real.log 2))^J := by rw [← mul_pow,hexact,one_pow]
      _ ≤ r^J*(C*((J+1 : ℕ) : ℝ)^d*
          (1+‖truncatedResponse s ((J : ℝ)*Real.log 2)‖)) :=
        mul_le_mul_of_nonneg_left hJ (pow_nonneg hr.le J)
      _ ≤ r^J*(C*((J+1 : ℕ) : ℝ)^d*(1+1/s.re)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (norm_truncatedResponse_le_of_zeta_zero hs hs1 hz _))
          (by positivity)) (pow_nonneg hr.le J)
      _ = _ := by ring
  have hbad : (1 : ℝ) ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds ht hge
  norm_num at hbad

end
end RiemannGaussian.ArithmeticOperatorFloorInverseAudit
