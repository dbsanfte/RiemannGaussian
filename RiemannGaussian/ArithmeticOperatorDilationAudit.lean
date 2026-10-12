/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorGramAudit
import RiemannGaussian.SuzukiCarryPhaseScaleGate

/-!
# Pole-centered cutoff dilation and its exact collapse

This prototype passes the source and density gates. Its complete finite
arithmetic expression is nevertheless an arbitrary-weight scalar test.
The precise missing input is a signed bound on that joined test, not an
additional dilation identity.
-/

namespace RiemannGaussian.ArithmeticOperatorDilationAudit
noncomputable section
open Complex
open scoped BigOperators

/-- A literal integer prefix, including every prime power when w=Lambda. -/
def prefixSum (w : ℕ → ℂ) (H : ℕ) : ℂ := ∑ n ∈ Finset.Icc 1 H, w n

/-- Exact two-scale contrast; density centering is applied jointly. -/
def cutoffContrast (p : ℂ) (w : ℕ → ℂ) (H : ℕ) : ℂ :=
  prefixSum w (2*H)-Complex.exp (p*(Real.log 2 : ℂ))*prefixSum w H

/-- The joined scalar kernel retains the actual cutoff boundary. -/
def cutoffKernel (p : ℂ) (H n : ℕ) : ℂ :=
  1-if n ≤ H then Complex.exp (p*(Real.log 2 : ℂ)) else 0

/-- The diagnostic power is evaluated without rounding its physical scale. -/
def powerResponse (s : ℂ) (H : ℝ) : ℂ := Complex.exp (s*(Real.log H : ℂ))

theorem cutoffContrast_eq_joined (p : ℂ) (w : ℕ → ℂ) (H : ℕ) :
    cutoffContrast p w H =
      ∑ n ∈ Finset.Icc 1 (2*H), w n*cutoffKernel p H n := by
  classical
  have he : (Finset.Icc 1 (2*H)).filter (fun n => n ≤ H) = Finset.Icc 1 H := by
    ext n
    simp only [Finset.mem_filter,Finset.mem_Icc]
    omega
  unfold cutoffContrast prefixSum cutoffKernel
  simp_rw [mul_sub, mul_one, mul_ite, mul_zero]
  rw [Finset.sum_sub_distrib,← Finset.sum_filter,he,Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem powerResponse_two_scale {H : ℝ} (hH : 0 < H) (s : ℂ) :
    powerResponse s (2*H) =
      Complex.exp (s*(Real.log 2 : ℂ))*powerResponse s H := by
  unfold powerResponse
  rw [Real.log_mul (by norm_num) hH.ne',Complex.ofReal_add,mul_add,Complex.exp_add]

/-- The complete density mode cancels exactly, including its complex height. -/
theorem density_response_cancels {H : ℝ} (hH : 0 < H) (p : ℂ) :
    powerResponse p (2*H)-Complex.exp (p*(Real.log 2 : ℂ))*powerResponse p H = 0 := by
  rw [powerResponse_two_scale hH,sub_self]

/-- A matched off-line mode with different real exponent is retained.
This exact preflight does not assume it is the only actual zero. -/
theorem matched_source_response_nonzero {H : ℝ} (hH : 0 < H) {p s : ℂ}
    (hps : p.re ≠ s.re) {m : ℂ} (hm : m ≠ 0) :
    m*(powerResponse s (2*H)-Complex.exp (p*(Real.log 2 : ℂ))*powerResponse s H) ≠ 0 := by
  rw [powerResponse_two_scale hH,← sub_mul]
  exact mul_ne_zero hm (mul_ne_zero
    (sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp
      (SuzukiCarryPhaseScaleGate.scale_factor_ne_zero hps))))
    (Complex.exp_ne_zero _))

/-- A free-weight estimate cannot follow from this cutoff identity unless
the whole source-retaining scalar kernel has vanished. -/
theorem cutoff_bound_forall_weights_iff (p : ℂ) (H : ℕ) (B : ℝ) :
    (∀ w : ℕ → ℂ, ‖cutoffContrast p w H‖ ≤ B) ↔
      0 ≤ B ∧ ∀ n ∈ Finset.Icc 1 (2*H), cutoffKernel p H n = 0 := by
  simp_rw [cutoffContrast_eq_joined]
  exact ArithmeticOperatorGramAudit.scalar_bound_forall_weights_iff _ _ _

end
end RiemannGaussian.ArithmeticOperatorDilationAudit
