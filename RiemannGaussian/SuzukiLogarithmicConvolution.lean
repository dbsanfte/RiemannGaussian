/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiBalancedBlockBounds
import RiemannGaussian.SuzukiDivisorQuotientOptimizer
import RiemannGaussian.ZetaPrimeQuadraticArithmetic

/-!
# The logarithmic convolution constraint on Suzuki work

Logarithmic weighting is a derivation of Dirichlet convolution. Applied
to the actual von Mangoldt divisor identity, this gives the exact
second logarithmic convolution identity and its centered version.

The Suzuki prime moment is coupled to the complete prime-pair coefficient
at the same product cutoff. No product complement is dropped, and no
independent lower bound for the remaining signed sum is asserted.
-/

namespace RiemannGaussian
noncomputable section
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- Multiplication by the arithmetic logarithm differentiates Dirichlet
convolution. Both logarithmic factors remain inside the exact product sum. -/
theorem arithmeticFunction_logWeight_mul (f g : ArithmeticFunction ℝ) :
    (f * g).pmul ArithmeticFunction.log =
      f.pmul ArithmeticFunction.log * g + f * g.pmul ArithmeticFunction.log := by
  ext n
  simp only [ArithmeticFunction.pmul_apply, ArithmeticFunction.log_apply,
    ArithmeticFunction.mul_apply, ArithmeticFunction.add_apply]
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨ha, hb⟩ := Nat.ne_zero_of_mem_divisorsAntidiagonal hp
  have hlog : Real.log n = Real.log p.1 + Real.log p.2 := by
    rw [← (Nat.mem_divisorsAntidiagonal.mp hp).1, Nat.cast_mul,
      Real.log_mul (Nat.cast_ne_zero.mpr ha) (Nat.cast_ne_zero.mpr hb)]
  rw [hlog]
  ring

/-- The actual prime logarithmic moment and the full ordered prime-pair
convolution are one signed Möbius convolution of the squared logarithm. -/
theorem vonMangoldt_logWeight_add_self_convolution :
    ArithmeticFunction.vonMangoldt.pmul ArithmeticFunction.log +
      ArithmeticFunction.vonMangoldt * ArithmeticFunction.vonMangoldt =
        (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log.pmul ArithmeticFunction.log := by
  have h := arithmeticFunction_logWeight_mul ArithmeticFunction.vonMangoldt
    (ζ : ArithmeticFunction ℝ)
  rw [ArithmeticFunction.vonMangoldt_mul_zeta, ArithmeticFunction.zeta_pmul] at h
  have he := congrArg (fun f : ArithmeticFunction ℝ => f * μ) h
  rw [add_mul, mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius, mul_one,
    mul_assoc, ArithmeticFunction.log_mul_moebius_eq_vonMangoldt] at he
  exact he.symm.trans (mul_comm _ _)

/-- The same identity at every integer keeps the entire finite Möbius
sum, including its signs, and the original ordered prime-pair coefficient. -/
theorem sum_moebius_log_square_eq_vonMangoldt_log_add_pair (n : ℕ) :
    (∑ p ∈ n.divisorsAntidiagonal, (μ p.1 : ℝ) * (Real.log p.2) ^ 2) =
      ArithmeticFunction.vonMangoldt n * Real.log n + zetaPrimePairArithmetic n := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    vonMangoldt_logWeight_add_self_convolution
  simpa only [ArithmeticFunction.add_apply, ArithmeticFunction.pmul_apply,
    ArithmeticFunction.log_apply, ArithmeticFunction.mul_apply, ArithmeticFunction.intCoe_apply,
    zetaPrimePairArithmetic, pow_two, mul_assoc] using h.symm

/-- Centering must act inside the complete convolution. It subtracts the
same first-order von Mangoldt term and leaves the full pair contribution. -/
theorem sum_moebius_log_mul_sub_center (n : ℕ) (r : ℝ) :
    (∑ p ∈ n.divisorsAntidiagonal,
      (μ p.1 : ℝ) * Real.log p.2 * (Real.log p.2 - r)) =
      ArithmeticFunction.vonMangoldt n * (Real.log n - r) + zetaPrimePairArithmetic n := by
  have hfirst : (∑ p ∈ n.divisorsAntidiagonal, (μ p.1 : ℝ) * Real.log p.2) =
      ArithmeticFunction.vonMangoldt n := by
    simpa only [ArithmeticFunction.mul_apply, ArithmeticFunction.intCoe_apply,
      ArithmeticFunction.log_apply] using congrArg (fun f : ArithmeticFunction ℝ => f n)
        ArithmeticFunction.moebius_mul_log_eq_vonMangoldt
  calc
    _ = (∑ p ∈ n.divisorsAntidiagonal, (μ p.1 : ℝ) * (Real.log p.2) ^ 2) -
        (∑ p ∈ n.divisorsAntidiagonal, (μ p.1 : ℝ) * Real.log p.2) * r := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = _ := by rw [sum_moebius_log_square_eq_vonMangoldt_log_add_pair, hfirst]; ring

/-- Every real finite weight family preserves the same exact signed
constraint. No nonnegativity or optimization hypothesis is imposed on the weights. -/
theorem sum_weighted_vonMangoldt_center_eq_moebius_sub_pair
    (S : Finset ℕ) (w : ℕ → ℝ) (r : ℝ) :
    (∑ n ∈ S, w n * ArithmeticFunction.vonMangoldt n * (Real.log n - r)) =
      ∑ n ∈ S, w n * ((∑ p ∈ n.divisorsAntidiagonal,
        (μ p.1 : ℝ) * Real.log p.2 * (Real.log p.2 - r)) - zetaPrimePairArithmetic n) := by
  simp_rw [sum_moebius_log_mul_sub_center, add_sub_cancel_right, mul_assoc]

/-- Complex finite tests retain their phases through the same coefficient
identity. No real part or norm is taken in transporting the convolution. -/
theorem sum_complex_weighted_vonMangoldt_center_eq_moebius_sub_pair
    (S : Finset ℕ) (w : ℕ → ℂ) (r : ℝ) :
    (∑ n ∈ S, w n * (ArithmeticFunction.vonMangoldt n : ℂ) * ((Real.log n - r : ℝ) : ℂ)) =
      ∑ n ∈ S, w n * (((∑ p ∈ n.divisorsAntidiagonal,
        (μ p.1 : ℝ) * Real.log p.2 * (Real.log p.2 - r)) - zetaPrimePairArithmetic n : ℝ) : ℂ) := by
  simp_rw [sum_moebius_log_mul_sub_center, add_sub_cancel_right, Complex.ofReal_mul, mul_assoc]

/-- The original finite Suzuki linear form has this exact convolution
formula at every center and cutoff. The pair term is subtracted in full. -/
theorem suzukiLegendreLinearForm_eq_moebius_sub_pair (N : ℕ) (r : ℝ) :
    suzukiLegendreLinearForm N r =
      ∑ n ∈ Finset.Icc 1 N,
        ((∑ p ∈ n.divisorsAntidiagonal,
          (μ p.1 : ℝ) * Real.log p.2 * (Real.log p.2 - r)) - zetaPrimePairArithmetic n) /
          Real.sqrt n := by
  simp_rw [sum_moebius_log_mul_sub_center, add_sub_cancel_right]
  rfl

/-- Every complete centered work block inherits the pointwise arithmetic
identity with all its original events and its unchanged starting center. -/
theorem suzukiMassBlockCenteredWork_eq_moebius_sub_pair (start count : ℕ) :
    suzukiMassBlockCenteredWork start count =
      ∑ j ∈ Finset.range count,
        ((∑ p ∈ (start + j + 3).divisorsAntidiagonal,
          (μ p.1 : ℝ) * Real.log p.2 *
            (Real.log p.2 - suzukiLegendreMassCenter start)) -
          zetaPrimePairArithmetic (start + j + 3)) / Real.sqrt (start + j + 3 : ℕ) := by
  simp_rw [sum_moebius_log_mul_sub_center, add_sub_cancel_right]
  unfold suzukiMassBlockCenteredWork suzukiPrimeWeight suzukiPrimeLocation
  apply Finset.sum_congr rfl
  intro j _
  rw [show start + j + 1 + 2 = start + j + 3 by omega]
  ring

/-- Evaluation at the same exact mass center gives the unchanged nonlinear
Suzuki potential. Its full prime-pair subtraction and Archimedean terms
remain together; the identity itself supplies no global lower bound. -/
theorem suzukiMassLegendrePotential_eq_moebius_sub_pair (count : ℕ) :
    suzukiMassLegendrePotential count =
      suzukiArchimedeanIntercept + 4 * Real.exp (suzukiLegendreMassCenter count / 2) +
        suzukiArchimedeanSlopeConstant * suzukiLegendreMassCenter count +
        ∑ n ∈ Finset.Icc 1 (count + 2),
          ((∑ p ∈ n.divisorsAntidiagonal,
            (μ p.1 : ℝ) * Real.log p.2 * (Real.log p.2 - suzukiLegendreMassCenter count)) -
              zetaPrimePairArithmetic n) / Real.sqrt n := by
  rw [← suzukiLegendreTrial_massCenter, suzukiLegendreTrial,
    suzukiLegendreLinearForm_eq_moebius_sub_pair]

end
end RiemannGaussian
