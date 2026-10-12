/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorBinaryEulerControl
import RiemannGaussian.SuzukiLogarithmicConvolution

/-!
# Complete Selberg constraints and a coherent unit-prime control

Completely multiplicative reweighting commutes with the exact finite
divisor convolution, including arbitrary correlated incidence masks.
Consequently the coherent UNIT-prime Euler control respects the complete
prime-pair divisibility ledger and its positive Selberg coefficient.
This does not preserve the UNALTERED Mobius/Gamma right-hand side.
No source estimate for a masked actual-prime quadratic is inferred.
-/

namespace RiemannGaussian.ArithmeticOperatorSelbergControlAudit
noncomputable section
open scoped BigOperators Classical

/-- Exact ordered divisor convolution, with the zero endpoint unchanged. -/
def convolution (a b : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ de ∈ n.divisorsAntidiagonal, a de.1*b de.2

/-- Completely multiplicative reweighting of an integer coefficient. -/
def reweight (g : ℕ →*₀ ℂ) (a : ℕ → ℂ) (n : ℕ) : ℂ := g n*a n

/-- The product identity holds on every exact integer factorization. -/
theorem reweighted_incidence (g : ℕ →*₀ ℂ) (a b : ℕ → ℂ)
    {n : ℕ} {de : ℕ×ℕ} (hde : de∈n.divisorsAntidiagonal) :
    reweight g a de.1*reweight g b de.2 = g n*(a de.1*b de.2) := by
  have hn := (Nat.mem_divisorsAntidiagonal.mp hde).1
  rw [reweight,reweight,←hn,map_mul]
  ring

/-- Every correlated incidence mask survives the SAME reweighting.
There is no separation of phases or replacement of a cutoff. -/
theorem masked_convolution_reweight (g : ℕ →*₀ ℂ) (a b : ℕ → ℂ)
    (mask : ℕ → ℕ×ℕ → ℂ) (n : ℕ) :
    (∑ de ∈ n.divisorsAntidiagonal,
      mask n de*(reweight g a de.1*reweight g b de.2)) =
    g n*(∑ de ∈ n.divisorsAntidiagonal,mask n de*(a de.1*b de.2)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro de hde
  rw [reweighted_incidence g a b hde]
  ring

/-- Full Dirichlet convolution commutes with multiplicative selection. -/
theorem convolution_reweight (g : ℕ →*₀ ℂ) (a b : ℕ → ℂ) (n : ℕ) :
    convolution (reweight g a) (reweight g b) n = g n*convolution a b n := by
  simpa only [one_mul,convolution] using
    masked_convolution_reweight g a b (fun _ _ => 1) n

/-- Finite physical cutoffs and the complete complex test stay literal. -/
theorem weighted_masked_convolution_reweight (g : ℕ →*₀ ℂ) (a b : ℕ → ℂ)
    (S : Finset ℕ) (w : ℕ → ℂ) (mask : ℕ → ℕ×ℕ → ℂ) :
    (∑ n∈S,w n*∑ de∈n.divisorsAntidiagonal,
      mask n de*(reweight g a de.1*reweight g b de.2)) =
    ∑ n∈S,w n*g n*∑ de∈n.divisorsAntidiagonal,
      mask n de*(a de.1*b de.2) := by
  simp_rw [masked_convolution_reweight,mul_assoc]

/-- Both signs of the logarithmic Selberg word, not an absolute allowance. -/
def selbergWord (epsilon : ℂ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a n*(Real.log n : ℂ)+epsilon*convolution a a n

/-- The entire word, not merely either leg, is multiplicatively selected. -/
theorem selbergWord_reweight (g : ℕ →*₀ ℂ) (epsilon : ℂ)
    (a : ℕ → ℂ) (n : ℕ) :
    selbergWord epsilon (reweight g a) n = g n*selbergWord epsilon a n := by
  rw [selbergWord,selbergWord,convolution_reweight,reweight]
  ring

/-- The actual Mangoldt row, including every proper prime power. -/
def mangoldt (n : ℕ) : ℂ := (ArithmeticFunction.vonMangoldt n : ℂ)

theorem convolution_mangoldt (n : ℕ) :
    convolution mangoldt mangoldt n = (zetaPrimePairArithmetic n : ℂ) := by
  simp only [convolution,mangoldt,zetaPrimePairArithmetic,
    ArithmeticFunction.mul_apply,Complex.ofReal_sum,Complex.ofReal_mul]

/-- Positive complete Selberg word of the ACTUAL integer sequence. -/
theorem selbergWord_plus_mangoldt (n : ℕ) :
    selbergWord 1 mangoldt n =
      ((ArithmeticFunction.vonMangoldt n*Real.log n+zetaPrimePairArithmetic n : ℝ) : ℂ) := by
  simp [selbergWord,mangoldt,convolution_mangoldt]

/-- The signed prime-minus-pair word retains the opposite quadratic sign. -/
theorem selbergWord_minus_mangoldt (n : ℕ) :
    selbergWord (-1) mangoldt n =
      ((ArithmeticFunction.vonMangoldt n*Real.log n-zetaPrimePairArithmetic n : ℝ) : ℂ) := by
  simp [selbergWord,mangoldt,convolution_mangoldt,sub_eq_add_neg]

/-- The exact Mobius log-square identity is extra ACTUAL arithmetic data. -/
theorem actual_plus_eq_moebius (n : ℕ) :
    selbergWord 1 mangoldt n =
      ((∑ de∈n.divisorsAntidiagonal,
        (ArithmeticFunction.moebius de.1 : ℝ)*(Real.log de.2)^2 : ℝ) : ℂ) := by
  rw [selbergWord_plus_mangoldt,
    sum_moebius_log_square_eq_vonMangoldt_log_add_pair]

/-- The unit-prime control satisfies the full pair-incidence identity. -/
theorem control_convolution (u y : ℝ) (n : ℕ) :
    convolution
      (fun n => (ArithmeticOperatorPrimeTowerControl.towerCoefficient
        (ArithmeticOperatorBinaryPrimeControl.retainedBase u y) n : ℂ))
      (fun n => (ArithmeticOperatorPrimeTowerControl.towerCoefficient
        (ArithmeticOperatorBinaryPrimeControl.retainedBase u y) n : ℂ)) n =
      ArithmeticOperatorBinaryEulerControl.indicatorHom u y n*
        (zetaPrimePairArithmetic n : ℂ) := by
  simp_rw [ArithmeticOperatorBinaryEulerControl.coefficient_eq_indicator_mangoldt]
  exact (convolution_reweight _ mangoldt mangoldt n).trans
    (congrArg (_*·) (convolution_mangoldt n))

/-- Complete two-prime selection does not violate the positive Selberg
coefficient, but multiplies its Mobius right-hand side as well. -/
theorem control_selbergWord (u y : ℝ) (epsilon : ℂ) (n : ℕ) :
    selbergWord epsilon
      (fun n => (ArithmeticOperatorPrimeTowerControl.towerCoefficient
        (ArithmeticOperatorBinaryPrimeControl.retainedBase u y) n : ℂ)) n =
      ArithmeticOperatorBinaryEulerControl.indicatorHom u y n*
        selbergWord epsilon mangoldt n := by
  simp_rw [ArithmeticOperatorBinaryEulerControl.coefficient_eq_indicator_mangoldt]
  exact selbergWord_reweight _ epsilon mangoldt n

/-- Actual complete Selberg coefficient is nonnegative before phase. -/
theorem actual_plus_nonnegative (n : ℕ) : 0≤(selbergWord 1 mangoldt n).re := by
  rw [selbergWord_plus_mangoldt,Complex.ofReal_re]
  exact add_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.log_natCast_nonneg n))
    (zetaPrimePairArithmetic_nonneg n)

/-- Even the full positive quadratic constraint admits the coherent
unit-prime control. This supplies no signed filtered comparison. -/
theorem control_plus_nonnegative (u y : ℝ) (n : ℕ) :
    0≤(selbergWord 1
      (fun n => (ArithmeticOperatorPrimeTowerControl.towerCoefficient
        (ArithmeticOperatorBinaryPrimeControl.retainedBase u y) n : ℂ)) n).re := by
  rw [control_selbergWord]
  change 0≤((if ArithmeticOperatorBinaryEulerControl.kept u y n then (1 : ℂ) else 0)*
    selbergWord 1 mangoldt n).re
  split_ifs
  · simpa using actual_plus_nonnegative n
  · simp

/-- Complete ACTUAL Selberg data are stronger than positivity or the
selected-monoid divisor ledger. They detect even one omitted prime. -/
theorem control_fails_actual_moebius_constraint :
    ∃ p : ℕ, p.Prime ∧
      selbergWord 1
        (fun n => (ArithmeticOperatorPrimeTowerControl.towerCoefficient
          (ArithmeticOperatorBinaryPrimeControl.retainedBase (10001/20000) 54) n : ℂ)) p ≠
      ((∑ de∈p.divisorsAntidiagonal,
        (ArithmeticFunction.moebius de.1 : ℝ)*(Real.log de.2)^2 : ℝ) : ℂ) := by
  obtain ⟨p,hp,hdeleted⟩ := ArithmeticOperatorBinaryEulerControl.exists_deleted_prime
  refine ⟨p,hp,?_⟩
  rw [←actual_plus_eq_moebius,control_selbergWord,
    ArithmeticOperatorBinaryEulerControl.indicator_prime _ _ hp]
  simp only [ArithmeticOperatorBinaryPrimeControl.retainedBase,hdeleted,sub_self,
    Complex.ofReal_zero,zero_mul]
  intro hh
  have hr := congrArg Complex.re hh
  rw [selbergWord_plus_mangoldt,Complex.ofReal_re,
    ArithmeticFunction.vonMangoldt_apply_prime hp] at hr
  have hl : 0<Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hpair := zetaPrimePairArithmetic_nonneg p
  simp only [Complex.zero_re] at hr
  nlinarith

end
end RiemannGaussian.ArithmeticOperatorSelbergControlAudit
