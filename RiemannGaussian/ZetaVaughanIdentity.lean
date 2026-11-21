/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-! # Vaughan's identity for real arithmetic functions -/

open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace RiemannGaussian.ZetaVaughanReduction
noncomputable section

/-- Truncation of the actual arithmetic function, including its zero value. -/
def head (D : ℕ) (a : ArithmeticFunction ℝ) : ArithmeticFunction ℝ where
  toFun n := if n ≤ D then a n else 0
  map_zero' := by simp

/-- The entire complementary von Mangoldt divisor fibre. -/
def cofactor (V : ℕ) : ArithmeticFunction ℝ :=
  (ArithmeticFunction.vonMangoldt - head V ArithmeticFunction.vonMangoldt) * ζ

/-- The signed bilinear coefficient, with both large factors retained. -/
def bilinear (U V : ℕ) : ArithmeticFunction ℝ :=
  ((μ : ArithmeticFunction ℝ) - head U μ) * cofactor V

/-- All three small-factor terms with their exact relative signs. -/
def small (U V : ℕ) : ArithmeticFunction ℝ :=
  head V ArithmeticFunction.vonMangoldt + head U μ * ArithmeticFunction.log -
    head U μ * head V ArithmeticFunction.vonMangoldt * ζ

/-- Vaughan's identity for the literal von Mangoldt weights, at every cutoff. -/
theorem vaughan (U V : ℕ) : ArithmeticFunction.vonMangoldt = small U V + bilinear U V := by
  unfold small bilinear cofactor
  rw [← ArithmeticFunction.vonMangoldt_mul_zeta]
  calc
    ArithmeticFunction.vonMangoldt = ArithmeticFunction.vonMangoldt *
        ((μ : ArithmeticFunction ℝ) * ζ) := by
      rw [ArithmeticFunction.coe_moebius_mul_coe_zeta, mul_one]
    _ = _ := by
      have h : (μ : ArithmeticFunction ℝ) * ζ * head V ArithmeticFunction.vonMangoldt =
          head V ArithmeticFunction.vonMangoldt := by
        rw [ArithmeticFunction.coe_moebius_mul_coe_zeta, one_mul]
      linear_combination h

/-- Every retained cofactor is an exact sum over its large prime-power divisors. -/
theorem cofactor_eq (V n : ℕ) :
    cofactor V n = ∑ d ∈ n.divisors,
      if V < d then ArithmeticFunction.vonMangoldt d else 0 := by
  rw [cofactor, ArithmeticFunction.coe_mul_zeta_apply]
  apply Finset.sum_congr rfl
  intro d _
  change ArithmeticFunction.vonMangoldt d - head V ArithmeticFunction.vonMangoldt d = _
  by_cases hd : d ≤ V <;> simp [head, hd, not_lt.mpr, not_le.mp]

/-- Every product keeps the Möbius sign and the same full cofactor. -/
theorem bilinear_eq (U V n : ℕ) :
    bilinear U V n = ∑ a ∈ n.divisorsAntidiagonal,
      if U < a.1 then (μ a.1 : ℝ) * cofactor V a.2 else 0 := by
  rw [bilinear, ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro a _
  change ((μ a.1 : ℝ) - head U μ a.1) * cofactor V a.2 = _
  by_cases ha : a.1 ≤ U <;> simp [head, ha, not_lt.mpr, not_le.mp]

end
end RiemannGaussian.ZetaVaughanReduction
