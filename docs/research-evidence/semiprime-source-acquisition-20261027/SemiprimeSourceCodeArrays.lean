/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeArrayOps
import OpenAISemiprime.Algorithms.SubexponentialSAT.SubexpRowInterpolation

/-! # Coefficient arrays from finite source interpolation expressions
Runtime expressions contain only rational constants, addition and multiplication.
Polynomial objects occur only in the correctness specification.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceCodeArrays
open scoped BigOperators
open Polynomial SemiprimeJetArray SemiprimeArrayOps
open OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation

/-- Execute a finite source expression, caching both recursive array results. -/
def compile (J : ℕ) : PolynomialCode ℚ → InverseReport
  | .constant a => ⟨Array.ofFn (fun i : Fin J => if i.val=0 then a else 0),0,0⟩
  | .indeterminate => ⟨Array.ofFn (fun i : Fin J => if i.val=1 then 1 else 0),0,0⟩
  | .add p q =>
      let a := compile J p
      let b := compile J q
      let out := addJet a.coefficients b.coefficients J
      ⟨out.coefficients,a.arithmetic+b.arithmetic+out.arithmetic,
        a.reads+b.reads+out.reads⟩
  | .mul p q =>
      let a := compile J p
      let b := compile J q
      let out := multiply a.coefficients b.coefficients J
      ⟨out.coefficients,a.arithmetic+b.arithmetic+out.arithmetic,
        a.reads+b.reads+out.reads⟩

/-- Every executed expression returns exactly the requested array width. -/
theorem compile_size (J : ℕ) (p : PolynomialCode ℚ) :
    (compile J p).coefficients.size=J := by
  cases p <;> simp [compile, addJet_size, multiply_size]

/-- Low coefficients are actual coefficients of the finite source expression. -/
theorem compile_coefficient (J : ℕ) (p : PolynomialCode ℚ) (i : ℕ) (hi : i<J) :
    coefficient (compile J p).coefficients i = p.denote.coeff i := by
  induction p generalizing i with
  | constant a => simp [compile, ofFn_coefficient, hi, PolynomialCode.denote, coeff_C]
  | indeterminate => simp [compile, ofFn_coefficient, hi, PolynomialCode.denote, coeff_X, eq_comm]
  | add p q hp hq =>
    change coefficient (addJet (compile J p).coefficients (compile J q).coefficients J).coefficients i = _
    rw [addJet_coefficient _ _ J i hi]
    simpa only [PolynomialCode.denote,coeff_add] using congrArg₂ (·+·) (hp i hi) (hq i hi)
  | mul p q hp hq =>
    change coefficient (multiply (compile J p).coefficients (compile J q).coefficients J).coefficients i = _
    rw [multiply_coefficient _ _ J i hi, PolynomialCode.denote, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.sum_congr rfl
    intro k hk
    have hki : k ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    rw [hp k (by omega),hq (i-k) (by omega)]

/-- Actual scalar-operation count, bounded by the finite expression tree size. -/
def nodes : PolynomialCode ℚ → ℕ
  | .constant _ => 1
  | .indeterminate => 1
  | .add p q => nodes p+nodes q+1
  | .mul p q => nodes p+nodes q+1

/-- The cached expression interpreter performs at most quadratic-width work per node. -/
theorem compile_arithmetic (J : ℕ) (p : PolynomialCode ℚ) :
    (compile J p).arithmetic ≤ nodes p * (J*(J+1)+J) := by
  induction p with
  | constant a => simp [compile,nodes]
  | indeterminate => simp [compile,nodes]
  | add p q hp hq =>
    simp only [compile,nodes]
    have ho := (addJet_work (compile J p).coefficients (compile J q).coefficients J).1
    rw [ho]
    nlinarith
  | mul p q hp hq =>
    simp only [compile,nodes]
    have ho := (multiply_work (compile J p).coefficients (compile J q).coefficients J).1
    rw [ho]
    nlinarith

/-- Cached coefficient reads are quadratic in width per finite expression node. -/
theorem compile_reads (J : ℕ) (p : PolynomialCode ℚ) :
    (compile J p).reads ≤ nodes p * (J*(J+1)+2*J) := by
  induction p with
  | constant a => simp [compile,nodes]
  | indeterminate => simp [compile,nodes]
  | add p q hp hq =>
    simp only [compile,nodes]
    have ho := (addJet_work (compile J p).coefficients (compile J q).coefficients J).2
    rw [ho]
    nlinarith
  | mul p q hp hq =>
    simp only [compile,nodes]
    have ho := (multiply_work (compile J p).coefficients (compile J q).coefficients J).2
    rw [ho]
    nlinarith

#print axioms compile_coefficient
end RiemannGaussian.SemiprimeSourceCodeArrays
