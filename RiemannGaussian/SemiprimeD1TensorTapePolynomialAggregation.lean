/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ActualCallPolynomialAggregation
import RiemannGaussian.SemiprimeD1TensorTapeRecursiveReport

/-! # Cubic call-inventory bound for the actual tape-leaf program
This internal proof join retains all reports and restricts remaining fuel to the
real schedule invariant. Original-data local bounds are discharged separately.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1TensorTapePolynomialAggregation
open SemiprimeD1RecursiveCallTree SemiprimeD1RecursiveCallState
open SemiprimeD1TensorTapeRecursiveReport

/-- Actual local squared branching costs aggregate into a cubic actual-call
factor, with the real fuel-zero serialized leaf paid independently. -/
theorem run_clock_le_count_cube (s fuel threshold B : ℕ) (root : Call)
    (hinv : threshold ≤ root.depth+fuel)
    (hleaf : ∀c,Reach s root c → threshold ≤ c.depth → localWork s 0 c ≤ B)
    (hlocal : ∀c,Reach s root c → ∀f ≤ fuel,threshold ≤ c.depth+f →
      localWork s f c ≤ B*((children s c).length+1)^2) :
    (SemiprimeD1TensorTapeRecursiveCounter.run s fuel root.depth root.ctx root.net).clock ≤
      B*(count s fuel root)^3 := by
  apply SemiprimeD1ActualCallPolynomialAggregation.report_le_count_cube s fuel threshold B root
    (fun f c => (SemiprimeD1TensorTapeRecursiveCounter.run s f c.depth c.ctx c.net).clock)
    (localWork s)
  · exact run_zero_clock s
  · exact run_clock s
  · exact hinv
  · exact hleaf
  · exact hlocal

end RiemannGaussian.SemiprimeD1TensorTapePolynomialAggregation
