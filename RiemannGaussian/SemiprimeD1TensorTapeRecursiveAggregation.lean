/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ActualCallAggregation
import RiemannGaussian.SemiprimeD1TensorTapeRecursiveReport

/-! # Fuel-compatible aggregation of the actual tape-leaf controller
The local premise is restricted to actual reachable remaining-fuel states.
This proof-only join retains the new leaf reports and all repeated active reports.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1TensorTapeRecursiveAggregation
open SemiprimeD1RecursiveCallTree SemiprimeD1RecursiveCallState
open SemiprimeD1TensorTapeRecursiveReport

/-- The closed tape-leaf program obeys the actual call-count aggregation, with
no nonexistent zero-fuel root execution included. -/
theorem run_clock_le_count (s fuel threshold B : ℕ) (root : Call)
    (hinv : threshold ≤ root.depth+fuel)
    (hlocal : ∀ c, Reach s root c → ∀ f ≤ fuel,
      threshold ≤ c.depth+f → localWork s f c ≤ B) :
    (SemiprimeD1TensorTapeRecursiveCounter.run s fuel root.depth root.ctx root.net).clock ≤
      B*count s fuel root := by
  apply SemiprimeD1ActualCallAggregation.report_le_count s fuel threshold B root
    (fun f c => (SemiprimeD1TensorTapeRecursiveCounter.run s f c.depth c.ctx c.net).clock)
    (localWork s)
  · exact run_zero_clock s
  · exact run_clock s
  · exact hinv
  · exact hlocal

end RiemannGaussian.SemiprimeD1TensorTapeRecursiveAggregation
