/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1TensorTapeRecursiveAggregation
import RiemannGaussian.SemiprimeD1PhysicalFrameBudget

/-! # Actual tape-leaf local frame budget
The active component is identified only after payload congruence. Every inactive
or fuel-zero contribution retains the executed tape leaf's own report.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1TensorTapeFrameBudget
open SemiprimeD1RecursiveCallTree SemiprimeD1RecursiveCounter SemiprimeD1TensorNetwork
open SemiprimeD1TensorTapeRecursiveReport

/-- Original-data local budget with the actual serialized leaf report. -/
def budget (s : ℕ) (parent : Call) : ℕ :=
  if activeTest s (SemiprimeD1PackingReady.logarithm s) parent.depth (edgeCount parent.net) then
    SemiprimeD1PhysicalFrameBudget.budget s parent
  else (SemiprimeD1TensorTapeLeaf.leaf parent.ctx parent.net).clock+
    s+SemiprimeD1PackingReady.logarithm s+parent.depth+edgeCount parent.net+8

/-- Actual local work has no advised payload/child-cost input. The zero-fuel
inactivity condition is discharged by the real schedule invariant downstream. -/
theorem localWork_bound (s fuel : ℕ) (parent : Call)
    (hz : fuel=0 → activeTest s (SemiprimeD1PackingReady.logarithm s)
      parent.depth (edgeCount parent.net)=false) :
    localWork s fuel parent ≤ budget s parent := by
  cases fuel with
  | zero =>
    simp only [localWork,budget,hz rfl,Bool.false_eq_true,ite_false]
    omega
  | succ fuel =>
    by_cases ha : activeTest s (SemiprimeD1PackingReady.logarithm s)
        parent.depth (edgeCount parent.net)=true
    · rw [localWork_active s fuel parent ha]
      simpa only [budget,ha,ite_true,SemiprimeD1PhysicalRecursiveReport.localWork] using
        SemiprimeD1PhysicalFrameBudget.frame_clock s fuel parent
    · have hf : activeTest s (SemiprimeD1PackingReady.logarithm s)
          parent.depth (edgeCount parent.net)=false := Bool.eq_false_iff.mpr ha
      rw [localWork_inactive s fuel parent hf]
      simp only [budget,hf,Bool.false_eq_true,ite_false,le_refl]

end RiemannGaussian.SemiprimeD1TensorTapeFrameBudget
