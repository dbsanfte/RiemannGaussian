/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecursiveCallState

/-! # Fuel-compatible aggregation for proved actual program recurrences
This is a proof-only finite-tree summation principle. Concrete controllers must
prove the zero/successor equations for their OWN reports and derive the contribution
envelope; no report function is supplied to any executable public counter.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace RiemannGaussian.SemiprimeD1ActualCallAggregation
open SemiprimeD1RecursiveCallTree SemiprimeD1RecursiveCallState

/-- A proved actual report recurrence sums to the literal call count, restricted
to real reachable remaining-fuel states. No nonexistent zero-fuel root is paid. -/
theorem report_le_count (s fuel threshold B : ℕ) (root : Call)
    (report contribution : ℕ → Call → ℕ)
    (hzero : ∀ c, report 0 c=contribution 0 c)
    (hsucc : ∀ f c, report (f+1) c=contribution (f+1) c+
      ((children s c).map (report f)).sum)
    (hinv : threshold ≤ root.depth+fuel)
    (hlocal : ∀ c, Reach s root c → ∀ f ≤ fuel,
      threshold ≤ c.depth+f → contribution f c ≤ B) :
    report fuel root ≤ B*count s fuel root := by
  have go : ∀ f ≤ fuel, ∀ c, Reach s root c → threshold ≤ c.depth+f →
      report f c ≤ B*count s f c := by
    intro f
    induction f with
    | zero =>
      intro hf c hr hi
      simpa only [hzero,count,Nat.mul_one] using hlocal c hr 0 hf hi
    | succ f ih =>
      intro hf c hr hi
      have hs : ((children s c).map (report f)).sum ≤
          ((children s c).map (fun child => B*count s f child)).sum := by
        apply List.sum_le_sum
        intro child hchild
        apply ih (by omega) child (Reach.step hr hchild)
        rw [mem_children_depth s c child hchild]
        omega
      rw [hsucc,count]
      rw [List.sum_map_mul_left] at hs
      nlinarith only [hs,hlocal c hr (f+1) hf hi]
  exact go fuel le_rfl root Reach.root hinv

end RiemannGaussian.SemiprimeD1ActualCallAggregation
