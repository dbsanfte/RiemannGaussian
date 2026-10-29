/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PhysicalRecursiveReport

/-! # Fuel-compatible actual report aggregation
Only states satisfying the real depth-plus-remaining-fuel invariant require a
local bound. In particular no artificial zero-fuel computation at the root is
included when the actual root fuel is the schedule threshold.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace RiemannGaussian.SemiprimeD1PhysicalRecursiveAggregation
open SemiprimeD1RecursiveCallTree SemiprimeD1RecursiveCallState
open SemiprimeD1PhysicalRecursiveReport

/-- Internal summation over ACTUAL reachable remaining-fuel states. The final
resource endpoint derives the local envelope from original-state/component
bounds; this lemma neither supplies nor executes an advised child solver. -/
theorem run_clock_le_count (s fuel threshold B : ℕ) (root : Call)
    (hinv : threshold ≤ root.depth+fuel)
    (hlocal : ∀ c, Reach s root c → ∀ f ≤ fuel,
      threshold ≤ c.depth+f → localWork s f c ≤ B) :
    (SemiprimeD1PhysicalRecursiveCounter.run s fuel root.depth root.ctx root.net).clock ≤
      B*count s fuel root := by
  rw [run_clock_eq_treeWork]
  have go : ∀ f ≤ fuel, ∀ c, Reach s root c → threshold ≤ c.depth+f →
      treeWork s f c ≤ B*count s f c := by
    intro f
    induction f with
    | zero =>
      intro hf c hr hi
      simpa only [treeWork,count,Nat.mul_one] using hlocal c hr 0 hf hi
    | succ f ih =>
      intro hf c hr hi
      have hs : ((children s c).map (treeWork s f)).sum ≤
          ((children s c).map (fun child => B*count s f child)).sum := by
        apply List.sum_le_sum
        intro child hchild
        apply ih (by omega) child (Reach.step hr hchild)
        rw [mem_children_depth s c child hchild]
        omega
      simp only [treeWork,count]
      rw [List.sum_map_mul_left] at hs
      nlinarith only [hs,hlocal c hr (f+1) hf hi]
  exact go fuel le_rfl root Reach.root hinv

end RiemannGaussian.SemiprimeD1PhysicalRecursiveAggregation
