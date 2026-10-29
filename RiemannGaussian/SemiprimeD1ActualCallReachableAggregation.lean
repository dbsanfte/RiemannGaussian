/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ActualCallPolynomialAggregation

/-! # Actual-state-only polynomial report aggregation
The exact recurrence is required only on genuine reachable contexts. This
allows original root invariants to discharge positivity and actual shape.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1ActualCallReachableAggregation
open SemiprimeD1RecursiveCallTree SemiprimeD1RecursiveCallState
open SemiprimeD1ActualCallPolynomialAggregation

/-- An actual local squared-degree envelope gives a cubic total-call overhead,
without charging nonexistent remaining-fuel states. -/
theorem report_le_count_cube (s fuel threshold B : ℕ) (root : Call)
    (report contribution : ℕ → Call → ℕ)
    (hzero : ∀c,Reach s root c → report 0 c=contribution 0 c)
    (hsucc : ∀f c,Reach s root c → report (f+1) c=contribution (f+1) c+
      ((children s c).map (report f)).sum)
    (hinv : threshold ≤ root.depth+fuel)
    (hleaf : ∀c,Reach s root c → threshold ≤ c.depth → contribution 0 c ≤ B)
    (hlocal : ∀c,Reach s root c → ∀f ≤ fuel,threshold ≤ c.depth+f →
      contribution f c ≤ B*((children s c).length+1)^2) :
    report fuel root ≤ B*(count s fuel root)^3 := by
  have go : ∀f ≤ fuel,∀c,Reach s root c → threshold ≤ c.depth+f →
      report f c ≤ B*(count s f c)^3 := by
    intro f
    induction f with
    | zero =>
      intro hf c hr hi
      rw [hzero c hr]
      simp only [count,Nat.one_pow,Nat.mul_one]
      exact hleaf c hr (by omega)
    | succ f ih =>
      intro hf c hr hi
      have hs : ((children s c).map (report f)).sum ≤
          ((children s c).map (fun child => B*(count s f child)^3)).sum := by
        apply List.sum_le_sum
        intro child hc
        apply ih (by omega) child (Reach.step hr hc)
        rw [mem_children_depth s c child hc]
        omega
      rw [hsucc f c hr,count]
      have hstep:=step_budget ((children s c).map (count s f)) (by
        intro x hx
        obtain ⟨child,hc,rfl⟩:=List.mem_map.mp hx
        exact count_positive s f child)
      simp only [List.length_map,List.map_map,Function.comp_def] at hstep
      rw [List.sum_map_mul_left] at hs
      have hl:=hlocal c hr (f+1) hf hi
      calc
        _ ≤ B*((children s c).length+1)^2+
            B*(((children s c).map (fun child => (count s f child)^3)).sum) := Nat.add_le_add hl hs
        _ = B*(((children s c).length+1)^2+
            (((children s c).map (fun child => (count s f child)^3)).sum)) := by ring
        _ ≤ _ := Nat.mul_le_mul_left B hstep
  exact go fuel le_rfl root Reach.root hinv

end RiemannGaussian.SemiprimeD1ActualCallReachableAggregation
