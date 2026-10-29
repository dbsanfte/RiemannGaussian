/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ActualCallAggregation

/-! # Squared local branching overhead aggregates cubically
All sums use the literal actual child inventory and compatible remaining fuel.
The lemma is proof-only; it supplies no executable counter callback or cost.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1ActualCallPolynomialAggregation
open SemiprimeD1RecursiveCallTree SemiprimeD1RecursiveCallState

/-- Nonnegative scalar cubes sum to at most the cube of their total. -/
theorem sum_cubes (xs : List ℕ) : (xs.map (fun x => x^3)).sum ≤ xs.sum^3 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons]
    apply (Nat.add_le_add_left ih _).trans
    nlinarith only [Nat.zero_le (x*x*xs.sum),Nat.zero_le (x*xs.sum*xs.sum)]

/-- Positive child counts dominate their actual list length. -/
theorem length_le_sum (xs : List ℕ) (hx : ∀x∈xs,1 ≤ x) : xs.length ≤ xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hh:=hx x (by simp)
    have ht:=ih (by intro y hy;exact hx y (by simp [hy]))
    simp only [List.length_cons,List.sum_cons]
    omega

/-- The local squared branching term and all child cubic terms fit one cube. -/
theorem step_budget (xs : List ℕ) (hx : ∀x∈xs,1 ≤ x) :
    (xs.length+1)^2+(xs.map (fun x => x^3)).sum ≤ (1+xs.sum)^3 := by
  have hl:=Nat.pow_le_pow_left (Nat.add_le_add_right (length_le_sum xs hx) 1) 2
  have hc:=sum_cubes xs
  nlinarith only [hl,hc,Nat.zero_le (xs.sum*xs.sum),Nat.zero_le xs.sum]

/-- Every actual finite call inventory includes its current call. -/
theorem count_positive (s fuel : ℕ) (c : Call) : 1 ≤ count s fuel c := by
  cases fuel <;> simp only [count] <;> omega

/-- An actual local squared-degree envelope gives a cubic total-call overhead,
without charging nonexistent remaining-fuel states. -/
theorem report_le_count_cube (s fuel threshold B : ℕ) (root : Call)
    (report contribution : ℕ → Call → ℕ)
    (hzero : ∀c,report 0 c=contribution 0 c)
    (hsucc : ∀f c,report (f+1) c=contribution (f+1) c+
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
      rw [hzero]
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
      rw [hsucc,count]
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

end RiemannGaussian.SemiprimeD1ActualCallPolynomialAggregation
