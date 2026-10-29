/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib

/-!
# Streaming evaluation of Boolean tensor entries

The recursive evaluator computes the genuine multilinear extension at arbitrary
ring inputs while retaining the supplied Boolean entry function. Its instrumented
version records calls at the leaves and recursion depth on the same branches.

This is the local algebraic evaluator used by the proposed large-scope counting
extension. Primitive-machine compilation, entry-evaluator costs, coefficient
heights, workspace and the complete factoring bound are separate obligations.
-/

namespace RiemannGaussian.SemiprimeStreamingTensor
open scoped BigOperators
variable {R : Type*} [CommRing R]

/-- Depth-first multilinear evaluation: no truth-table list is an input. -/
def evaluate : (w : ℕ) → ((Fin w → Bool) → R) → (Fin w → R) → R
  | 0, T, _ => T Fin.elim0
  | w + 1, T, x =>
      (1 - x 0) * evaluate w (fun a => T (Fin.cons false a)) (fun i => x i.succ) +
      x 0 * evaluate w (fun a => T (Fin.cons true a)) (fun i => x i.succ)

/-- Embed a Boolean input as zero or one in the coefficient ring. -/
def bit (b : Bool) : R := if b then 1 else 0

theorem boolean_recovery (w : ℕ) (T : (Fin w → Bool) → R) (a : Fin w → Bool) :
    evaluate w T (fun i => bit (a i)) = T a := by
  induction w with
  | zero =>
    change T Fin.elim0 = T a
    congr 1
    funext i
    exact Fin.elim0 i
  | succ w ih =>
    simp only [evaluate]
    rw [ih, ih]
    have ha : Fin.cons (a 0) (fun i => a i.succ) = a := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    cases h : a 0 <;> simp only [bit, Bool.false_eq_true, ↓reduceIte, sub_zero,
      one_mul, zero_mul, add_zero, sub_self, zero_add]
    · exact congrArg T (by simpa only [h] using ha)
    · exact congrArg T (by simpa only [h] using ha)

/-- Number of leaf evaluations in the complete binary recursion on the arity. -/
def leafCount : ℕ → ℕ
  | 0 => 1
  | w + 1 => leafCount w + leafCount w

/-- Recursion depth of the streaming evaluator on the given arity. -/
def recursionDepth : ℕ → ℕ
  | 0 => 0
  | w + 1 => recursionDepth w + 1

theorem leafCount_eq (w : ℕ) : leafCount w = 2 ^ w := by
  induction w with
  | zero => rfl
  | succ w ih => simp [leafCount, ih, pow_succ, Nat.mul_two]

theorem recursionDepth_eq (w : ℕ) : recursionDepth w = w := by
  induction w with
  | zero => rfl
  | succ w ih => simp [recursionDepth, ih]

/-- Exact tensor-product interpolation formula, without a materialized table. -/
theorem evaluate_eq_sum (w : ℕ) (T : (Fin w → Bool) → R) (x : Fin w → R) :
    evaluate w T x = ∑ a : Fin w → Bool,
      T a * ∏ i, (if a i then x i else 1 - x i) := by
  classical
  induction w with
  | zero =>
    simp only [evaluate, Fintype.prod_empty, mul_one, Fintype.sum_unique]
    congr 1
  | succ w ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (w + 1) => Bool)).sum_comp]
    rw [Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    simp only [Fintype.sum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte]
    conv_rhs => rw [add_comm]
    rw [evaluate, ih, ih]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro a ha
      change _ = T (Fin.cons false a) * _
      ring
    · apply Finset.sum_congr rfl
      intro a ha
      change _ = T (Fin.cons true a) * _
      ring

/-- Instrumented version: each leaf performs the table call and each internal
node combines the values and actual recursive call counts/depths. -/
def evaluateTracked : (w : ℕ) → ((Fin w → Bool) → R) → (Fin w → R) → R × ℕ × ℕ
  | 0, T, _ => (T Fin.elim0, 1, 0)
  | w + 1, T, x =>
      let left := evaluateTracked w (fun a => T (Fin.cons false a)) (fun i => x i.succ)
      let right := evaluateTracked w (fun a => T (Fin.cons true a)) (fun i => x i.succ)
      ((1 - x 0) * left.1 + x 0 * right.1,
        left.2.1 + right.2.1, max left.2.2 right.2.2 + 1)

theorem evaluateTracked_eq (w : ℕ) (T : (Fin w → Bool) → R) (x : Fin w → R) :
    evaluateTracked w T x = (evaluate w T x, 2 ^ w, w) := by
  induction w with
  | zero => rfl
  | succ w ih =>
    simp [evaluateTracked, evaluate, ih, pow_succ, Nat.mul_two]

/-- Exact interpolation together with the evaluator's recursive call/depth counts. -/
theorem evaluateTracked_eq_sum (w : ℕ) (T : (Fin w → Bool) → R) (x : Fin w → R) :
    evaluateTracked w T x =
      (∑ a : Fin w → Bool, T a * ∏ i, (if a i then x i else 1 - x i), 2 ^ w, w) := by
  rw [evaluateTracked_eq, evaluate_eq_sum]

/-- At Boolean inputs the tracked value is the original local tensor entry. -/
theorem evaluateTracked_at_boolean (w : ℕ) (T : (Fin w → Bool) → R)
    (a : Fin w → Bool) :
    evaluateTracked w T (fun i => bit (a i)) = (T a, 2 ^ w, w) := by
  rw [evaluateTracked_eq, boolean_recovery]

/-- Substituting degree-r paths in the streaming multilinear evaluator costs
only the true number of local ports in polynomial degree. -/
theorem natDegree_evaluate_le {C : Type*} [CommRing C] (w : ℕ)
    (T : (Fin w → Bool) → C) (paths : Fin w → Polynomial C) (r : ℕ)
    (hp : ∀ i, (paths i).natDegree ≤ r) :
    (evaluate w (fun a => Polynomial.C (T a)) paths).natDegree ≤ w * r := by
  induction w with
  | zero => simp [evaluate]
  | succ w ih =>
    simp only [evaluate]
    have hsub : ((1 : Polynomial C) - paths 0).natDegree ≤ r :=
      (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) (hp 0))
    apply Polynomial.natDegree_add_le_of_degree_le
    · simpa only [Nat.succ_mul, Nat.add_comm] using
        (Polynomial.natDegree_mul_le).trans
          (Nat.add_le_add hsub (ih _ _ (fun i => hp i.succ)))
    · simpa only [Nat.succ_mul, Nat.add_comm] using
        (Polynomial.natDegree_mul_le).trans
          (Nat.add_le_add (hp 0) (ih _ _ (fun i => hp i.succ)))

/-- A sum of tensor products has degree controlled by total port incidence,
without multiplying maximum arity by the number of tensor vertices. -/
theorem natDegree_sum_product_evaluate_le
    {C E X : Type*} [CommRing C] [Fintype E] [Fintype X]
    (arity : E → ℕ) (T : (e : E) → (Fin (arity e) → Bool) → C)
    (paths : X → (e : E) → Fin (arity e) → Polynomial C) (r : ℕ)
    (hp : ∀ x e i, (paths x e i).natDegree ≤ r) :
    (∑ x, ∏ e, evaluate (arity e) (fun a => Polynomial.C (T e a)) (paths x e)).natDegree
      ≤ (∑ e, arity e) * r := by
  classical
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro x hx
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc
    ∑ e, (evaluate (arity e) (fun a => Polynomial.C (T e a)) (paths x e)).natDegree
        ≤ ∑ e, arity e * r := by
      apply Finset.sum_le_sum
      intro e he
      exact natDegree_evaluate_le _ _ _ _ (hp x e)
    _ = (∑ e, arity e) * r := by rw [Finset.sum_mul]

#print axioms natDegree_evaluate_le
#print axioms natDegree_sum_product_evaluate_le
#print axioms evaluateTracked_eq_sum
#print axioms evaluateTracked_at_boolean
#print axioms evaluateTracked_eq
#print axioms boolean_recovery
#print axioms evaluate_eq_sum
#print axioms leafCount_eq
#print axioms recursionDepth_eq
end RiemannGaussian.SemiprimeStreamingTensor

