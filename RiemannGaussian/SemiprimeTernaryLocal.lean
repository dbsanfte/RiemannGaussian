/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib

/-!
# Exact two-branch evaluation of a ternary zero-extension

The value at any input containing symbol2 is zero. Consequently the genuine
three-point interpolation uses only two recursive Boolean table branches.
The core imports Mathlib only and has no source-layout or counter dependency.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeTernaryLocal
open scoped BigOperators
variable {R : Type*} [CommRing R]

/-- The quadratic cardinal for symbol0, using a supplied inverse of2. -/
def delta0 (twoInv x : R) : R := (x-1)*(x-2)*twoInv
/-- The quadratic cardinal for symbol1. -/
def delta1 (x : R) : R := -(x*(x-2))
/-- The quadratic cardinal for symbol2. -/
def delta2 (twoInv x : R) : R := x*(x-1)*twoInv
/-- Three-point scalar cardinal, without a division operation at evaluation time. -/
def cardinal (twoInv : R) (a : Fin 3) (x : R) : R :=
  if a.val=0 then delta0 twoInv x else if a.val=1 then delta1 x else delta2 twoInv x

/-- Every scalar cardinal takes its exact Kronecker value over any ring with unit2. -/
theorem cardinal_recovery (twoInv : R) (htwo : (2 : R)*twoInv=1) (a b : Fin 3) :
    cardinal twoInv a (b.val : R) = if a=b then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> norm_num [cardinal,delta0,delta1,delta2] <;>
    exact htwo

/-- Ternary zero-extension of an actual Boolean table, scanned recursively. -/
def liftTable : (w : ℕ) → ((Fin w → Bool) → R) → (Fin w → Fin 3) → R
  | 0, T, _ => T Fin.elim0
  | w+1, T, a =>
      if (a 0).val=0 then liftTable w (fun b => T (Fin.cons false b)) (fun i => a i.succ)
      else if (a 0).val=1 then liftTable w (fun b => T (Fin.cons true b)) (fun i => a i.succ)
      else 0

/-- Prefixing a Boolean zero selects the actual false table branch. -/
theorem liftTable_zero (w : ℕ) (T : (Fin (w+1) → Bool) → R) (a : Fin w → Fin 3) :
    liftTable (w+1) T (Fin.cons 0 a)=liftTable w (fun b => T (Fin.cons false b)) a := rfl
/-- Prefixing a Boolean one selects the actual true table branch. -/
theorem liftTable_one (w : ℕ) (T : (Fin (w+1) → Bool) → R) (a : Fin w → Fin 3) :
    liftTable (w+1) T (Fin.cons 1 a)=liftTable w (fun b => T (Fin.cons true b)) a := rfl
/-- Every symbol2 prefix kills the whole subtree identically. -/
theorem liftTable_two (w : ℕ) (T : (Fin (w+1) → Bool) → R) (a : Fin w → Fin 3) :
    liftTable (w+1) T (Fin.cons 2 a)=0 := rfl

/-- The Boolean projection used by the public ternary checker. -/
def project (a : Fin 3) : Bool := decide (a.val=1)

/-- The recursive lift is exactly zero outside the Boolean subcube. -/
theorem liftTable_formula (w : ℕ) (T : (Fin w → Bool) → R) (a : Fin w → Fin 3) :
    liftTable w T a=if (∀ i, (a i).val<2) then T (fun i => project (a i)) else 0 := by
  induction w with
  | zero =>
    simp only [liftTable,IsEmpty.forall_iff,ite_true]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ w ih =>
    have hp : Fin.cons (project (a 0)) (fun i => project (a i.succ))=(fun i => project (a i)) := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [← hp]
    generalize h : a 0 = c
    fin_cases c <;> simp [liftTable,Fin.forall_fin_succ,h,project,ih]

/-- Actual depth-first two-branch evaluator. The shared difference x−2 is cached. -/
def evaluate (twoInv : R) : (w : ℕ) → ((Fin w → Bool) → R) → (Fin w → R) → R
  | 0, T, _ => T Fin.elim0
  | w+1, T, x =>
      let lo := evaluate twoInv w (fun a => T (Fin.cons false a)) (fun i => x i.succ)
      let hi := evaluate twoInv w (fun a => T (Fin.cons true a)) (fun i => x i.succ)
      let value := x 0
      let minusOne := value-1
      let minusTwo := value-2
      let c0 := minusOne*minusTwo*twoInv
      let c1 := -(value*minusTwo)
      c0*lo+c1*hi

/-- Mathematical full ternary interpolation; no expanded table is an evaluator input. -/
noncomputable def interpolate (twoInv : R) (w : ℕ) (T : (Fin w → Fin 3) → R) (x : Fin w → R) : R :=
  ∑ a : Fin w → Fin 3, T a*∏ i, cardinal twoInv (a i) (x i)

/-- Full interpolation splits into the actual three scalar cardinals. -/
theorem interpolate_succ (twoInv : R) (w : ℕ) (T : (Fin (w+1) → Fin 3) → R) (x : Fin (w+1) → R) :
    interpolate twoInv (w+1) T x =
      delta0 twoInv (x 0)*interpolate twoInv w (fun a => T (Fin.cons 0 a)) (fun i => x i.succ)+
      delta1 (x 0)*interpolate twoInv w (fun a => T (Fin.cons 1 a)) (fun i => x i.succ)+
      delta2 twoInv (x 0)*interpolate twoInv w (fun a => T (Fin.cons 2 a)) (fun i => x i.succ) := by
  classical
  unfold interpolate
  rw [← (Fin.consEquiv (fun _ : Fin (w+1) => Fin 3)).sum_comp,Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
  have hb (c : Fin 3) :
      (∑ a : Fin w → Fin 3, T (Fin.cons c a)*(cardinal twoInv c (x 0)*∏ i, cardinal twoInv (a i) (x i.succ))) =
        cardinal twoInv c (x 0)*(∑ a : Fin w → Fin 3,T (Fin.cons c a)*∏ i,cardinal twoInv (a i) (x i.succ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [Fin.sum_univ_three]
  change (∑ a : Fin w → Fin 3, T (Fin.cons 0 a)*(cardinal twoInv 0 (x 0)*∏ i,cardinal twoInv (a i) (x i.succ)))+
    (∑ a : Fin w → Fin 3, T (Fin.cons 1 a)*(cardinal twoInv 1 (x 0)*∏ i,cardinal twoInv (a i) (x i.succ)))+
    (∑ a : Fin w → Fin 3, T (Fin.cons 2 a)*(cardinal twoInv 2 (x 0)*∏ i,cardinal twoInv (a i) (x i.succ)))=_
  rw [hb 0,hb 1,hb 2]
  rfl

/-- A zero table contributes identically zero, including the omitted symbol2 branch. -/
theorem interpolate_zero (twoInv : R) (w : ℕ) (x : Fin w → R) :
    interpolate twoInv w (fun _ => 0) x=0 := by simp [interpolate]

/-- The TWO-branch evaluator equals the complete THREE-point tensor interpolation. -/
theorem evaluate_eq_interpolate (twoInv : R) (w : ℕ) (T : (Fin w → Bool) → R) (x : Fin w → R) :
    evaluate twoInv w T x=interpolate twoInv w (liftTable w T) x := by
  induction w with
  | zero =>
    simp only [evaluate,interpolate,Fintype.prod_empty,mul_one,Fintype.sum_unique,liftTable]
  | succ w ih =>
    rw [interpolate_succ]
    simp only [liftTable_zero,liftTable_one,liftTable_two,interpolate_zero,mul_zero,add_zero]
    rw [← ih,← ih]
    rfl

/-- Exact interpolation recovery at every ternary grid point. -/
theorem interpolate_recovery (twoInv : R) (htwo : (2 : R)*twoInv=1)
    (w : ℕ) (T : (Fin w → Fin 3) → R) (a : Fin w → Fin 3) :
    interpolate twoInv w T (fun i => (a i).val)=T a := by
  classical
  unfold interpolate
  rw [Finset.sum_eq_single a]
  · simp only [cardinal_recovery twoInv htwo,ite_true,Finset.prod_const_one,mul_one]
  · intro b _ hba
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hba
    have hz : (∏ j, cardinal twoInv (b j) ((a j).val : R))=0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [cardinal_recovery twoInv htwo]; simp only [hi,ite_false])
    rw [hz,mul_zero]
  · simp

/-- The actual two-branch code recovers the zero-extended Boolean table exactly. -/
theorem ternary_recovery (twoInv : R) (htwo : (2 : R)*twoInv=1)
    (w : ℕ) (T : (Fin w → Bool) → R) (a : Fin w → Fin 3) :
    evaluate twoInv w T (fun i => (a i).val)=liftTable w T a := by
  rw [evaluate_eq_interpolate,interpolate_recovery twoInv htwo]

/-- The two-branch interpolant has twice the substituted local incidence degree. -/
theorem natDegree_evaluate_le {C : Type*} [CommRing C] (twoInv : C)
    (w : ℕ) (T : (Fin w → Bool) → C) (paths : Fin w → Polynomial C) (r : ℕ)
    (hp : ∀ i, (paths i).natDegree≤r) :
    (evaluate (Polynomial.C twoInv) w (fun a => Polynomial.C (T a)) paths).natDegree≤2*w*r := by
  induction w with
  | zero => simp [evaluate]
  | succ w ih =>
    have h1 : (paths 0-1).natDegree≤r := (Polynomial.natDegree_sub_le _ _).trans (max_le (hp 0) (by simp))
    have h2 : (paths 0-2).natDegree≤r := (Polynomial.natDegree_sub_le _ _).trans (max_le (hp 0) (by simp))
    have h0 : (delta0 (Polynomial.C twoInv) (paths 0)).natDegree≤2*r := by
      unfold delta0
      have hm : ((paths 0-1)*(paths 0-2)).natDegree≤r+r := (Polynomial.natDegree_mul_le).trans (Nat.add_le_add h1 h2)
      exact (Polynomial.natDegree_mul_le).trans (by simpa only [Polynomial.natDegree_C,add_zero,two_mul] using hm)
    have ht : (delta1 (paths 0)).natDegree≤2*r := by
      unfold delta1
      rw [Polynomial.natDegree_neg]
      simpa only [two_mul] using (Polynomial.natDegree_mul_le).trans (Nat.add_le_add (hp 0) h2)
    change (delta0 (Polynomial.C twoInv) (paths 0)*evaluate (Polynomial.C twoInv) w
      (fun a => Polynomial.C (T (Fin.cons false a))) (fun i => paths i.succ)+
      delta1 (paths 0)*evaluate (Polynomial.C twoInv) w
      (fun a => Polynomial.C (T (Fin.cons true a))) (fun i => paths i.succ)).natDegree≤_
    apply Polynomial.natDegree_add_le_of_degree_le
    · exact (Polynomial.natDegree_mul_le).trans ((Nat.add_le_add h0
        (ih _ _ (fun i => hp i.succ))).trans_eq (by ring))
    · exact (Polynomial.natDegree_mul_le).trans ((Nat.add_le_add ht
        (ih _ _ (fun i => hp i.succ))).trans_eq (by ring))

/-- Full sums/products retain a bound in TOTAL incidence, not maximum-arity times factor count. -/
theorem natDegree_sum_product_evaluate_le {C E A : Type*} [CommRing C] [Fintype E] [Fintype A]
    (twoInv : C) (arity : E → ℕ) (T : (e : E) → (Fin (arity e) → Bool) → C)
    (paths : A → (e : E) → Fin (arity e) → Polynomial C) (r : ℕ)
    (hp : ∀ a e i, (paths a e i).natDegree≤r) :
    (∑ a, ∏ e, evaluate (Polynomial.C twoInv) (arity e) (fun b => Polynomial.C (T e b)) (paths a e)).natDegree
      ≤2*(∑ e, arity e)*r := by
  classical
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro a _
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc
    _ ≤ ∑ e, 2*arity e*r := Finset.sum_le_sum (fun e _ => natDegree_evaluate_le _ _ _ _ _ (hp a e))
    _ = _ := by rw [← Finset.sum_mul,← Finset.mul_sum]

end RiemannGaussian.SemiprimeTernaryLocal
