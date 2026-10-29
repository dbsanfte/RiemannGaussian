/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeCounterNative
import RiemannGaussian.SemiprimeD1WireKernelPaper

/-! # Original finite wire deformation and its exact Boolean contraction

These are polynomial specifications, not matrices constructed at runtime.
The identity wire and degree contracts are consumed at the later actual sparse
packet embedding join; no tensor coefficient or Hermite answer is assumed.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1Deformation
open scoped BigOperators
open Polynomial SemiprimeStreamingTensor
variable {R : Type*} [CommRing R]

/-- The exact local column form in the original D.8 deformation. -/
noncomputable def rowForm (M : ℕ) (wire : Fin M→Fin M→R[X])
    (bits : Fin M→Bool) (row : Fin M) : R[X] :=
  ∑ column,wire row column*C (bit (bits column))

/-- Original D.8 as streamed multilinear extension, retaining arbitrary row/column tensors. -/
noncomputable def polynomial (M : ℕ) (A B : (Fin M→Bool)→R)
    (wire : Fin M→Fin M→R[X]) : R[X] :=
  ∑ bits : Fin M→Bool,C (B bits)*
    SemiprimeStreamingTensor.evaluate M (fun rows => C (A rows)) (rowForm M wire bits)

/-- The identity wire recovers the ACTUAL Boolean contraction at zero. -/
theorem at_zero (M : ℕ) (A B : (Fin M→Bool)→R) (wire : Fin M→Fin M→R[X])
    (hwire : ∀ i j,(wire i j).eval 0=if i=j then 1 else 0) :
    (polynomial M A B wire).eval 0=∑ bits : Fin M→Bool,A bits*B bits := by
  classical
  rw [polynomial,eval_finsetSum]
  apply Finset.sum_congr rfl
  intro bits _
  rw [eval_mul,eval_C]
  change B bits*(evalRingHom 0)
    (SemiprimeStreamingTensor.evaluate M (fun rows => C (A rows)) (rowForm M wire bits))=_
  rw [SemiprimeCounterNative.evaluate_map]
  have hrow : (fun i => (evalRingHom 0) (rowForm M wire bits i))=
      (fun i => bit (bits i)) := by
    funext i
    simp only [rowForm,coe_evalRingHom,eval_finsetSum,eval_mul,eval_C,hwire]
    simp
  rw [hrow]
  simp only [coe_evalRingHom,eval_C,boolean_recovery]
  exact mul_comm _ _

/-- Every original row path has the wire degree, independent of total wire count. -/
theorem rowForm_degree (M D : ℕ) (wire : Fin M→Fin M→R[X])
    (hwire : ∀ i j,(wire i j).natDegree≤D) (bits : Fin M→Bool) (row : Fin M) :
    (rowForm M wire bits row).natDegree≤D := by
  classical
  apply natDegree_sum_le_of_forall_le
  intro column _
  exact natDegree_mul_le.trans (by simpa only [natDegree_C,add_zero] using hwire row column)

/-- Total deformation degree is M times the actual per-wire degree. -/
theorem degree_le (M D : ℕ) (A B : (Fin M→Bool)→R) (wire : Fin M→Fin M→R[X])
    (hwire : ∀ i j,(wire i j).natDegree≤D) :
    (polynomial M A B wire).natDegree≤M*D := by
  classical
  apply natDegree_sum_le_of_forall_le
  intro bits _
  have h := natDegree_evaluate_le M A (rowForm M wire bits) D (rowForm_degree M D wire hwire bits)
  exact natDegree_mul_le.trans (by simpa only [natDegree_C,zero_add] using h)

end RiemannGaussian.SemiprimeD1Deformation
