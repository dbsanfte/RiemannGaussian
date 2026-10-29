/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeUniversalSourceExecution

/-! # Proof-only comparison of padded universal rows and original finite source indices
The actual runtime supplier enumerates all universal words. These equivalences
are used only to prove that its extra rows are zero and that no original row is lost.
-/
set_option autoImplicit false
noncomputable section
namespace RiemannGaussian.SemiprimeUniversalConstraintPadding
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes SqrtLog SemiprimeUniversalSourceExecution
variable {r Q : ℕ}

/-- The exact universal source layout, at any supplied spectral interval. -/
abbrev layout (r Q A R : ℕ) :=
  LayoutUniversal.data A R (SemiprimeSourceLayout.denominatorUnit R) rfl
    (SemiprimeSourceLayout.sampleUnits Q) (r := r)

/-- Proof-only inverse of the source's finite original constraint reindexing. -/
def sourceJoint (A R : ℕ) (t : Fin Q) (g : Fin r)
    (k : Fin ((layout r Q A R).rowCount t g)) : Joint t g (0 : Fin 1) :=
  (Fintype.equivFin (Joint t g (0 : Fin 1))).symm k

/-- Proof-only source row index for one actual joint word. -/
def jointIndex (A R : ℕ) (t : Fin Q) (g : Fin r)
    (a : Joint t g (0 : Fin 1)) : Fin ((layout r Q A R).rowCount t g) :=
  Fintype.equivFin (Joint t g (0 : Fin 1)) a

/-- Original indexed row values equal the corresponding full-universal padded row. -/
theorem sourceJoint_constraint (A R : ℕ) (t : Fin Q) (g : Fin r)
    (k : Fin ((layout r Q A R).rowCount t g))
    (y : {y : UniversalType r Q 1 // (layout r Q A R).head t y=g}) :
    (layout r Q A R).constraints t g k y =
      constraint A R t g (sourceJoint A R t g k).val y.val :=
  (constraint_source A R t g (sourceJoint A R t g k) y).symm

/-- The two source index maps are inverse, without any value-side row rescaling. -/
theorem sourceJoint_jointIndex (A R : ℕ) (t : Fin Q) (g : Fin r)
    (a : Joint t g (0 : Fin 1)) :
    sourceJoint A R t g (jointIndex A R t g a)=a :=
  (Fintype.equivFin (Joint t g (0 : Fin 1))).symm_apply_apply a

/-- Every source finite row occurs literally among padded rows. -/
theorem source_rows_in_padding (A R : ℕ) (t : Fin Q) (g : Fin r)
    (k : Fin ((layout r Q A R).rowCount t g)) :
    ∃ a : UniversalType r Q 1,
      ∀ y : {y : UniversalType r Q 1 // (layout r Q A R).head t y=g},
        (layout r Q A R).constraints t g k y=constraint A R t g a y.val :=
  ⟨(sourceJoint A R t g k).val, sourceJoint_constraint A R t g k⟩

/-- Every padded row is either zero or literally one original indexed source row. -/
theorem padding_rows_from_source (A R : ℕ) (t : Fin Q) (g : Fin r)
    (a : UniversalType r Q 1) :
    (∀ y : {y : UniversalType r Q 1 // (layout r Q A R).head t y=g},
      constraint A R t g a y.val=0) ∨
    (∃ k : Fin ((layout r Q A R).rowCount t g),
      ∀ y : {y : UniversalType r Q 1 // (layout r Q A R).head t y=g},
        constraint A R t g a y.val=(layout r Q A R).constraints t g k y) := by
  classical
  by_cases ha : a ∈ joint t g (0 : Fin 1)
  · right
    refine ⟨jointIndex A R t g ⟨a,ha⟩,fun y => ?_⟩
    have h := sourceJoint_constraint A R t g (jointIndex A R t g ⟨a,ha⟩) y
    rw [sourceJoint_jointIndex] at h
    exact h.symm
  · exact Or.inl (fun y => constraint_not_joint_row A R t g a y.val ha)

/-- The source-row cover specializes to the constructor's actual centered interval. -/
theorem actual_source_rows_in_padding (R : ℕ) (t : Fin Q) (g : Fin r)
    (k : Fin ((SemiprimeSourceLayout.universalLayout r Q R).rowCount t g)) :
    ∃ a : UniversalType r Q 1,
      ∀ y : {y : UniversalType r Q 1 // (SemiprimeSourceLayout.universalLayout r Q R).head t y=g},
        (SemiprimeSourceLayout.universalLayout r Q R).constraints t g k y=
          constraint (Subexp.TailInterval.intervalStart r Q R) R t g a y.val :=
  source_rows_in_padding _ R t g k

/-- The padded-row cover also specializes to the actual centered source constructor. -/
theorem actual_padding_rows_from_source (R : ℕ) (t : Fin Q) (g : Fin r)
    (a : UniversalType r Q 1) :
    (∀ y : {y : UniversalType r Q 1 // (SemiprimeSourceLayout.universalLayout r Q R).head t y=g},
      constraint (Subexp.TailInterval.intervalStart r Q R) R t g a y.val=0) ∨
    (∃ k : Fin ((SemiprimeSourceLayout.universalLayout r Q R).rowCount t g),
      ∀ y : {y : UniversalType r Q 1 // (SemiprimeSourceLayout.universalLayout r Q R).head t y=g},
        constraint (Subexp.TailInterval.intervalStart r Q R) R t g a y.val=
          (SemiprimeSourceLayout.universalLayout r Q R).constraints t g k y) :=
  padding_rows_from_source _ R t g a

#print axioms actual_padding_rows_from_source
end RiemannGaussian.SemiprimeUniversalConstraintPadding
