/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceInterpolationExecution
import RiemannGaussian.SemiprimeBinomialExecution

/-! # Actual acquired universal source rows and integer constraints
The parity data are computed by the cached integer solver, not supplied.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeUniversalSourceExecution
open scoped BigOperators
open Polynomial SemiprimeJetArray
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes Subexp.MatrixSupport SqrtLog
open SemiprimeUniversalNumeratorExecution SemiprimeSourceInterpolationExecution
variable {r Q Δ : ℕ}

/-- Actual integer universal entry with computed parity coefficients. -/
def numerator (A R : ℕ) (i : Fin Δ) (t : Fin Q)
    (a y : UniversalType r Q Δ) : ℤ :=
  entry (SemiprimeBinomialExecution.parity A R) i t a y

/-- Actual finite source-row array; all parity inputs are constructed. -/
def universalRow (A R : ℕ) (a : UniversalType r Q 1)
    (y : UniversalType r Q 1) : InverseReport :=
  row (SemiprimeBinomialExecution.parity A R) a 0 y

/-- The computed integer entry is the source numerator. -/
theorem numerator_eq (A R : ℕ) (i : Fin Δ) (t : Fin Q)
    (a y : UniversalType r Q Δ) :
    numerator A R i t a y = LayoutNumerator.entry i t A R a y :=
  entry_eq A _ (SemiprimeBinomialExecution.parity_eq A R) i t a y

/-- Actual array coefficients match every universal source row coefficient through R. -/
theorem universalRow_coefficient (A R : ℕ) (a y : UniversalType r Q 1)
    (k : ℕ) (hk : k<R+1) :
    coefficient (universalRow A R a y).coefficients k =
      ((LayoutUniversal.data A R (SemiprimeSourceLayout.denominatorUnit R) rfl
        (SemiprimeSourceLayout.sampleUnits Q)).row a y).coeff k :=
  universal_coefficient A _ (SemiprimeBinomialExecution.parity_eq A R) a y k hk

/-- The actual root constructor's centered universal row is acquired by the same arrays. -/
theorem source_universal_coefficient (R : ℕ) (a y : UniversalType r Q 1)
    (k : ℕ) (hk : k<R+1) :
    coefficient (universalRow (Subexp.TailInterval.intervalStart r Q R) R a y).coefficients k =
      ((SemiprimeSourceLayout.universalLayout r Q R).row a y).coeff k :=
  universalRow_coefficient _ R a y k hk

/-- Padded full-universal integer constraints, including outside-joint zero columns/rows. -/
def constraint (A R : ℕ) (t : Fin Q) (g : Fin r)
    (a y : UniversalType r Q 1) : ℤ :=
  if a.head t=g ∧ a.slot 0 t≠g then
    if y.head t=g ∧ y.slot 0 t≠g then
      (if a=y then 2^(R-1) else 0)-numerator A R 0 t a y
    else 0
  else 0

/-- Padded constraints are exactly zero extensions of the source's cleared defect. -/
theorem constraint_eq (A R : ℕ) (t : Fin Q) (g : Fin r)
    (a y : UniversalType r Q 1) :
    constraint A R t g a y = SubexpAnnihilation.zeroExtendMatrix (joint t g (0 : Fin 1))
      (LayoutScaledMatrices.clearedDefect (LayoutNumerator.denominator R)
        (LayoutNumerator.joint (0 : Fin 1) t g A R)) a y := by
  unfold constraint SubexpAnnihilation.zeroExtendMatrix
  by_cases ha : a.head t=g ∧ a.slot 0 t≠g
  · by_cases hy : y.head t=g ∧ y.slot 0 t≠g
    · have haj : a ∈ joint t g (0 : Fin 1) := ha
      have hyj : y ∈ joint t g (0 : Fin 1) := hy
      rw [ite_eq_left ha,ite_eq_left hy,dite_eq_left haj,dite_eq_left hyj]
      change (if a=y then 2^(R-1) else 0)-numerator A R 0 t a y =
        (if (⟨a,haj⟩ : Joint t g (0 : Fin 1))=⟨y,hyj⟩ then LayoutNumerator.denominator R else 0)-
          LayoutNumerator.entry 0 t A R a y
      simp only [Subtype.mk.injEq,numerator_eq,LayoutNumerator.denominator]
    · simp [joint,ha,hy]
  · simp [joint,ha]

/-- A column outside the named head has a literal zero padded constraint. -/
theorem constraint_not_head (A R : ℕ) (t : Fin Q) (g : Fin r)
    (a y : UniversalType r Q 1) (hy : y.head t ≠ g) :
    constraint A R t g a y = 0 := by
  by_cases ha : a.head t=g ∧ a.slot 0 t≠g <;> simp [constraint,ha,hy]

/-- A row outside the named joint fibre has a literal zero padded constraint. -/
theorem constraint_not_joint_row (A R : ℕ) (t : Fin Q) (g : Fin r)
    (a y : UniversalType r Q 1) (ha : a ∉ joint t g (0 : Fin 1)) :
    constraint A R t g a y = 0 := by
  have hn : ¬(a.head t=g ∧ a.slot 0 t≠g) := ha
  exact ite_eq_right hn

/-- Restricting the padded matrix recovers the source's actual head-column constraints. -/
theorem constraint_source (A R : ℕ) (t : Fin Q) (g : Fin r)
    (a : Joint t g (0 : Fin 1)) (y : LayoutUniversal.Head t g) :
    constraint A R t g a.val y.val = LayoutUniversal.constraints A R t g a y := by
  rw [constraint_eq]
  unfold LayoutUniversal.constraints LayoutExactBuckets.pulledConstraints
  by_cases hy : y.val.slot 0 t ≠ g
  · let b : Joint t g (0 : Fin 1) := ⟨y.val,⟨y.property,hy⟩⟩
    have hinj : Function.Injective (LayoutUniversal.jointOwner t g) := by
      intro u v h
      apply Subtype.ext
      exact congrArg (fun z : LayoutUniversal.Head t g => z.val) h
    have h := LayoutPullback.row_apply_injective (LayoutUniversal.jointOwner t g) hinj
      (LayoutScaledMatrices.clearedDefect (LayoutNumerator.denominator R)
        (LayoutNumerator.joint (0 : Fin 1) t g A R) a) b
    unfold SubexpAnnihilation.zeroExtendMatrix
    rw [dite_eq_left a.property,dite_eq_left b.property]
    exact h.symm
  · have hyn : y.val ∉ joint t g (0 : Fin 1) := fun h => hy h.2
    rw [SubexpAnnihilation.zeroExtendMatrix_of_column_not_mem _ _ _ _ hyn]
    symm
    apply LayoutPullback.row_eq_zero
    rintro ⟨b,hb⟩
    have hv : b.val=y.val := congrArg Subtype.val hb
    exact hy (hv ▸ b.property.2)

#print axioms source_universal_coefficient
end RiemannGaussian.SemiprimeUniversalSourceExecution
