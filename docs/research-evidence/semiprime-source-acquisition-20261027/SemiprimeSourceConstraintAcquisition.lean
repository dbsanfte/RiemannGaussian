/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimePaddedBlockExecution
import RiemannGaussian.SemiprimeUniversalConstraintPadding
import RiemannGaussian.SemiprimePaddedBlockCoverage

/-! # Actual original-variable padded integer source matrix
All runtime inputs are finite enumerations, owner/factor maps and public scalars.
The polynomial layout is used only in the semantic statements.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceConstraintAcquisition
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes SqrtLog Subexp.ConstructivePacking
open SemiprimeFiniteEnumerations SemiprimePaddedBlockExecution
variable {I V E : Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable {r Q : ℕ}

/-- The actual searched complete blocks and leftovers. -/
def packing (owner : I → V) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I V E r Q) (ε : ℚ) :=
  searchPacking owner factor en ε

/-- Literal computed original-variable head labels. -/
def head (owner : I → V) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I V E r Q) (ε : ℚ) (t : Fin Q) (v : V) : Fin r :=
  searchWords owner factor en ε (.inl v) t

/-- Explicit complete-block/universal-word plus incidence row enumeration. -/
def rowIndices (owner : I → V) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I V E r Q) (ε : ℚ) :=
  indices (packing owner factor en ε)

/-- Actual padded integer matrix, truncated to its original head columns. -/
def matrix (owner : I → V) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I V E r Q) (ε : ℚ) (R : ℕ)
    (t : Fin Q) (g : Fin r) : Fin (rowIndices owner factor en ε).values.length → V → ℤ :=
  let P := packing owner factor en ε
  let A := Subexp.TailInterval.intervalStart r Q R
  fun j v => if head owner factor en ε t v=g then
    SemiprimePaddedBlockExecution.matrix P owner (fun u => u.head t) g
      (SemiprimeUniversalSourceExecution.constraint A R t g) j v else 0

/-- Actual zero columns outside the named original head. -/
theorem matrix_not_head (owner : I → V) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I V E r Q) (ε : ℚ) (R : ℕ)
    (t : Fin Q) (g : Fin r) (j : Fin (rowIndices owner factor en ε).values.length) (v : V)
    (hv : head owner factor en ε t v≠g) : matrix owner factor en ε R t g j v=0 :=
  ite_eq_right hv

omit [DecidableEq I] in
/-- The computed packing's head labels are literally the owner-variable labels. -/
theorem packing_head (owner : I → V) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I V E r Q) (ε : ℚ) (t : Fin Q) (i : I) :
    ((packing owner factor en ε).label i).head t=head owner factor en ε t (owner i) := rfl

/-- Matrix lookup at an enumerated raw padded index, on its actual original head. -/
theorem matrix_raw (owner : I → V) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I V E r Q) (ε : ℚ) (R : ℕ)
    (t : Fin Q) (g : Fin r)
    (j : (Fin (packing owner factor en ε).blockCount × UniversalType r Q 1) ⊕ I)
    (v : V) (hv : head owner factor en ε t v=g) :
    matrix owner factor en ε R t g ((rowIndices owner factor en ε).equivFin.symm j) v =
      sourceRow (packing owner factor en ε) owner (fun u => u.head t) g
        (SemiprimeUniversalSourceExecution.constraint (Subexp.TailInterval.intervalStart r Q R) R t g) j v := by
  change (if head owner factor en ε t v=g then
    sourceRow (packing owner factor en ε) owner (fun u => u.head t) g
      (SemiprimeUniversalSourceExecution.constraint (Subexp.TailInterval.intervalStart r Q R) R t g)
      ((rowIndices owner factor en ε).equivFin ((rowIndices owner factor en ε).equivFin.symm j)) v else 0) = _
  rw [ite_eq_left hv,Equiv.apply_symm_apply]

noncomputable section
/-- Exact source copy layout, used only in refinement proofs. -/
abbrev copyLayout (owner : I → V) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I V E r Q) (ε : ℚ) (R : ℕ) :=
  LayoutBlocks.data (SemiprimeSourceLayout.universalLayout r Q R)
    (packing owner factor en ε).completeBlocks factor
    (fun e => searchWords owner factor en ε (.inr e)) (by intro i t; rfl)

/-- Every original searched source row is present in the executed integer matrix. -/
theorem source_rows_in_matrix (owner : I → V) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I V E r Q) (ε : ℚ) (R : ℕ)
    (t : Fin Q) (g : Fin r)
    (k : Fin ((SemiprimeSourceLayout.builtLayout owner factor en ε R).rowCount t g)) :
    ∃ j : Fin (rowIndices owner factor en ε).values.length,
      ∀ v : {v : V // (SemiprimeSourceLayout.builtLayout owner factor en ε R).head t v=g},
        (SemiprimeSourceLayout.builtLayout owner factor en ε R).constraints t g k v=
          matrix owner factor en ε R t g j v.val := by
  classical
  let L := SemiprimeSourceLayout.universalLayout r Q R
  let P := packing owner factor en ε
  let C := SemiprimeUniversalSourceExecution.constraint (Subexp.TailInterval.intervalStart r Q R) R t g
  have hc : ∀ i t, L.color (P.label i) t=searchWords owner factor en ε (.inr (factor i)) t := by
    intro i t
    rfl
  obtain ⟨j,hj⟩ := SemiprimePaddedBlockCoverage.source_rows_in_padding L P factor
    (fun e => searchWords owner factor en ε (.inr e)) hc t g C
    (SemiprimeUniversalConstraintPadding.actual_source_rows_in_padding R t g) k
  refine ⟨(rowIndices owner factor en ε).equivFin.symm j,fun v => ?_⟩
  have hv : head owner factor en ε t v.val=g := v.property
  rw [matrix_raw owner factor en ε R t g j v.val hv]
  have h := sourceRow_spec P owner (fun u => u.head t) (head owner factor en ε t)
    (packing_head owner factor en ε t) g C j
    ((copyLayout owner factor en ε R).constraints t g k) (fun i => (hj i).symm) v
  exact h.symm

/-- Each acquired row is zero or a literal original source row after the owner pullback. -/
theorem matrix_rows_from_source (owner : I → V) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I V E r Q) (ε : ℚ) (R : ℕ)
    (t : Fin Q) (g : Fin r) (j : Fin (rowIndices owner factor en ε).values.length) :
    (∀ v : {v : V // (SemiprimeSourceLayout.builtLayout owner factor en ε R).head t v=g},
      matrix owner factor en ε R t g j v.val=0) ∨
    (∃ k : Fin ((SemiprimeSourceLayout.builtLayout owner factor en ε R).rowCount t g),
      ∀ v : {v : V // (SemiprimeSourceLayout.builtLayout owner factor en ε R).head t v=g},
        matrix owner factor en ε R t g j v.val=
          (SemiprimeSourceLayout.builtLayout owner factor en ε R).constraints t g k v) := by
  classical
  let L := SemiprimeSourceLayout.universalLayout r Q R
  let P := packing owner factor en ε
  let C := SemiprimeUniversalSourceExecution.constraint (Subexp.TailInterval.intervalStart r Q R) R t g
  let a := (rowIndices owner factor en ε).equivFin j
  have hc : ∀ i t, L.color (P.label i) t=searchWords owner factor en ε (.inr (factor i)) t := by
    intro i t
    rfl
  have he : (rowIndices owner factor en ε).equivFin.symm a=j :=
    (rowIndices owner factor en ε).equivFin.symm_apply_apply j
  rcases SemiprimePaddedBlockCoverage.padding_rows_from_source L P factor
    (fun e => searchWords owner factor en ε (.inr e)) hc t g C
    (SemiprimeUniversalConstraintPadding.actual_padding_rows_from_source R t g) a with hz | ⟨k,hk⟩
  · left
    intro v
    have hv : head owner factor en ε t v.val=g := v.property
    rw [← he,matrix_raw owner factor en ε R t g a v.val hv]
    have h := sourceRow_spec P owner (fun u => u.head t) (head owner factor en ε t)
      (packing_head owner factor en ε t) g C a (fun _ => 0) hz v
    simpa only [LayoutPullback.row,ite_self,Finset.sum_const_zero] using h
  · right
    refine ⟨k,fun v => ?_⟩
    have hv : head owner factor en ε t v.val=g := v.property
    rw [← he,matrix_raw owner factor en ε R t g a v.val hv]
    have h := sourceRow_spec P owner (fun u => u.head t) (head owner factor en ε t)
      (packing_head owner factor en ε t) g C a
      ((copyLayout owner factor en ε R).constraints t g k) hk v
    exact h

end

end RiemannGaussian.SemiprimeSourceConstraintAcquisition
