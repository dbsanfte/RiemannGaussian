/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeLayoutSelection

/-! # Exact original-row padding and integer-kernel transport -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimePaddedConstraintSpan
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open LayoutExactBuckets LayoutRowSelection LayoutRank

/-- Rational casting of one literal integer row. -/
def castRow {V : Type*} (row : V → ℤ) : V → ℚ := fun v => (row v : ℚ)

/-- Integer zero remains the actual rational zero row. -/
theorem castRow_zero {V : Type*} : castRow (0 : V → ℤ)=0 := by
  funext v
  simp only [castRow,Pi.zero_apply,Int.cast_zero]

/-- Adding only duplicate/zero rows and retaining every old row preserves row space. -/
theorem rowSpace_eq_of_padding {O N V : Type*} (old : O → V → ℤ) (new : N → V → ℤ)
    (hnew : ∀ j,new j=0 ∨ ∃ i,new j=old i)
    (hold : ∀ i,∃ j,new j=old i) : rowSpace new=rowSpace old := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    change castRow (new j)∈rowSpace old
    rcases hnew j with hz|⟨i,hi⟩
    · rw [hz,castRow_zero]
      exact Submodule.zero_mem _
    · rw [hi]
      exact Submodule.subset_span ⟨i,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    obtain ⟨j,hj⟩ := hold i
    change castRow (old i)∈rowSpace new
    rw [← hj]
    exact Submodule.subset_span ⟨j,rfl⟩

/-- The actual rational rank is unchanged by exact complete row padding. -/
theorem rowRank_eq_of_padding {O N V : Type*} (old : O → V → ℤ) (new : N → V → ℤ)
    (hnew : ∀ j,new j=0 ∨ ∃ i,new j=old i)
    (hold : ∀ i,∃ j,new j=old i) : rowRank new=rowRank old := by
  exact congrArg (fun S : Submodule ℚ (V → ℚ) => Module.finrank ℚ S)
    (rowSpace_eq_of_padding old new hnew hold)

/-- Complete occurrence alone is enough to transfer old integer-kernel locality. -/
theorem killsIntegerKernel_of_complete {O N V R : Type*} [Fintype V] [CommRing R]
    (old : O → V → ℤ) (new : N → V → ℤ)
    (hold : ∀ i,∃ j,new j=old i) (a : V → R) (ha : KillsIntegerKernel a old) :
    KillsIntegerKernel a new := by
  intro z hz
  apply ha z
  intro i
  obtain ⟨j,hj⟩ := hold i
  have he : signature new z j=signature old z i := by
    exact congrArg (fun row : V → ℤ => ∑ v,row v*z v) hj
  exact he.symm.trans (hz j)

/-- Exact integer signature kernels agree, before any coefficient-ring reduction. -/
theorem integer_kernel_iff {O N V : Type*} [Fintype V]
    (old : O → V → ℤ) (new : N → V → ℤ)
    (hnew : ∀ j,new j=0 ∨ ∃ i,new j=old i)
    (hold : ∀ i,∃ j,new j=old i) (z : V → ℤ) :
    (∀ j,signature new z j=0) ↔ ∀ i,signature old z i=0 := by
  constructor
  · intro hz i
    obtain ⟨j,hj⟩ := hold i
    have he : signature new z j=signature old z i :=
      congrArg (fun row : V → ℤ => ∑ v,row v*z v) hj
    exact he.symm.trans (hz j)
  · intro hz j
    rcases hnew j with hj|⟨i,hi⟩
    · simp only [signature,hj,Pi.zero_apply,zero_mul,Finset.sum_const_zero]
    · have he : signature new z j=signature old z i :=
        congrArg (fun row : V → ℤ => ∑ v,row v*z v) hi
      exact he.trans (hz i)

/-- Executable literal zero-padding/reindexing from a supplied original-row map. -/
def padded {O N V : Type*} (old : O → V → ℤ) (pick : N → Option O) : N → V → ℤ :=
  fun j => match pick j with
    | none => 0
    | some i => old i

/-- The explicit map cannot introduce any non-original, nonzero row. -/
theorem padded_rows {O N V : Type*} (old : O → V → ℤ) (pick : N → Option O) :
    ∀ j,padded old pick j=0 ∨ ∃ i,padded old pick j=old i := by
  intro j
  cases h : pick j with
  | none => exact Or.inl (by simp only [padded,h])
  | some i => exact Or.inr ⟨i,by simp only [padded,h]⟩

/-- Coverage of the public row map provides literal complete old-row occurrence. -/
theorem padded_complete {O N V : Type*} (old : O → V → ℤ) (pick : N → Option O)
    (h : ∀ i,∃ j,pick j=some i) : ∀ i,∃ j,padded old pick j=old i := by
  intro i
  obtain ⟨j,hj⟩ := h i
  exact ⟨j,by simp only [padded,hj]⟩

/-- The explicit original-row/zero constructor has exactly the old rational row space. -/
theorem padded_rowSpace {O N V : Type*} (old : O → V → ℤ) (pick : N → Option O)
    (h : ∀ i,∃ j,pick j=some i) : rowSpace (padded old pick)=rowSpace old :=
  rowSpace_eq_of_padding old _ (padded_rows old pick) (padded_complete old pick h)

/-- Literal complete padding preserves rank without a supplied rank computation. -/
theorem padded_rowRank {O N V : Type*} (old : O → V → ℤ) (pick : N → Option O)
    (h : ∀ i,∃ j,pick j=some i) : rowRank (padded old pick)=rowRank old :=
  rowRank_eq_of_padding old _ (padded_rows old pick) (padded_complete old pick h)

end RiemannGaussian.SemiprimePaddedConstraintSpan
