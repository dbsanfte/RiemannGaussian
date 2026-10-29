/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeFiniteEnumerations

/-!
# Executed padded integer block constraints

The full universal alphabet and all original incidences form a concrete padded
row index. Invalid universal rows and covered leftover rows are zero. Explicit
enumerations implement the integer pullbacks, avoiding mathematical finite
equivalences in the runtime.
-/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace RiemannGaussian.SemiprimePaddedBlockExecution
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open Subexp.ConstructivePacking SqrtLog

variable {I U V : Type} [DecidableEq I] [DecidableEq U] [DecidableEq V]

/-- Sum one integer row along an owner map using its explicit finite list. -/
def integerPullback (en : FiniteEnumeration I) (owner : I → V) (a : I → ℤ) (v : V) : ℤ :=
  (List.ofFn (fun k : Fin en.values.length =>
    if owner (en.equivFin k)=v then a (en.equivFin k) else 0)).sum

/-- Explicit list summation equals the mathematical owner-fibre pullback. -/
theorem integerPullback_eq [Fintype I] (en : FiniteEnumeration I)
    (owner : I → V) (a : I → ℤ) (v : V) :
    integerPullback en owner a v=LayoutPullback.row owner a v := by
  rw [integerPullback,List.sum_ofFn]
  simpa only [LayoutPullback.row] using en.equivFin.sum_comp
    (fun i => if owner i=v then a i else (0 : ℤ))

/-- Every potential block row and every incidence has a concrete runtime index. -/
def indices (P : PackingData I U) : FiniteEnumeration ((Fin P.blockCount × U) ⊕ I) :=
  SemiprimeFiniteEnumerations.sum
    (SemiprimeFiniteEnumerations.prod (SemiprimeFiniteEnumerations.fin P.blockCount) P.types)
    P.vertices

/-- Actual padded copy constraints, before the original-variable pullback. -/
def copyRow {r : ℕ} (P : PackingData I U) (head : U → Fin r) (g : Fin r)
    (C : U → U → ℤ) : ((Fin P.blockCount × U) ⊕ I) → I → ℤ
  | .inl z => integerPullback P.types (P.vertexAt z.1) (C z.2)
  | .inr i => fun v => if P.lookup i=none ∧ head (P.label i)=g ∧ v=i then 1 else 0

/-- The computed original-coordinate padded matrix. -/
def sourceRow {r : ℕ} (P : PackingData I U) (owner : I → V)
    (head : U → Fin r) (g : Fin r) (C : U → U → ℤ)
    (j : (Fin P.blockCount × U) ⊕ I) : V → ℤ :=
  integerPullback P.vertices owner (copyRow P head g C j)

/-- Concrete finite row numbering with no choice of a finite-type equivalence. -/
def matrix {r : ℕ} (P : PackingData I U) (owner : I → V)
    (head : U → Fin r) (g : Fin r) (C : U → U → ℤ) :
    Fin (indices P).values.length → V → ℤ :=
  fun j => sourceRow P owner head g C ((indices P).equivFin j)

/-- Zero padded universal rows remain zero through block embedding. -/
theorem copyRow_zero {r : ℕ} (P : PackingData I U) (head : U → Fin r) (g : Fin r)
    (C : U → U → ℤ) (j : Fin P.blockCount) (a : U) (h : ∀ y, C a y=0) :
    copyRow P head g C (.inl (j,a))=0 := by
  funext v
  simp [copyRow,integerPullback,h]

/-- Covered incidences or wrong-head leftovers contribute only zero rows. -/
theorem copyRow_leftover_zero {r : ℕ} (P : PackingData I U) (head : U → Fin r)
    (g : Fin r) (C : U → U → ℤ) (i : I)
    (h : ¬(P.lookup i=none ∧ head (P.label i)=g)) :
    copyRow P head g C (.inr i)=0 := by
  funext v
  simp only [copyRow,Pi.zero_apply]
  split_ifs with hv
  · exact False.elim (h ⟨hv.1,hv.2.1⟩)
  · rfl

omit [DecidableEq I] in
/-- The concrete index count is block-count times alphabet size plus incidences. -/
theorem indices_length (P : PackingData I U) :
    (indices P).values.length=P.blockCount*P.types.values.length+P.vertices.values.length := by
  simp [indices,SemiprimeFiniteEnumerations.fin]

section Specification
variable [Fintype I] [Fintype U] {r Q R : ℕ}

omit [Fintype I] in
/-- A block row whose universal head restriction matches the source has exactly
the source's assembled head restriction. The source layout is proof-only. -/
theorem copyRow_block_spec
    (L : Layout.Data (O := ℚ) (G := Fin r) (id : U → U) (id : U → U) Q R)
    (P : PackingData I U) (t : Fin Q) (g : Fin r) (C : U → U → ℤ)
    (a : U) (k : Fin (L.rowCount t g))
    (h : ∀ y : {y : U // L.head t y=g}, C a y.val=L.constraints t g k y)
    (j : Fin P.blockCount)
    (v : {i : I // LayoutBlocks.copyHead L P.label t i=g}) :
    copyRow P (L.head t) g C (.inl (j,a)) v.val =
      LayoutBlocks.constraints L P.completeBlocks t g (.inl (j,k)) v := by
  rw [copyRow,integerPullback_eq]
  have hh : ∀ y : U, L.head t y=LayoutBlocks.copyHead L P.label t (P.vertexAt j y) := by
    intro y
    change L.head t y=L.head t (P.label (P.completeBlocks.embed (j,y)))
    rw [P.completeBlocks.type_eq]
  rw [LayoutHeadPullback.row_restrict (P.vertexAt j) (L.head t)
    (LayoutBlocks.copyHead L P.label t) hh g]
  change LayoutPullback.row (LayoutBlocks.embedHead L P.completeBlocks t g j)
    (fun y => C a y.val) v =
    LayoutPullback.row (LayoutBlocks.embedHead L P.completeBlocks t g j) (L.constraints t g k) v
  congr 2
  exact funext h

omit [Fintype I] in
/-- A real leftover is the original singleton constraint. -/
theorem copyRow_leftover_spec
    (L : Layout.Data (O := ℚ) (G := Fin r) (id : U → U) (id : U → U) Q R)
    (P : PackingData I U) (t : Fin Q) (g : Fin r) (C : U → U → ℤ)
    (i : {v : {i : I // LayoutBlocks.copyHead L P.label t i=g} //
      v.val ∉ Set.range P.completeBlocks.embed})
    (v : {i : I // LayoutBlocks.copyHead L P.label t i=g}) :
    copyRow P (L.head t) g C (.inr i.val.val) v.val =
      LayoutBlocks.constraints L P.completeBlocks t g (.inr i) v := by
  have hi := (P.lookup_none_iff i.val.val).mpr i.property
  have hh : L.head t (P.label i.val.val)=g := i.val.property
  simp only [copyRow,hi,hh,true_and,LayoutBlocks.constraints,Pi.single_apply]
  have he : v.val=i.val.val ↔ i.val=v := by
    constructor
    · intro h
      exact (Subtype.ext h).symm
    · intro h
      exact congrArg Subtype.val h.symm
  simp only [he,eq_comm]

omit [Fintype U] in
/-- Restricting the computed owner pullback gives the exact restricted source
pullback for any matching incidence head row. -/
theorem sourceRow_spec {r : ℕ} (P : PackingData I U) (owner : I → V)
    (head : U → Fin r) (originalHead : V → Fin r)
    (hhead : ∀ i, head (P.label i)=originalHead (owner i))
    (g : Fin r) (C : U → U → ℤ) (j : (Fin P.blockCount × U) ⊕ I)
    (a : {i : I // head (P.label i)=g} → ℤ)
    (ha : ∀ i : {i : I // head (P.label i)=g}, copyRow P head g C j i.val=a i)
    (v : {v : V // originalHead v=g}) :
    sourceRow P owner head g C j v.val=
      LayoutPullback.row (LayoutHeadPullback.headOwner owner
        (fun i => head (P.label i)) originalHead hhead g) a v := by
  rw [sourceRow,integerPullback_eq,LayoutHeadPullback.row_restrict owner
    (fun i => head (P.label i)) originalHead hhead g]
  congr 2
  exact funext ha

end Specification
end RiemannGaussian.SemiprimePaddedBlockExecution
