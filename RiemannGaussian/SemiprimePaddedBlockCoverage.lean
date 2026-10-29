/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimePaddedBlockExecution

/-! # Exact row coverage for the executed padded block family
All finite choice below is proof-only comparison to the semantic layout.
-/
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace RiemannGaussian.SemiprimePaddedBlockCoverage
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open Subexp.ConstructivePacking SqrtLog SemiprimePaddedBlockExecution
variable {I U F : Type} [Fintype I] [Fintype U] [DecidableEq I] [DecidableEq U]
variable {r Q R : ℕ}

/-- The semantic block layout used only in comparison proofs. -/
abbrev blockLayout
    (L : Layout.Data (O := ℚ) (G := Fin r) (id : U → U) (id : U → U) Q R)
    (P : PackingData I U) (factor : I → F) (color : F → Fin Q → Fin r)
    (hcolor : ∀ i t, L.color (P.label i) t=color (factor i) t) :=
  LayoutBlocks.data L P.completeBlocks factor color hcolor

omit [Fintype I] in
/-- A universal row zero on this head stays zero after block embedding and
restriction to the copied head. -/
theorem copyRow_block_zero
    (L : Layout.Data (O := ℚ) (G := Fin r) (id : U → U) (id : U → U) Q R)
    (P : PackingData I U) (t : Fin Q) (g : Fin r) (C : U → U → ℤ)
    (a : U) (h : ∀ y : {y : U // L.head t y=g}, C a y.val=0)
    (j : Fin P.blockCount)
    (v : {i : I // LayoutBlocks.copyHead L P.label t i=g}) :
    copyRow P (L.head t) g C (.inl (j,a)) v.val=0 := by
  rw [copyRow,integerPullback_eq]
  have hh : ∀ y : U, L.head t y=LayoutBlocks.copyHead L P.label t (P.vertexAt j y) := by
    intro y
    change L.head t y=L.head t (P.label (P.completeBlocks.embed (j,y)))
    rw [P.completeBlocks.type_eq]
  rw [LayoutHeadPullback.row_restrict (P.vertexAt j) (L.head t)
    (LayoutBlocks.copyHead L P.label t) hh g]
  unfold LayoutPullback.row
  apply Finset.sum_eq_zero
  intro y _
  simp only [h y,ite_self]

/-- Every original assembled source row occurs among the computed padded rows. -/
theorem source_rows_in_padding
    (L : Layout.Data (O := ℚ) (G := Fin r) (id : U → U) (id : U → U) Q R)
    (P : PackingData I U) (factor : I → F) (color : F → Fin Q → Fin r)
    (hcolor : ∀ i t, L.color (P.label i) t=color (factor i) t)
    (t : Fin Q) (g : Fin r) (C : U → U → ℤ)
    (hold : ∀ k : Fin (L.rowCount t g), ∃ a : U,
      ∀ y : {y : U // L.head t y=g}, L.constraints t g k y=C a y.val)
    (k : Fin ((blockLayout L P factor color hcolor).rowCount t g)) :
    ∃ j : (Fin P.blockCount × U) ⊕ I,
      ∀ v : {i : I // (blockLayout L P factor color hcolor).head t i=g},
        (blockLayout L P factor color hcolor).constraints t g k v=
          copyRow P (L.head t) g C j v.val := by
  classical
  let old := (Fintype.equivFin (LayoutBlocks.RowIndex L P.completeBlocks t g)).symm k
  change ∃ j, ∀ v, LayoutBlocks.constraints L P.completeBlocks t g old v = _
  cases old with
  | inl z =>
    obtain ⟨a,ha⟩ := hold z.2
    exact ⟨.inl (z.1,a),fun v => (copyRow_block_spec L P t g C a z.2
      (fun y => (ha y).symm) z.1 v).symm⟩
  | inr i =>
    exact ⟨.inr i.val.val,fun v => (copyRow_leftover_spec L P t g C i v).symm⟩

/-- Every computed padded row is zero or exactly an original assembled row. -/
theorem padding_rows_from_source
    (L : Layout.Data (O := ℚ) (G := Fin r) (id : U → U) (id : U → U) Q R)
    (P : PackingData I U) (factor : I → F) (color : F → Fin Q → Fin r)
    (hcolor : ∀ i t, L.color (P.label i) t=color (factor i) t)
    (t : Fin Q) (g : Fin r) (C : U → U → ℤ)
    (hnew : ∀ a : U,
      (∀ y : {y : U // L.head t y=g}, C a y.val=0) ∨
      (∃ k : Fin (L.rowCount t g), ∀ y : {y : U // L.head t y=g},
        C a y.val=L.constraints t g k y))
    (j : (Fin P.blockCount × U) ⊕ I) :
    (∀ v : {i : I // (blockLayout L P factor color hcolor).head t i=g},
      copyRow P (L.head t) g C j v.val=0) ∨
    (∃ k : Fin ((blockLayout L P factor color hcolor).rowCount t g),
      ∀ v : {i : I // (blockLayout L P factor color hcolor).head t i=g},
        copyRow P (L.head t) g C j v.val=
          (blockLayout L P factor color hcolor).constraints t g k v) := by
  classical
  let e := Fintype.equivFin (LayoutBlocks.RowIndex L P.completeBlocks t g)
  cases j with
  | inl z =>
    rcases hnew z.2 with hz | ⟨k,hk⟩
    · exact Or.inl (copyRow_block_zero L P t g C z.2 hz z.1)
    · right
      refine ⟨e (.inl (z.1,k)),fun v => ?_⟩
      change copyRow P (L.head t) g C (.inl z) v.val=
        LayoutBlocks.constraints L P.completeBlocks t g (e.symm (e (.inl (z.1,k)))) v
      rw [e.symm_apply_apply]
      exact copyRow_block_spec L P t g C z.2 k hk z.1 v
  | inr i =>
    by_cases hi : P.lookup i=none ∧ L.head t (P.label i)=g
    · right
      let v : {i : I // LayoutBlocks.copyHead L P.label t i=g} := ⟨i,hi.2⟩
      let old : {v : {i : I // LayoutBlocks.copyHead L P.label t i=g} //
          v.val ∉ Set.range P.completeBlocks.embed} :=
        ⟨v,(P.lookup_none_iff i).mp hi.1⟩
      refine ⟨e (.inr old),fun w => ?_⟩
      change copyRow P (L.head t) g C (.inr i) w.val=
        LayoutBlocks.constraints L P.completeBlocks t g (e.symm (e (.inr old))) w
      rw [e.symm_apply_apply]
      exact copyRow_leftover_spec L P t g C old w
    · left
      intro v
      exact congrFun (copyRow_leftover_zero P (L.head t) g C i hi) v.val

/-- Padding uses at most twice the actual incidence count, even if the
universal alphabet is larger than the original input. -/
theorem indices_length_le (P : PackingData I U) :
    (indices P).values.length≤2*P.vertices.values.length := by
  have h := Fintype.card_le_of_injective P.completeBlocks.embed P.completeBlocks.embed.injective
  rw [Fintype.card_prod,Fintype.card_fin] at h
  rw [indices_length,FiniteEnumeration.length_eq_card,FiniteEnumeration.length_eq_card]
  omega

end RiemannGaussian.SemiprimePaddedBlockCoverage
