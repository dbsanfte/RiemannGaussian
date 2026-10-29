/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketModeOriginal
import RiemannGaussian.SemiprimeD1PacketEntryComponents

/-! # Original-beta source product equals the actual supported exponent product
The base at each mode is constructed from the executed local column terms.
Original acquired tuple membership discharges finite support/length internally;
no source-factor answer or requested exponent catalogue is supplied.
-/
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace RiemannGaussian.SemiprimeD1PacketSourceProduct
open scoped BigOperators
open SemiprimeD1PacketModeProjection SemiprimeD1PacketEntryBits
open SemiprimeD1PacketEntryValue SemiprimeD1PacketEntryComponents SemiprimeD1PacketEntryInputs
open SemiprimeD1JetAxes SemiprimeD1JetInterpretation
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Actual acquired source base, zero past the finite descriptor cache. -/
def sourceBase (ctx : Context) (a : ℕ) (i : Fin a) (columns : List (Wire a))
    (cache : SemiprimeD1PacketModeMask.Cache) (j : ℕ) : Carrier ctx :=
  match cache.items[j]? with
  | none => 0
  | some item => (columns.map (fun column => interpret ctx (sourceTerm ctx a i item column).words)).sum

/-- The literal indexed list is exactly its complete ordered finite-index enumeration. -/
theorem zipIdx_ofFn {A : Type*} (items : List A) :
    items.zipIdx 0=List.ofFn (fun j : Fin items.length => (items[j.val],j.val)) := by
  apply List.ext_getElem
  · simp only [List.length_zipIdx,List.length_ofFn]
  · intro j hj hj'
    simp only [List.getElem_zipIdx,List.getElem_ofFn,Nat.zero_add]

/-- Every actual global source slot occurs once with its ORIGINAL beta exponent. -/
theorem sourceProduct_finite (ctx : Context) (a : ℕ) (i : Fin a) (columns : List (Wire a))
    (beta : List ℕ) (cache : SemiprimeD1PacketModeMask.Cache) (hpos : ctx.Positive) :
    interpret ctx (sourceProduct ctx a i columns beta cache.items 0).words=
      ∏ j : Fin cache.items.length,
        if j.val∈sourceSet cache then sourceBase ctx a i columns cache j.val ^ beta.getD j.val 0 else 1 := by
  rw [sourceProduct_value ctx _ _ _ _ _ _ hpos,zipIdx_ofFn,List.map_ofFn,List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro j _
  dsimp only [Function.comp_def]
  rw [sourceFactor_value ctx a i columns beta j.val cache.items[j.val] hpos]
  simp only [sourceSet,Set.mem_ofPred_eq,sourceEnabled,sourceBase,List.getElem?_eq_getElem j.isLt,
    List.getD_eq_getElem?_getD]

/-- Actual finite source-product execution equals the supported Finsupp product.
The sole generic support premise is later discharged from actual acquired tuples. -/
theorem sourceProduct_toFinsupp (ctx : Context) (a : ℕ) (i : Fin a) (columns : List (Wire a))
    (beta : List ℕ) (cache : SemiprimeD1PacketModeMask.Cache) (hpos : ctx.Positive)
    (hlen : beta.length≤cache.items.length) :
    interpret ctx (sourceProduct ctx a i columns beta cache.items 0).words=
      beta.toFinsupp.prod (fun j exponent =>
        if j∈sourceSet cache then sourceBase ctx a i columns cache j ^ exponent else 1) := by
  have hs : beta.toFinsupp.support⊆Finset.range cache.items.length := by
    intro j hj
    apply Finset.mem_range.mpr
    by_contra hn
    have hz := List.toFinsupp_apply_le beta j (hlen.trans (Nat.le_of_not_gt hn))
    exact (Finsupp.mem_support_iff.mp hj) hz
  have hp := Finsupp.prod_of_support_subset beta.toFinsupp hs
    (fun j exponent => if j∈sourceSet cache then sourceBase ctx a i columns cache j ^ exponent else 1)
    (by intro j _;simp only [pow_zero,ite_self])
  rw [hp,Finset.prod_range]
  simpa only [List.toFinsupp_apply] using sourceProduct_finite ctx a i columns beta cache hpos

/-- Every ACTUALLY acquired original query has exactly the actual descriptor length. -/
theorem original_query_length (n F r a u p : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (i : Fin a)
    (packet : Fin (SemiprimeD1OriginalModeAcquisition.acquire n F r a u i.val p arity owner).packets.state.packets.length)
    (g : Fin r) (beta : List ℕ)
    (hb : beta∈(SemiprimeD1OriginalModeAcquisition.acquire n F r a u i.val p arity owner).modes.values) :
    beta.length=(SemiprimeD1PacketModeMask.fromModes
      (SemiprimeD1OriginalModeAcquisition.acquire n F r a u i.val p arity owner) packet i g).items.length := by
  have hm := (SemiprimeD1OriginalModeAcquisition.modes_correct n F r a u i.val p arity owner beta).1.mp hb
  have hlen := hm.1
  simp only [SemiprimeD1ModeCatalog.weights,List.length_map,SemiprimeD1ModeCatalog.catalog_length] at hlen
  have hc := congrArg List.length (SemiprimeD1PacketModeMask.fromModes_catalogue
    (SemiprimeD1OriginalModeAcquisition.acquire n F r a u i.val p arity owner) packet i g)
  simp only [List.length_map,SemiprimeD1ModeCatalog.catalog_length] at hc
  rw [SemiprimeD1OriginalModeAcquisition.precision_original] at hc
  exact hlen.trans hc.symm

/-- Closed original-query product identity: actual membership replaces length advice. -/
theorem original_source_product (ctx : Context) (n F r a u p : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (i : Fin a)
    (packet : Fin (SemiprimeD1OriginalModeAcquisition.acquire n F r a u i.val p arity owner).packets.state.packets.length)
    (g : Fin r) (columns : List (Wire a)) (beta : List ℕ)
    (hb : beta∈(SemiprimeD1OriginalModeAcquisition.acquire n F r a u i.val p arity owner).modes.values)
    (hpos : ctx.Positive) :
    let cache := SemiprimeD1PacketModeMask.fromModes
      (SemiprimeD1OriginalModeAcquisition.acquire n F r a u i.val p arity owner) packet i g
    interpret ctx (sourceProduct ctx a i columns beta cache.items 0).words=
      beta.toFinsupp.prod (fun j exponent =>
        if j∈sourceSet cache then sourceBase ctx a i columns cache j ^ exponent else 1) := by
  exact sourceProduct_toFinsupp ctx a i columns beta _ hpos
    (original_query_length n F r a u p arity owner i packet g beta hb).le

end
end RiemannGaussian.SemiprimeD1PacketSourceProduct
