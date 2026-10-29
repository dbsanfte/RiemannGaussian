/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketInventory

/-! # Original acquired-pair row-reader refinement
All dictionary/palette assumptions in the generic parser are discharged using
actual selected IDs and the same once-acquired original row dictionary.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1PacketRowsOriginal
open SemiprimeD1PacketRows
open SemiprimeD1IncidenceAcquisition
open SemiprimeSourceHistogramTrie (stored)

/-- Actual valid original IDs give exactly their two original palette rows. -/
theorem read_ids (r a : ℕ) [NeZero r] (leftId rightId : List Bool)
    (hl : leftId∈(SemiprimeSourceCompactWordBank.acquire r a).ids)
    (hr : rightId∈(SemiprimeSourceCompactWordBank.acquire r a).ids) :
    let out := read (SemiprimeSourceHistogramRows.acquire r a) a
      (SemiprimeSourceHistogramKeyBits.frame leftId rightId)
    out.left=SemiprimeD1OrientationPalette.fields (SemiprimeSourceWordBankSemantics.decode r a leftId) ∧
    out.right=SemiprimeD1OrientationPalette.fields (SemiprimeSourceWordBankSemantics.decode r a rightId) ∧
    out.valid=true := by
  dsimp only
  have hlr := original_fields r a leftId hl
  have hrr := original_fields r a rightId hr
  simp only [SemiprimeD1PacketRows.read,SemiprimeSourceHistogramKeyBits.split_frame,hlr.1,hlr.2,hrr.1,hrr.2,
    Bool.and_self]
  simp

/-- Literal actual selected-pair reader, using the retained acquired dictionary. -/
def originalRead (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (i : (e : Fin F)×Fin (arity e)) : PairRows :=
  read (acquire n F r a arity owner).selection.cache.rows.source.dictionary a
    (originalKey n F r a arity owner i)

/-- Every original real port reads precisely its selected two label rows. -/
theorem original_read (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (i : (e : Fin F)×Fin (arity e)) :
    let out := originalRead n F r a arity owner i
    out.left=SemiprimeD1OrientationPalette.fields
        (SemiprimeD1SelectedCollision.selectedLabel n F r a arity owner i).1 ∧
    out.right=SemiprimeD1OrientationPalette.fields
        (SemiprimeD1SelectedCollision.selectedLabel n F r a arity owner i).2 ∧
    out.valid=true := by
  let fixed := (SemiprimeD1IncidenceSearch.run n F r a arity owner).value
  let dict := (SemiprimeSourceHistogramPrefix.acquire fixed).trie
  let port :=  (SemiprimeSourceHistogramPortKeys.record owner i).value
  have hv := SemiprimeD1IncidenceSearch.run_valid n F r a arity owner
  have hl := SemiprimeSourceHistogramDictRefinement.stored_mem r a fixed hv port.ownerKey
  have hr := SemiprimeSourceHistogramDictRefinement.stored_mem r a fixed hv port.factorKey
  have hp := read_ids r a (stored dict port.ownerKey) (stored dict port.factorKey) hl hr
  have hc := SemiprimeD1IncidenceAcquisition.record_rep owner i
  have ho := SemiprimeSourceHistogramDictRefinement.stored_decode r a fixed port.ownerKey hc.1.1
  have hf := SemiprimeSourceHistogramDictRefinement.stored_decode r a fixed port.factorKey hc.2.1
  have hvals := SemiprimeSourceHistogramPortKeys.record_values owner i
  change SemiprimeBitArithmetic.bitValue port.ownerKey=port.ownerCode ∧
    SemiprimeBitArithmetic.bitValue port.factorKey=port.factorCode at hvals
  rw [hvals.1] at ho
  rw [hvals.2] at hf
  change SemiprimeSourceWordBankSemantics.decode r a (stored dict port.ownerKey)=_ at ho
  change SemiprimeSourceWordBankSemantics.decode r a (stored dict port.factorKey)=_ at hf
  rw [ho,hf] at hp
  have hd : (acquire n F r a arity owner).selection.cache.rows.source.dictionary=
      SemiprimeSourceHistogramRows.acquire r a := rfl
  dsimp only at hp ⊢
  have h21 : (2 : SemiprimeSourceIncidenceHistogram.Feature)≠1 := by decide
  simp only [originalRead,hd,originalKey,SemiprimeSourceHistogramFeatureBits.jointBytes,
    SemiprimeSourceHistogramFeatureBits.componentKey,h21,ite_false,ite_true]
  simpa only [SemiprimeD1SelectedCollision.selectedLabel,
    SemiprimeSourceHistogramHeadOriginal.originalEnv,
    SemiprimeSourceHistogramDictRefinement.labels_original,port,dict,fixed,
    SemiprimeSourceHistogramPortKeys.record] using hp

end RiemannGaussian.SemiprimeD1PacketRowsOriginal
