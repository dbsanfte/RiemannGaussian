/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerCatalogueOriginalIds
import RiemannGaussian.SemiprimeD1StackOwnerLookupOriginal
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackOwnerCatalogueOriginalMap
open SemiprimePublicAcquiredExecution SemiprimeMacroParameters
open SemiprimeD1StackOwnerCatalogue SemiprimeD1StackOwnerCatalogueSource
open SemiprimeD1StackOwnerCatalogueParse SemiprimeD1StackOwnerCatalogueOriginalRow
open SemiprimeD1StackOwnerCatalogueLoop SemiprimeD1StackOwnerCatalogueOriginalIds
open SemiprimeD1StackOwnerCatalogueOriginalMetadata (dimensions_original originalDimension)
open SemiprimeBitArithmetic (bitValue)
namespace L
export SemiprimeD1StackOwnerLookupOriginal.Public (ownerWord catalogue occurrences_eq)
end L
/-- The actual acquired dimension words equal original N's parameters; no scalar metadata is advised. -/
theorem original_metadata (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    Metadata (SemiprimeD1StackRootScopeBankExecution.result bits)
      (firstAxis (bitLength (bitValue bits))) (secondAxis (bitLength (bitValue bits)))
      (digitCount (bitLength (bitValue bits))) := by
  refine ⟨?_,?_,?_⟩
  · change ready bits (dimension 0)=_
    simpa only [originalDimension,ite_true] using dimensions_original bits hc hN 0
  · change ready bits (dimension 1)=_
    simpa only [originalDimension,show (1:Fin 3)≠0 by decide,ite_false,ite_true] using dimensions_original bits hc hN 1
  · change ready bits (dimension 2)=_
    simpa only [originalDimension,show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide,ite_false]
      using dimensions_original bits hc hN 2
/-- Actual bank IDs are exactly the old proved lookup owner's padded M-bit words, in ORIGINAL E order. -/
theorem pairs_owner (N:Nat) (hN:0<N) :
    pairs N=(edgeEnumeration N).values.map (fun e=>(e,L.ownerWord N e)) := by
  have he:(List.ofFn (fun i:Fin (wireCount N)=>(edgeEnumeration N).equivFin i))=(edgeEnumeration N).values:=by
    change (List.ofFn (fun i:Fin (edgeEnumeration N).values.length=>(edgeEnumeration N).values[i.val]))=_
    exact List.ofFn_getElem
  rw [←he,List.map_ofFn]
  unfold pairs
  apply congrArg List.ofFn
  funext i
  simp only [L.ownerWord,L.occurrences_eq N hN,Function.comp_def]
  rw [(edgeEnumeration N).equivFin.symm_apply_apply i]
/-- Mathematical row list corresponding to physically emitted arithmetic/equality bytes. -/
def rows {r t digits:Nat} (hd:0<digits) (hc:digits≤r*t) (ps:List (Pair r t digits)) :
    List (List Bool×List Bool) := ps.flatMap (fun p=>
      [(SemiprimeD1PortOwnerKeys.key (SemiprimeD1PortOwnerKeys.endpoint hd hc p.1 false),p.2),
       (SemiprimeD1PortOwnerKeys.key (SemiprimeD1PortOwnerKeys.endpoint hd hc p.1 true),p.2)])
/-- Framing appends a literal following map suffix. -/
theorem row_append (key owner tail:List Bool) :
    SemiprimeD1StackOwnerCatalogueEmit.rowBytes key owner++tail=
      true::SemiprimeSourceHistogramKeyBits.frame key (SemiprimeSourceHistogramKeyBits.frame owner tail) := by
  simp only [SemiprimeD1StackOwnerCatalogueEmit.rowBytes,List.cons_append,
    SemiprimeD1StackOwnerEqualityKey.frame_append,List.nil_append]
/-- All actual emitted map bytes have exactly the already-verified lookup parser grammar. -/
theorem bytes_records {r t digits:Nat} (hd:0<digits) (hc:digits≤r*t) (ps:List (Pair r t digits))
    (tail:List Bool) :
    bytes ps++(false::tail)=SemiprimeD1StackOwnerLookup.records (rows hd hc ps) tail := by
  induction ps with
  | nil=>rfl
  | cons p ps ih=>
    change (SemiprimeD1StackOwnerCatalogueRow.emitted (fields p.1 p.2)
      (SemiprimeD1StackPortOwnerRecipeSpec.original p.1)
      (SemiprimeD1StackPortOwnerRecipeClassify.originalTag p.1)++bytes ps)++(false::tail)=
      SemiprimeD1StackOwnerLookup.records
        ((SemiprimeD1PortOwnerKeys.key (SemiprimeD1PortOwnerKeys.endpoint hd hc p.1 false),p.2)::
         (SemiprimeD1PortOwnerKeys.key (SemiprimeD1PortOwnerKeys.endpoint hd hc p.1 true),p.2)::rows hd hc ps) tail
    rw [original_emitted hd hc]
    simp only [List.append_assoc,SemiprimeD1StackOwnerLookup.records]
    rw [row_append,row_append,ih]

/-- Full physical map rows are exactly the ORIGINAL endpoint catalogue used by lookup completeness. -/
theorem rows_original (N:Nat) (hN:0<N) :
    rows (digitCount_bounds (bitLength_pos hN)).1
      (SemiprimeScheduledCounter.public_digit_capacity (bitLength_pos hN)) (pairs N)=L.catalogue N hN := by
  rw [pairs_owner N hN]
  unfold rows L.catalogue SemiprimeD1StackOwnerLookupOriginal.forward
  simp only [List.flatMap_map,List.product,List.map_flatMap,List.map_cons,List.map_nil]
  rfl
/-- Every byte of the newly physically acquired forward map agrees with the original lookup catalogue. -/
theorem original_bytes (N:Nat) (hN:0<N) :
    bytes (pairs N)++[false]=SemiprimeD1StackOwnerLookup.records (L.catalogue N hN) [] := by
  rw [bytes_records (digitCount_bounds (bitLength_pos hN)).1
    (SemiprimeScheduledCounter.public_digit_capacity (bitLength_pos hN)),rows_original N hN]
end RiemannGaussian.SemiprimeD1StackOwnerCatalogueOriginalMap
