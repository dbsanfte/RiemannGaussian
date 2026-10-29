/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerCatalogueLoop
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackOwnerCatalogueOriginalIds
open SemiprimePublicAcquiredExecution
open SemiprimeD1StackOwnerCatalogueLoop
open SemiprimeD1OrdinalBankSpec (words idAt)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeSourceHistogramKeyBits (frame)
/-- Original E edges paired with the FIRST E words from the actual acquired 2E bank.
This list is a proof description of physical parser results, never a machine input. -/
def pairs (N:Nat) : List (PublicEdge N×List Bool) :=
  List.ofFn (fun i:Fin (wireCount N)=>((edgeEnumeration N).equivFin i,idAt (2*wireCount N) i.val))
/-- Actual unused M-E bank suffix after precisely E wire-owner words have been read. -/
def unused (N:Nat) : List Bool := vectorBits ((words (2*wireCount N)).drop (wireCount N))
/-- The actual edge projection is exactly the ORIGINAL constructor enumeration in order. -/
theorem pairs_edges (N:Nat) : (pairs N).map Prod.fst=(edgeEnumeration N).values := by
  simp only [pairs,List.map_ofFn]
  change (List.ofFn (fun i:Fin (edgeEnumeration N).values.length=>(edgeEnumeration N).values[i.val]))=_
  exact List.ofFn_getElem
/-- Exactly E bank words are read, with their original 2E-bit padding retained. -/
theorem pairs_ids (N:Nat) : (pairs N).map Prod.snd=(words (2*wireCount N)).take (wireCount N) := by
  apply List.ext_getElem
  · simp only [pairs,List.length_map,List.length_ofFn,List.length_take,SemiprimeD1OrdinalBankSpec.length]
    omega
  · intro i hi hj
    have hiE:i<wireCount N:=by simpa only [pairs,List.length_map,List.length_ofFn] using hi
    have hiM:i<(words (2*wireCount N)).length:=by rw [SemiprimeD1OrdinalBankSpec.length];omega
    simp only [pairs,List.getElem_map,List.getElem_ofFn,List.getElem_take]
    unfold idAt
    rw [List.getElem?_eq_getElem hiM,Option.getD_some]
/-- Actual six-field tape reconstruction agrees with the original edge projection. -/
theorem edges_map {r t digits:Nat} (ps:List (Pair r t digits)) :
    edgeTapeOf ps=(ps.map Prod.fst).foldr SemiprimeD1EdgeCatalogueEncoding.edge [] := by
  simp only [edgeTapeOf,List.foldr_map]
/-- Actual ID-prefix framing agrees with the retained acquired bank suffix. -/
theorem ids_map {r t digits:Nat} (ps:List (Pair r t digits)) (tail:List Bool) :
    idTapeOf ps tail=(ps.map Prod.snd).foldr (fun w rest=>true::frame w rest) tail := by
  simp only [idTapeOf,List.foldr_map]
/-- The ID parser's untouched suffix is physically present in the same acquired bank. -/
theorem vector_append (xs ys:List (List Bool)) :
    xs.foldr (fun w rest=>true::frame w rest) (vectorBits ys)=vectorBits (xs++ys) := by
  induction xs with
  | nil=>rfl
  | cons w xs ih=>simp only [List.foldr_cons,List.cons_append,vectorBits,ih]
/-- Complete parser-entry edge reader, without a supplied order premise. -/
theorem original_edges (N:Nat) :
    edgeTapeOf (pairs N)=(edgeEnumeration N).values.foldr SemiprimeD1EdgeCatalogueEncoding.edge [] := by
  rw [edges_map,pairs_edges]
/-- Complete parser-entry ID reader is the ACTUAL entire M bank, even though only E words are read. -/
theorem original_ids (N:Nat) : idTapeOf (pairs N) (unused N)=vectorBits (words (2*wireCount N)) := by
  rw [ids_map,pairs_ids]
  unfold unused
  rw [vector_append,List.take_append_drop]
end RiemannGaussian.SemiprimeD1StackOwnerCatalogueOriginalIds
