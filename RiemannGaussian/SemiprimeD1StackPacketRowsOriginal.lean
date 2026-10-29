/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketRowsClock
import RiemannGaussian.SemiprimeD1StackPacketRowsMeaning
import RiemannGaussian.SemiprimeD1StackSourceSelectedKeysOriginal
/-! # Exact original packet-row acquisition from actual selected joint keys and catalogue
The only runtime inputs are the joint key and acquired alphabet catalogue.
Original width, selected ID lists and port functions are semantic proof indices.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketRowsOriginal
open SemiprimeD1StackPacketRows SemiprimeD1StackPacketRowsExecution SemiprimeD1StackPacketRowsClock
open SemiprimeD1StackPacketRowsMeaning SemiprimeD1StackPacketRowsAcquire
open SemiprimeSourceHistogramKeyBits (frame split_frame)
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace Alpha
export SemiprimeD1StackSourceAlphabet64 (aux)
export SemiprimeD1StackSourceAlphabet64Encoding (result)
end Alpha
/-- Exactly the stopped physical catalogue word of the actual frozen alphabet source. -/
def catalogue (a:Nat) :List Bool:=Alpha.result a (Alpha.aux .output)
/-- Complete original two-input read, with EXACT old fields and original well-formedness flag. -/
theorem source_run_original (a:Nat) (owner factor:List Bool)
    (ho:owner∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids)
    (hf:factor∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids) :
    ∃t ≤ polynomial (frame owner factor) (catalogue a),
      SemiprimeD1StackCalls.run program t (initial (frame owner factor) (catalogue a))=
        some (done (frame owner factor) (catalogue a) (fields 64 a owner) (fields 64 a factor)) ∧
      (done (frame owner factor) (catalogue a) (fields 64 a owner) (fields 64 a factor)).data (output false)=
        vectorBits (SemiprimeD1PacketRows.read (SemiprimeSourceHistogramRows.acquire 64 a) a (frame owner factor)).left ∧
      (done (frame owner factor) (catalogue a) (fields 64 a owner) (fields 64 a factor)).data (output true)=
        vectorBits (SemiprimeD1PacketRows.read (SemiprimeSourceHistogramRows.acquire 64 a) a (frame owner factor)).right ∧
      (SemiprimeD1PacketRows.read (SemiprimeSourceHistogramRows.acquire 64 a) a (frame owner factor)).valid=true ∧
      (done (frame owner factor) (catalogue a) (fields 64 a owner) (fields 64 a factor)).data success=[true] :=by
  have hl:=original_lookup 64 a owner ho
  have hr:=original_lookup 64 a factor hf
  obtain ⟨t,ht,h⟩:=source_run_bounded owner factor (originalEntries 64 a) (fields 64 a owner) (fields 64 a factor)
    hl.2.1 hr.2.1 hl.1 hr.1 (hl.2.2.trans hr.2.2.symm)
  rw [catalogue_original] at ht h
  refine ⟨t,ht,h,?_,?_,?_,rfl⟩
  · change vectorBits (fields 64 a owner)=_
    rw [(SemiprimeD1PacketRows.read_frame _ a owner factor).1,fields_original 64 a owner ho]
  · change vectorBits (fields 64 a factor)=_
    rw [(SemiprimeD1PacketRows.read_frame _ a owner factor).2,fields_original 64 a factor hf]
  · have ho':=(SemiprimeD1PacketRows.original_fields 64 a owner ho).2
    have hf':=(SemiprimeD1PacketRows.original_fields 64 a factor hf).2
    simp only [SemiprimeD1PacketRows.read,split_frame,ho',hf',Bool.true_and]
/-- Both inputs are retained exactly; the success and two row vectors are the sole new output words. -/
theorem inputs_retained (key cat:List Bool) (left right:List (List Bool)) :
    (done key cat left right).data (aux .key)=key ∧ (done key cat left right).data (aux .catalogue)=cat :=⟨rfl,rfl⟩
/-- Native selected-key lineage yields two actual acquired menu IDs, never a supplied row answer. -/
theorem selected_key_lineage (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (p:(e:Fin F)×Fin (arity e)) :
    ∃leftID rightID,leftID∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids ∧
      rightID∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids ∧
      SemiprimeD1IncidenceAcquisition.originalKey n F 64 a arity owner p=frame leftID rightID :=by
  let ids:=(SemiprimeD1IncidenceSearch.run n F 64 a arity owner).value
  let trie:=(SemiprimeSourceHistogramPrefix.acquire ids).trie
  let port:=(SemiprimeSourceHistogramPortKeys.record owner p).value
  have hv:=SemiprimeD1IncidenceSearch.run_valid n F 64 a arity owner
  have hl:=SemiprimeSourceHistogramDictRefinement.stored_mem 64 a ids hv port.ownerKey
  have hr:=SemiprimeSourceHistogramDictRefinement.stored_mem 64 a ids hv port.factorKey
  refine ⟨SemiprimeSourceHistogramTrie.stored trie port.ownerKey,
    SemiprimeSourceHistogramTrie.stored trie port.factorKey,hl,hr,?_⟩
  have h21:(2:SemiprimeSourceIncidenceHistogram.Feature)≠1:=by decide
  simp only [SemiprimeD1IncidenceAcquisition.originalKey,SemiprimeSourceHistogramFeatureBits.jointBytes,
    SemiprimeSourceHistogramFeatureBits.componentKey,h21,ite_false,ite_true]
  rfl
/-- Every actual original selected key has a complete actual packet-row source trace with its own physical-input polynomial clock. -/
theorem source_run_selected (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (p:(e:Fin F)×Fin (arity e)) :
    ∃leftID rightID,∃t ≤ polynomial (SemiprimeD1IncidenceAcquisition.originalKey n F 64 a arity owner p) (catalogue a),
      SemiprimeD1StackCalls.run program t
        (initial (SemiprimeD1IncidenceAcquisition.originalKey n F 64 a arity owner p) (catalogue a))=
        some (done (SemiprimeD1IncidenceAcquisition.originalKey n F 64 a arity owner p) (catalogue a)
          (fields 64 a leftID) (fields 64 a rightID)) ∧
      (done (SemiprimeD1IncidenceAcquisition.originalKey n F 64 a arity owner p) (catalogue a)
        (fields 64 a leftID) (fields 64 a rightID)).data (output false)=
          vectorBits (SemiprimeD1PacketRows.read (SemiprimeSourceHistogramRows.acquire 64 a) a
            (SemiprimeD1IncidenceAcquisition.originalKey n F 64 a arity owner p)).left ∧
      (done (SemiprimeD1IncidenceAcquisition.originalKey n F 64 a arity owner p) (catalogue a)
        (fields 64 a leftID) (fields 64 a rightID)).data (output true)=
          vectorBits (SemiprimeD1PacketRows.read (SemiprimeSourceHistogramRows.acquire 64 a) a
            (SemiprimeD1IncidenceAcquisition.originalKey n F 64 a arity owner p)).right ∧
      (SemiprimeD1PacketRows.read (SemiprimeSourceHistogramRows.acquire 64 a) a
        (SemiprimeD1IncidenceAcquisition.originalKey n F 64 a arity owner p)).valid=true :=by
  obtain ⟨l,r,hl,hr,hkey⟩:=selected_key_lineage n F a arity owner p
  obtain ⟨t,ht,h,hol,hor,hv,_⟩:=source_run_original a l r hl hr
  rw [hkey]
  exact ⟨l,r,t,ht,h,hol,hor,hv⟩
end RiemannGaussian.SemiprimeD1StackPacketRowsOriginal
