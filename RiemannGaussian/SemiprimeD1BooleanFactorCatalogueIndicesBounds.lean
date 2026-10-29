/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BooleanFactorCatalogueIndices
/-! # Derived original scope and descriptor bounds for the actual Boolean sweep -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1BooleanFactorCatalogueIndicesBounds
open SemiprimeD1BooleanFactorCatalogueIndices
open SemiprimePublicAcquiredExecution (factorCount indexedArity vertexEnumeration)
open SemiprimeBitArithmetic (bitValue)
/-- Original occurrence-domain size M, distinct from E-wire or factor cardinality. -/
def occurrences (N : Nat) : Nat :=SemiprimeD1StackOwnerFibreOriginal.Owner.occurrences N
/-- The physical counter equals the next typed factor's exact original ordinal. -/
theorem cons_values (N n : Nat) (f : Fin (factorCount N)) (fs : List (Fin (factorCount N)))
    (h : (f::fs).map Fin.val=List.range' n (f::fs).length) :
    f.val=n ∧ fs.map Fin.val=List.range' (n+1) fs.length := by
  have hh:=List.range'_eq_cons_iff.mp h.symm
  refine ⟨hh.1.symm,?_⟩
  have ht:=hh.2.2
  rw [←hh.1] at ht
  simpa only [List.length_cons,Nat.add_sub_cancel] using ht
/-- Every remaining physical descriptor suffix keeps the original ordinal range. -/
theorem suffix_values (N n : Nat) :
    ((indices N).drop n).map Fin.val=List.range' n (factorCount N-n) := by
  rw [List.map_drop,indices_values,List.range_eq_range',List.drop_range']
  simp only [Nat.mul_one,Nat.zero_add]
/-- Every selected actual scope word has precisely the acquired original common width. -/
theorem scope_word_length (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) (f : Fin (factorCount (bitValue bits)))
    (s : List Bool) (hs : s∈scopeWords bits f.val) : s.length=occurrences (bitValue bits) := by
  rw [original_scopes bits hc hN f] at hs
  obtain ⟨p,_,rfl⟩:=List.mem_map.mp hs
  exact SemiprimeD1StackOwnerFibreOriginal.scopeWord_length _ p
/-- The scope converter's byte-width premise follows from the actual original source. -/
theorem scope_word_length_le (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) (f : Fin (factorCount (bitValue bits))) :
    ∀s∈scopeWords bits f.val,s.length≤occurrences (bitValue bits) :=
  fun s hs=>(scope_word_length bits hc hN f s hs).le
/-- Actual scope values are original occurrence ordinals, never E-wire indices. -/
theorem scope_word_value_lt (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) (f : Fin (factorCount (bitValue bits)))
    (s : List Bool) (hs : s∈scopeWords bits f.val) : bitValue s<occurrences (bitValue bits) := by
  rw [original_scopes bits hc hN f] at hs
  obtain ⟨p,_,rfl⟩:=List.mem_map.mp hs
  rw [SemiprimeD1StackOwnerFibreOriginal.scopeWord_value]
  have h:=((SemiprimeD1StackOwnerFibreOriginal.enumeration (bitValue bits)).equivFin.symm p).isLt
  simpa only [occurrences,SemiprimeD1StackOwnerFibreOriginal.enumeration_length] using h
/-- Numeric conversion cost uses only a proved bound on actual acquired metadata. -/
theorem scope_word_value_le (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) (f : Fin (factorCount (bitValue bits))) :
    ∀s∈scopeWords bits f.val,bitValue s≤occurrences (bitValue bits) :=
  fun s hs=>(scope_word_value_lt bits hc hN f s hs).le
/-- The selected factor's scope count is bounded by the entire original incidence domain. -/
theorem scope_count_le (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) (f : Fin (factorCount (bitValue bits))) :
    (scopeWords bits f.val).length≤occurrences (bitValue bits) := by
  rw [original_scopes bits hc hN f,List.length_map,SemiprimeD1RootTensorTables.factorNode_degree]
  exact Finset.single_le_sum (fun e (_:e∈(Finset.univ:Finset (Fin (factorCount (bitValue bits)))))=>
    Nat.zero_le (indexedArity (bitValue bits) e)) (Finset.mem_univ f)
/-- Actual record count cannot exceed physically emitted nine-field stream bytes. -/
theorem stream_count (rows : List SemiprimeD1FactorScopePairEncoding.Record) :
    rows.length≤(SemiprimeD1FactorScopePairEncoding.stream rows []).length := by
  induction rows with
  | nil=>rfl
  | cons w ws ih=>
    change ws.length+1≤(SemiprimeD1FactorScopePairEncoding.record w
      (SemiprimeD1FactorScopePairEncoding.stream ws [])).length
    rw [SemiprimeD1FactorScopePairEncoding.record_length]
    omega
/-- All actual scoped records have the derived original occurrence cardinality. -/
theorem source_count (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) :
    (SemiprimeD1StackFactorScopePairExecution.rows bits).length=occurrences (bitValue bits) := by
  rw [SemiprimeD1FactorScopeIncidencesOriginal.original_rows bits hc hN]
  simp only [SemiprimeD1FactorScopeIncidencesOriginal.indexedRows,List.length_map,
    SemiprimeD1StackOwnerFibreOriginal.enumeration_length]
  rfl
/-- M itself has an original-binary-width polynomial bound from the ACTUAL source
prefix clock and its physical byte inventory, with no cardinality advice. -/
theorem occurrences_le (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) : occurrences (bitValue bits)≤10^114*(bits.length+1)^30 := by
  have hb:bits≠[]:=by intro h;rw [h] at hN;exact Nat.lt_irrefl _ hN
  have hn:=stream_count (SemiprimeD1StackFactorScopePairExecution.rows bits)
  have hs:=SemiprimeD1StackFactorScopePairBounds.stream_length bits hb
  rw [source_count bits hc hN] at hn
  exact hn.trans hs
/-- Every original descriptor preserves its literal appended suffix. -/
theorem vertex_append {r t digits : Nat} (v : SemiprimeMacroGraph.SubdividedVertex r t digits) (tail : List Bool) :
    SemiprimeD1VertexCatalogueEncoding.vertex v tail=
      SemiprimeD1VertexCatalogueEncoding.vertex v []++tail := by
  rw [←SemiprimeD1EdgeCatalogueEncoding.record_vertex v tail,
    ←SemiprimeD1EdgeCatalogueEncoding.record_vertex v []]
  exact SemiprimeD1StackEdgeCatalogueEmit.record_append _ tail
/-- Concrete descriptor queues decompose by exactly the actually parsed head bytes. -/
theorem descriptorTape_cons_length (N : Nat) (f : Fin (factorCount N)) (fs : List (Fin (factorCount N))) :
    (descriptorTape N (f::fs)).length=(SemiprimeD1VertexCatalogueEncoding.vertex (vertex N f) []).length+
      (descriptorTape N fs).length := by
  change (SemiprimeD1VertexCatalogueEncoding.vertex (vertex N f) (descriptorTape N fs)).length=_
  rw [vertex_append,List.length_append]
/-- An individual original descriptor occupies part of its actual physical queue. -/
theorem descriptor_mem_length (N : Nat) (fs : List (Fin (factorCount N))) (f : Fin (factorCount N))
    (hf : f∈fs) :
    (SemiprimeD1VertexCatalogueEncoding.vertex (vertex N f) []).length≤(descriptorTape N fs).length := by
  induction fs with
  | nil=>simp only [List.not_mem_nil] at hf
  | cons g fs ih=>
    rw [descriptorTape_cons_length]
    obtain rfl|h:=List.mem_cons.mp hf
    · omega
    · have ht:=ih h;omega
/-- Actual53-role descriptor acquisition charges every emitted byte in its own
source trace; no mathematical descriptor length is used as a runtime supplier. -/
theorem catalogue_width (bits : List Bool) (hb : bits≠[]) :
    (VS.result bits SemiprimeD1StackBooleanFactorCatalogueView.catalogueOutput).length≤
      bits.length+10000000000000*(bits.length+1)^5 := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackVertexCatalogueBounds.source_run_polynomial bits hb
  have hi (k : SemiprimeD1StackVertexCatalogue.Stack) :
      ((SemiprimeD1StackVertexCatalogue.initial bits).data k).length≤bits.length := by
    change (SemiprimeD1StackVertexCatalogue.input bits k).length≤bits.length
    rw [SemiprimeD1StackBooleanFactorCatalogueSource.catalogue_input]
    split <;> simp
  have hd:=SemiprimeD1StackReturnLink.run_data_bound SemiprimeD1StackVertexCatalogue.program t bits.length _ _ hi hr
  have h:=hd SemiprimeD1StackBooleanFactorCatalogueView.catalogueOutput
  change (VS.result bits SemiprimeD1StackBooleanFactorCatalogueView.catalogueOutput).length≤bits.length+t at h
  omega
/-- Every individual original descriptor is bounded by the actual source's whole output. -/
theorem descriptor_length_le (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) (f : Fin (factorCount (bitValue bits))) :
    (SemiprimeD1VertexCatalogueEncoding.vertex (vertex (bitValue bits) f) []).length≤
      bits.length+10000000000000*(bits.length+1)^5 := by
  have hb:bits≠[]:=by intro h;rw [h] at hN;exact Nat.lt_irrefl _ hN
  have h:=descriptor_mem_length (bitValue bits) (indices (bitValue bits)) f (List.mem_finRange f)
  rw [←descriptor_source bits hc hN] at h
  exact h.trans (catalogue_width bits hb)
end RiemannGaussian.SemiprimeD1BooleanFactorCatalogueIndicesBounds
