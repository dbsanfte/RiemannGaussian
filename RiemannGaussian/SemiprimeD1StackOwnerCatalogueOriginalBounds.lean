/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerCatalogueNumeric
import RiemannGaussian.SemiprimeD1StackOwnerCatalogueOriginalMap
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackOwnerCatalogueOriginalBounds
open SemiprimeD1StackOwnerCatalogue SemiprimeD1StackOwnerCatalogueSource
open SemiprimeD1StackOwnerCatalogueOriginalRow SemiprimeD1StackOwnerCatalogueOriginalMap
open SemiprimeD1StackOwnerCatalogueOriginalIds SemiprimeD1StackOwnerCatalogueNumeric
open SemiprimePublicAcquiredExecution SemiprimeMacroParameters
open SemiprimeBitArithmetic (bitValue)
namespace Old
export SemiprimeD1StackRootScopeBankBounds (tapeCap polynomial)
end Old
/-- One fixed polynomial bound for all physically acquired dimensions, edge fields and owner IDs. -/
def operandCap (n:Nat) : Nat :=10*(n+Old.polynomial n)+30*Old.tapeCap n+100
/-- Each initial old source role contains at most the actual binary N input. -/
theorem source_input_length (bits:List Bool) (k:S.Stack) : (S.input bits k).length≤bits.length := by
  rcases k with k|k
  · rcases k with k|k
    · change (SemiprimeD1StackVertexCatalogue.input bits k).length≤bits.length
      rw [SemiprimeD1StackEdgeCatalogueExecution.cat_input]
      split <;> simp
    · exact Nat.zero_le _
  · rcases k with k|k <;> exact Nat.zero_le _
/-- Actual retained metadata word lengths are derived from the SAME original source trace. -/
theorem source_role_length (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (k:S.Stack) : (SemiprimeD1StackRootScopeBankExecution.result bits k).length≤bits.length+Old.polynomial bits.length := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackRootScopeBankBounds.source_run_polynomial bits hc hN
  have h:=SemiprimeD1StackReturnLink.run_data_bound S.program t bits.length _ _
    (source_input_length bits) hr k
  change (SemiprimeD1StackRootScopeBankExecution.result bits k).length≤bits.length+t at h
  exact h.trans (Nat.add_le_add_left ht _)
/-- An actual original framed field is no longer than the actual record containing it. -/
theorem field_record_length (p:SemiprimeD1StackEdgeCount.Record) (i:Fin 6) (tail:List Bool) :
    (p i).length≤(SemiprimeD1StackEdgeCount.record p tail).length := by
  fin_cases i
  · change (p (0:Fin 6)).length≤_
    simp only [SemiprimeD1StackEdgeCount.record,SemiprimeSourceHistogramKeyBits.frame_length]
    omega
  · change (p (1:Fin 6)).length≤_
    simp only [SemiprimeD1StackEdgeCount.record,SemiprimeSourceHistogramKeyBits.frame_length]
    omega
  · change (p (2:Fin 6)).length≤_
    simp only [SemiprimeD1StackEdgeCount.record,SemiprimeSourceHistogramKeyBits.frame_length]
    omega
  · change (p (3:Fin 6)).length≤_
    simp only [SemiprimeD1StackEdgeCount.record,SemiprimeSourceHistogramKeyBits.frame_length]
    omega
  · change (p (4:Fin 6)).length≤_
    simp only [SemiprimeD1StackEdgeCount.record,SemiprimeSourceHistogramKeyBits.frame_length]
    omega
  · change (p (5:Fin 6)).length≤_
    simp only [SemiprimeD1StackEdgeCount.record,SemiprimeSourceHistogramKeyBits.frame_length]
    omega
/-- Following edge bytes remain part of the actual record tape; no symbolic-reference sharing is free. -/
theorem tail_record_length (p:SemiprimeD1StackEdgeCount.Record) (tail:List Bool) :
    tail.length≤(SemiprimeD1StackEdgeCount.record p tail).length := by
  simp only [SemiprimeD1StackEdgeCount.record,SemiprimeSourceHistogramKeyBits.frame_length]
  omega
/-- Membership in the actual source's edge tape bounds every actually parsed unary coordinate. -/
theorem field_tape_length (ps:List SemiprimeD1StackEdgeCount.Record) (p:SemiprimeD1StackEdgeCount.Record)
    (hp:p∈ps) (i:Fin 6) : (p i).length≤(SemiprimeD1StackEdgeCount.tape ps []).length := by
  induction ps with
  | nil=>cases hp
  | cons q ps ih=>
    rcases List.mem_cons.mp hp with h|h
    · subst p;exact field_record_length q i _
    · exact (ih h).trans (tail_record_length q _)
/-- Actual source metadata, with every dimension role bounded from the actual prefix clock. -/
theorem metadata_lengths (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    firstAxis (bitLength (bitValue bits))≤bits.length+Old.polynomial bits.length ∧
    secondAxis (bitLength (bitValue bits))≤bits.length+Old.polynomial bits.length ∧
    digitCount (bitLength (bitValue bits))≤bits.length+Old.polynomial bits.length := by
  have hm:=original_metadata bits hc hN
  have hd (i:Fin 3):(metaStore (SemiprimeD1StackRootScopeBankExecution.result bits) (dimension i)).length≤
      bits.length+Old.polynomial bits.length:=by
    simp only [metaStore,dimension,SemiprimeD1StackOwnerCatalogueSource.data,source]
    exact source_role_length bits hc hN _
  refine ⟨?_,?_,?_⟩
  · simpa only [hm.1,SemiprimeD1StackUnaryDivmod.unary,List.length_replicate] using hd 0
  · simpa only [hm.2.1,SemiprimeD1StackUnaryDivmod.unary,List.length_replicate] using hd 1
  · simpa only [hm.2.2,SemiprimeD1StackUnaryDivmod.unary,List.length_replicate] using hd 2
/-- Every original edge field length follows from membership in the actual acquired E tape. -/
theorem original_field_length (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (e:PublicEdge (bitValue bits)) (i:Fin 6) :
    (SemiprimeD1StackEdgeCount.edgeFields e i).length≤Old.tapeCap bits.length := by
  have hm:SemiprimeD1StackEdgeCount.edgeFields e∈SemiprimeD1StackRootScopeBankExecution.records bits:=
    List.mem_map.mpr ⟨e,(edgeEnumeration (bitValue bits)).complete e,rfl⟩
  exact (field_tape_length _ _ hm i).trans (SemiprimeD1StackRootScopeBankBounds.tape_bytes bits hc hN)
/-- The actual original E count is bounded by the bytes that its actual scanner consumed. -/
theorem wire_count_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    wireCount (bitValue bits)≤Old.tapeCap bits.length := by
  have h:=SemiprimeD1StackRootScopeBankBounds.count_le bits hc hN
  rw [SemiprimeD1StackOwnerCatalogueOriginalMetadata.occurrences_original bits] at h
  omega
/-- Every actual original arithmetic operand is polynomial in binary input width. -/
theorem original_volume (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (e:PublicEdge (bitValue bits)) :
    SemiprimeD1StackPortOwnerRecipeNumeric.volume (SemiprimeD1StackPortOwnerRecipeSpec.original e)≤operandCap bits.length := by
  have hm:=metadata_lengths bits hc hN
  have h0:=original_field_length bits hc hN e 1
  have h1:=original_field_length bits hc hN e 2
  have h2:=original_field_length bits hc hN e 3
  have h3:=original_field_length bits hc hN e 4
  have h4:=original_field_length bits hc hN e 5
  change (SemiprimeD1EdgeCatalogueEncoding.bit e.1 0).length≤_ at h0
  change (SemiprimeD1EdgeCatalogueEncoding.bit e.1 1).length≤_ at h1
  change (SemiprimeD1EdgeCatalogueEncoding.bit e.1 2).length≤_ at h2
  change (SemiprimeD1EdgeCatalogueEncoding.bit e.1 3).length≤_ at h3
  change (SemiprimeD1EdgeCatalogueEncoding.bit e.1 4).length≤_ at h4
  dsimp only [SemiprimeD1StackPortOwnerRecipeNumeric.volume,SemiprimeD1StackPortOwnerRecipeSpec.original]
  unfold operandCap
  omega
/-- The SAME physically selected owner bank word has width M=2E, distinct from its numeric E index. -/
theorem original_owner_length (bits:List Bool) (p:PublicEdge (bitValue bits)×List Bool)
    (hp:p∈pairs (bitValue bits)) : p.2.length=2*wireCount (bitValue bits) := by
  obtain ⟨i,hi⟩:=List.mem_ofFn.mp hp
  have he:p=( (edgeEnumeration (bitValue bits)).equivFin i,
      SemiprimeD1OrdinalBankSpec.idAt (2*wireCount (bitValue bits)) i.val):=hi.symm
  rw [he]
  apply SemiprimeD1OrdinalBankSpec.id_length
  have h:=i.isLt
  omega
/-- All seven ACTUALLY parsed original row payloads have the same derived polynomial cap. -/
theorem original_payloads (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (p:PublicEdge (bitValue bits)×List Bool) (hp:p∈pairs (bitValue bits)) :
    ∀i,(fields p.1 p.2 i).length≤operandCap bits.length := by
  intro i
  have hw:=wire_count_le bits hc hN
  have hid:=original_owner_length bits p hp
  fin_cases i
  · change (SemiprimeD1StackEdgeCount.edgeFields p.1 (0:Fin 6)).length≤_
    have h:=original_field_length bits hc hN p.1 0
    unfold operandCap;omega
  · change (SemiprimeD1StackEdgeCount.edgeFields p.1 (1:Fin 6)).length≤_
    have h:=original_field_length bits hc hN p.1 1
    unfold operandCap;omega
  · change (SemiprimeD1StackEdgeCount.edgeFields p.1 (2:Fin 6)).length≤_
    have h:=original_field_length bits hc hN p.1 2
    unfold operandCap;omega
  · change (SemiprimeD1StackEdgeCount.edgeFields p.1 (3:Fin 6)).length≤_
    have h:=original_field_length bits hc hN p.1 3
    unfold operandCap;omega
  · change (SemiprimeD1StackEdgeCount.edgeFields p.1 (4:Fin 6)).length≤_
    have h:=original_field_length bits hc hN p.1 4
    unfold operandCap;omega
  · change (SemiprimeD1StackEdgeCount.edgeFields p.1 (5:Fin 6)).length≤_
    have h:=original_field_length bits hc hN p.1 5
    unfold operandCap;omega
  · change p.2.length≤_
    unfold operandCap;omega
end RiemannGaussian.SemiprimeD1StackOwnerCatalogueOriginalBounds
