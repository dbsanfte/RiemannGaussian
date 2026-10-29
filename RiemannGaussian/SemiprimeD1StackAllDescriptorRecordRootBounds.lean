/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackAllDescriptorRecordUniformBounds
import RiemannGaussian.SemiprimeD1BooleanFactorCatalogueIndicesOriginal
import RiemannGaussian.SemiprimeD1StackRootScheduleOriginal

/-! # Uniform original-family actual descriptor acquisition envelope
The acquired original descriptor and scope bytes are estimated from the
existing actual N-only sources. This pointwise body bound feeds the whole
factor-catalogue loop; it does not replace that loop's acquisition clock.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackAllDescriptorRecordRootBounds
open SemiprimeBitArithmetic (bitValue)
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace U
export SemiprimeD1StackAllDescriptorRecordUniformBounds (inventory envelope raw_length_le component_bound)
end U
namespace O
export SemiprimeD1StackAllDescriptorRecordOriginal (rawFields originalCode raw_canonical raw_binaryN raw_transform_bound)
end O
namespace IX
export SemiprimeD1BooleanFactorCatalogueIndices (scopeWords vertex)
export SemiprimeD1BooleanFactorCatalogueIndicesBounds
  (occurrences scope_word_length_le scope_word_value_le scope_count_le descriptor_length_le)
export SemiprimeD1BooleanFactorCatalogueIndicesOriginal (scope_count_eq)
end IX
/-- Fixed original input-polynomial capacity before every original descriptor. -/
def baseCapacity (bits:List Bool) : Nat :=10^20*(bits.length+1)^6
/-- Caller history and final-output bytes remain explicitly charged. -/
def capacity (bits hist out:List Bool) : Nat :=baseCapacity bits+hist.length+out.length
/-- Original complete factor-table arity cap, with its actual three-quarter-power size. -/
def arityCapacity (bits:List Bool) : Nat :=SemiprimeMacroParameters.scopeBound bits.length
/-- Every one of five framed descriptor fields is part of its actual record bytes. -/
theorem field_in_record (w:SemiprimeD1EdgeCatalogueEncoding.Record) (i:Fin 5) :
    (w i).length ≤ (SemiprimeD1EdgeCatalogueEncoding.record w []).length := by
  fin_cases i
  · change (w 0).length ≤ _
    simp only [SemiprimeD1EdgeCatalogueEncoding.record,SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
    omega
  · change (w 1).length ≤ _
    simp only [SemiprimeD1EdgeCatalogueEncoding.record,SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
    omega
  · change (w 2).length ≤ _
    simp only [SemiprimeD1EdgeCatalogueEncoding.record,SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
    omega
  · change (w 3).length ≤ _
    simp only [SemiprimeD1EdgeCatalogueEncoding.record,SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
    omega
  · change (w 4).length ≤ _
    simp only [SemiprimeD1EdgeCatalogueEncoding.record,SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
    omega
/-- Binary N plus the real serialized descriptor bounds every cached raw field. -/
theorem raw_field_bytes {r t digits:Nat} (bits:List Bool) (v:SemiprimeMacroGraph.SubdividedVertex r t digits)
    (i:Fin 6) : (O.rawFields bits v i).length ≤
      bits.length+(SemiprimeD1VertexCatalogueEncoding.vertex v []).length := by
  rw [←SemiprimeD1EdgeCatalogueEncoding.record_vertex]
  fin_cases i
  · exact Nat.le_add_right _ _
  · exact (field_in_record _ 0).trans (Nat.le_add_left _ _)
  · exact (field_in_record _ 1).trans (Nat.le_add_left _ _)
  · exact (field_in_record _ 2).trans (Nat.le_add_left _ _)
  · exact (field_in_record _ 3).trans (Nat.le_add_left _ _)
  · exact (field_in_record _ 4).trans (Nat.le_add_left _ _)
/-- Physical scope framing is bounded without parsing any numerical identifier. -/
theorem vector_length (words:List (List Bool)) (M:Nat) (h:∀w∈words,w.length ≤ M) :
    (vectorBits words).length ≤ 2*words.length*M+2*words.length+1 := by
  have hs:(words.map List.length).sum ≤ words.length*M := by
    induction words with
    | nil=>simp
    | cons w ws ih=>
      have hw:=h w (by simp)
      have ht:=ih (fun x hx=>h x (by simp [hx]))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith
  rw [SemiprimeD1TensorTapeCodec.vectorBits_length]
  simp only [Nat.mul_assoc]
  omega
/-- The actual acquired occurrence-domain size has the original linear bound. -/
theorem occurrences_linear (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    IX.occurrences (bitValue bits) ≤ 12800*bits.length := by
  have h:=SemiprimeD1RootTensorTables.actual_incidence_bound (bitValue bits) hN
  have hw:=SemiprimeD1StackRootScheduleOriginal.width_original bits hc
  simp only [IX.occurrences,SemiprimeD1StackOwnerLookupOriginal.Public.occurrences]
  simpa only [←hw] using h
/-- Abstract arithmetic isolates polynomial scope bytes from native original enumeration. -/
theorem scope_arithmetic (M L:Nat) (hM:M ≤ 12800*L) :
    2*M^2+2*M+1 ≤ 10^10*(L+1)^2 := by
  have h:=Nat.pow_le_pow_left hM 2
  nlinarith
/-- The actual complete binary scope vector has a fixed quadratic input-width bound. -/
theorem scope_bytes (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (f:Fin (SemiprimePublicAcquiredExecution.factorCount (bitValue bits))) :
    (vectorBits (IX.scopeWords bits f.val)).length ≤ 10^10*(bits.length+1)^2 := by
  have h0:=vector_length (IX.scopeWords bits f.val) (IX.occurrences (bitValue bits))
    (IX.scope_word_length_le bits hc hN f)
  simp only [Nat.mul_assoc] at h0
  have h1:=IX.scope_count_le bits hc hN f
  have hm:=Nat.mul_le_mul_right (IX.occurrences (bitValue bits)) h1
  have h2:(vectorBits (IX.scopeWords bits f.val)).length ≤
      2*(IX.occurrences (bitValue bits))^2+2*IX.occurrences (bitValue bits)+1 := by
    rw [pow_two]
    omega
  exact h2.trans (scope_arithmetic _ _ (occurrences_linear bits hc hN))
/-- The actual selected scope count is the original factor arity, within its genuine cap. -/
theorem scope_arity (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (f:Fin (SemiprimePublicAcquiredExecution.factorCount (bitValue bits))) :
    (IX.scopeWords bits f.val).length ≤ arityCapacity bits := by
  rw [IX.scope_count_eq bits hc hN f]
  have h:=SemiprimePublicAcquiredExecution.indexedArity_le (bitValue bits) f
  have hw:=SemiprimeD1StackRootScheduleOriginal.width_original bits hc
  simpa only [arityCapacity,←hw] using h
/-- The physically acquired product arity is also below the common original scope cap. -/
theorem product_arity (bits:List Bool) :
    SemiprimeD1StackProductTableSpec.arity bits ≤ arityCapacity bits := by
  unfold SemiprimeD1StackProductTableSpec.arity
  rw [SemiprimeD1StackPublicProductBounds.cached_length]
  unfold arityCapacity SemiprimeMacroParameters.scopeBound
  exact Nat.mul_le_mul_right _ (by omega)
/-- The real boundary writer's acquired depth fits the very same original cap. -/
theorem boundary_arity (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    (SemiprimeD1StackZeroBoundaryTable.cached bits).length ≤ arityCapacity bits := by
  rw [SemiprimeD1StackZeroBoundaryTableBounds.original_depth bits hc,SemiprimeMacroParameters.axes_product]
  have hw:=SemiprimeD1StackRootScheduleOriginal.width_original bits hc
  rw [←hw]
  unfold arityCapacity SemiprimeMacroParameters.scopeBound
  exact Nat.le_mul_of_pos_left _ (by omega)
/-- Every original acquired descriptor field has a fixed input-polynomial byte cap. -/
theorem raw_capacity (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (f:Fin (SemiprimePublicAcquiredExecution.factorCount (bitValue bits))) (i:Fin 6) :
    (O.rawFields bits (IX.vertex (bitValue bits) f) i).length ≤ 10^15*(bits.length+1)^6 := by
  have h0:=raw_field_bytes bits (IX.vertex (bitValue bits) f) i
  have h1:=IX.descriptor_length_le bits hc hN f
  have h5:(bits.length+1)^5 ≤ (bits.length+1)^6:=Nat.pow_le_pow_right (by omega) (by decide)
  have hL:bits.length+1 ≤ (bits.length+1)^6:=by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega:1 ≤ bits.length+1) (by decide:1 ≤ 6)
  omega
/-- The same actual complete dispatcher clock has one bound for ALL original eighteen-tag rows. -/
theorem runBound_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (f:Fin (SemiprimePublicAcquiredExecution.factorCount (bitValue bits))) (hist out:List Bool) :
    SemiprimeD1StackAllDescriptorRecordClock.runBound
      (O.originalCode (IX.vertex (bitValue bits) f)) (O.rawFields bits (IX.vertex (bitValue bits) f))
      (IX.scopeWords bits f.val) (IX.occurrences (bitValue bits)) hist out ≤
        10^130*((capacity bits hist out+1)^18*2^(arityCapacity bits)) := by
  have hL:bits.length+1 ≤ (bits.length+1)^6:=by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega:1 ≤ bits.length+1) (by decide:1 ≤ 6)
  have h2:(bits.length+1)^2 ≤ (bits.length+1)^6:=Nat.pow_le_pow_right (by omega) (by decide)
  have hraw:∀i,(O.rawFields bits (IX.vertex (bitValue bits) f) i).length ≤ capacity bits hist out:=by
    intro i
    have h:=raw_capacity bits hc hN f i
    unfold capacity baseCapacity
    omega
  have hb:(vectorBits (IX.scopeWords bits f.val)).length ≤ capacity bits hist out:=by
    have h:=scope_bytes bits hc hN f
    unfold capacity baseCapacity
    omega
  have hh:hist.length ≤ capacity bits hist out:=by unfold capacity;omega
  have ho:out.length ≤ capacity bits hist out:=by unfold capacity;omega
  have hm:IX.occurrences (bitValue bits) ≤ capacity bits hist out:=by
    have h:=occurrences_linear bits hc hN
    unfold capacity baseCapacity
    omega
  exact SemiprimeD1StackAllDescriptorRecordUniformBounds.run_bound _ _ _ _ hist out _ _
    hraw hb hh ho hm (scope_arity bits hc hN f) (product_arity bits) (boundary_arity bits hc)
/-- The original body's own actual trace clock has the same uniform family bound. -/
theorem timeBound_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (f:Fin (SemiprimePublicAcquiredExecution.factorCount (bitValue bits))) (hist out:List Bool) :
    SemiprimeD1StackAllDescriptorRecordSpec.timeBound
      (O.originalCode (IX.vertex (bitValue bits) f)) (O.rawFields bits (IX.vertex (bitValue bits) f))
      (IX.scopeWords bits f.val) hist out ≤
        10^130*((capacity bits hist out+1)^18*2^(arityCapacity bits)) :=
  (SemiprimeD1StackAllDescriptorRecordClock.timeBound_le _ _ _ _ hist out
    (IX.scope_word_length_le bits hc hN f) (IX.scope_word_value_le bits hc hN f)).trans
      (runBound_original bits hc hN f hist out)
/-- Same actual fixed source execution for every original descriptor, with all
retained caller bytes and every real decoder/loader/checker/cleanup step charged. -/
theorem source_run_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (f:Fin (SemiprimePublicAcquiredExecution.factorCount (bitValue bits))) (hist out:List Bool) :
    ∃t ≤ 10^130*((capacity bits hist out+1)^18*2^(arityCapacity bits)),
      SemiprimeD1StackCalls.run SemiprimeD1StackAllDescriptorRecord.program t
        (SemiprimeD1StackAllDescriptorRecord.initial (O.rawFields bits (IX.vertex (bitValue bits) f))
          (vectorBits (IX.scopeWords bits f.val)) hist out)=some
            (SemiprimeD1StackAllDescriptorRecordSpec.done (O.originalCode (IX.vertex (bitValue bits) f))
              (O.rawFields bits (IX.vertex (bitValue bits) f)) (IX.scopeWords bits f.val) hist out) := by
  obtain ⟨htag,h2,h3,h4⟩:=O.raw_canonical bits (IX.vertex (bitValue bits) f)
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackAllDescriptorRecordClock.source_run_bounded _ _ htag h2 h3 h4
    (O.raw_transform_bound bits (IX.vertex (bitValue bits) f)) hc hN (IX.scopeWords bits f.val) hist out
    (IX.occurrences (bitValue bits)) (IX.scope_word_length_le bits hc hN f) (IX.scope_word_value_le bits hc hN f)
  exact ⟨t,ht.trans (runBound_original bits hc hN f hist out),hr⟩
/-- The genuine original scope exponent has the established three-quarter-power estimate. -/
theorem arityCapacity_fourth (bits:List Bool) (h:0<bits.length) :
    (arityCapacity bits)^4 ≤ 512^4*bits.length^3 :=
  SemiprimeMacroParameters.scopeBound_fourth_le h
/-- With clear caller accumulators, the SAME actual row clock has a fixed
original-width polynomial times the original arity exponential. -/
theorem timeBound_zero_history (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (f:Fin (SemiprimePublicAcquiredExecution.factorCount (bitValue bits))) :
    SemiprimeD1StackAllDescriptorRecordSpec.timeBound
      (O.originalCode (IX.vertex (bitValue bits) f)) (O.rawFields bits (IX.vertex (bitValue bits) f))
      (IX.scopeWords bits f.val) [] [] ≤
        (10^130*(10^21)^18)*(bits.length+1)^108*2^(arityCapacity bits) := by
  have h:=timeBound_original bits hc hN f [] []
  have hpos:1 ≤ (bits.length+1)^6:=Nat.pow_pos (by omega)
  have hi:capacity bits [] []+1 ≤ 10^21*(bits.length+1)^6:=by
    unfold capacity baseCapacity
    simp only [List.length_nil,Nat.add_zero]
    omega
  have hp:=Nat.pow_le_pow_left hi 18
  have hL:((bits.length+1)^6)^18=(bits.length+1)^108:=
    (pow_mul (bits.length+1) 6 18).symm
  rw [mul_pow,hL] at hp
  have hm:=Nat.mul_le_mul_left (10^130) (Nat.mul_le_mul_right (2^(arityCapacity bits)) hp)
  exact h.trans (by simpa only [Nat.mul_assoc] using hm)
end RiemannGaussian.SemiprimeD1StackAllDescriptorRecordRootBounds
