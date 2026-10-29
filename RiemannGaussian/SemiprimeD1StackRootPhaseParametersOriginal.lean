/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseParametersBounds
/-! # Exact original chronological full phase banks and stable allocation ordinals
The cache contains every stopped actual48-role source bank, accepted or rejected.
Phase bodies, recursive child networks, coefficient recovery and the complete
counter remain separate obligations; none is replaced by a native body evaluator.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseParametersOriginal
open SemiprimeD1StackRootPhaseParameters SemiprimeD1StackRootPhaseParametersEncoding
open SemiprimeD1StackRootPhaseParametersRows SemiprimeD1StackRootPhaseParametersExecution
open SemiprimeD1StackRootPhaseParametersCaps SemiprimeD1StackRootPhaseParametersBounds
open SemiprimeBitArithmetic (bitValue)
open SemiprimeSourceHistogramKeyBits (frame split)
namespace PO
export SemiprimeD1StackPhaseWorkingPrecisionOriginal
  (originalOrder precision_original power_original height_retained blocks_retained rejected_outputs)
end PO
/-- Proof-side decoding of a finite number of physically framed retained words.
The executing cache program uses the real Frame/Field procedures, not this function. -/
def readWords : Nat→List Bool→List (List Bool)
  | 0,_=>[]
  | n+1,bytes=>(split bytes).first::readWords n (split bytes).rest
/-- All declared physical-role words survive exact framing, including empty fields. -/
theorem read_frames (keys:List P.Stack) (bank:P.Stack→List Bool) (tail:List Bool) :
    readWords keys.length (keys.foldr (fun k rest=>frame (bank k) rest) tail)=keys.map bank :=by
  induction keys generalizing tail with
  | nil=>rfl
  | cons k ks ih=>
    simp only [List.length_cons,List.foldr_cons,readWords,List.map_cons,
      (SemiprimeSourceHistogramKeyBits.split_frame (bank k) _).1,
      (SemiprimeSourceHistogramKeyBits.split_frame (bank k) _).2.1,ih]
/-- Each actual complete cache record contains EXACTLY all48 actual stopped words. -/
theorem record_words (a u edges:Nat) (t:List Bool) :
    readWords 48 (record a u edges t)=I.roles.map (stopped a u edges t) :=by
  have h:=read_frames I.roles (stopped a u edges t) []
  rw [SemiprimeD1StackRootPhaseParametersInventory.roles_length] at h
  exact h
/-- One fixed cache ABI position; exact words, with no binary/unary reinterpretation. -/
def wordAt (bytes:List Bool) (i:Fin 48) : List Bool :=((readWords 48 bytes)[i.val]?).getD []
/-- Every fixed ABI position is its exact stopped physical field, including all37 old cache words. -/
theorem record_word (a u edges:Nat) (t:List Bool) (i:Fin 48) :
    wordAt (record a u edges t) i=stopped a u edges t (I.role i) :=by
  unfold wordAt
  rw [record_words,List.getElem?_map,List.getElem?_eq_getElem
    (show i.val<I.roles.length by rw [SemiprimeD1StackRootPhaseParametersInventory.roles_length];exact i.isLt)]
  rfl
/-- Every original126-role acquired source/grid cell is retained literally. -/
theorem grid_preserved (bits:List Bool) (k:G.Stack) :
    result bits (gridStack k)=SemiprimeD1StackRootPhaseGridEncoding.result bits k :=rfl
/-- Original binary N is retained byte for byte after every phase has been cached. -/
theorem input_preserved (bits:List Bool) : result bits originalInput=bits :=
  SemiprimeD1StackRootPhaseGridEncoding.input_preserved bits
/-- Abstract acquired-cache heap projection prevents proof reduction of original-N lists. -/
theorem finished_heap (root:G.Stack→List Bool) (cached:List (List Bool)) :
    finished root cached heap=SemiprimeD1StackHeapAllocate.heapBytes cached :=rfl
/-- Abstract acquired-cache reference projection preserves every actual ordinal word. -/
theorem finished_output (root:G.Stack→List Bool) (cached:List (List Bool)) :
    finished root cached output=SemiprimeD1TensorTapeCodec.vectorBits (references cached.length) :=rfl
/-- Abstract acquired-cache counter projection counts exactly the allocated records. -/
theorem finished_counter (root:G.Stack→List Bool) (cached:List (List Bool)) :
    finished root cached (aux .counter)=List.replicate cached.length true :=rfl
/-- The actual physical heap is exactly the original phase-major full-bank catalogue. -/
theorem heap_original (bits:List Bool) : result bits heap=SemiprimeD1StackHeapAllocate.heapBytes
    (records (exponentValue bits) (levelsValue bits) (edgeValue bits) (phases bits)) :=by
  unfold SemiprimeD1StackRootPhaseParametersEncoding.result
  exact finished_heap _ _
/-- Chronological actual stable references are0,...,K-1, represented by acquired unary markers. -/
theorem output_original (bits:List Bool) : result bits output=
    SemiprimeD1TensorTapeCodec.vectorBits (references (phases bits).length) :=by
  unfold SemiprimeD1StackRootPhaseParametersEncoding.result
  rw [finished_output]
  simp only [records,List.length_map]
/-- The physical allocation counter records exactly the actual phase count. -/
theorem counter_original (bits:List Bool) : result bits (aux .counter)=List.replicate (phases bits).length true :=by
  unfold SemiprimeD1StackRootPhaseParametersEncoding.result
  rw [finished_counter]
  simp only [records,List.length_map]
/-- Every actual allocated ordinal remains stable under subsequent allocations. -/
theorem stable_reference (cached future:List (List Bool)) (address:Nat) (ha:address<cached.length) :
    (cached++future)[address]?=cached[address]? :=List.getElem?_append_left ha
/-- Every original phase is in range because its ACTUAL acquired index word has a+1 binary digits. -/
theorem phase_in_range (bits:List Bool) (t:List Bool) (ht:t∈phases bits) : bitValue t<2^(exponentValue bits+1) :=by
  have h:=SemiprimeBitArithmetic.bitValue_lt_width t
  rw [phase_word_width bits t ht] at h
  exact h
/-- Original chronological numeric phase order, with no permutation or omitted rejection. -/
theorem phase_values (bits:List Bool) : (phases bits).map bitValue=
    if SemiprimeD1StackRootPhaseGridEncoding.active bits then List.range (2^(exponentValue bits+1)) else [] :=by
  unfold phases
  split
  · rw [SemiprimeD1StackAssignmentOrder.assignments_values _ _
      (by rw [SemiprimeD1StackAssignmentOrder.zero_remaining])]
    rw [SemiprimeD1OrdinalBankSpec.zero_value,←List.range_eq_range']
  · rfl
/-- Fixed serialized position40 is the actual binary precision output role. -/
theorem role_precision : I.role 40=P.aux .output :=rfl
/-- Fixed serialized position47 is the actual binary dyadic power output role. -/
theorem role_power : I.role 47=P.aux .power :=rfl
/-- Fixed serialized position25 is the actual acquired unary height role. -/
theorem role_height : I.role 25=P.metadataStack (SemiprimeD1StackPhaseWorkingPrecisionMetadata.divStack .quotient) :=rfl
/-- Fixed serialized position32 is the actual acquired unary q role. -/
theorem role_blocks : I.role 32=P.metadataStack (SemiprimeD1StackPhaseWorkingPrecisionMetadata.aux .q) :=rfl
/-- The actual acquired unary height is retained in the complete stopped-bank cache. -/
theorem height_cached (bits:List Bool) (t:List Bool) (ht:t∈phases bits)
    (hg:SemiprimeD1StackPhaseGeometryGuardOriginal.originalGuard (exponentValue bits) (levelsValue bits) t) :
    wordAt (record (exponentValue bits) (levelsValue bits) (edgeValue bits) t) 25=
      List.replicate (SemiprimeD1ModeRate.jetHeight (edgeValue bits) (levelsValue bits)) true :=by
  rw [record_word,role_height]
  exact PO.height_retained _ _ _ t [false,true] (phase_in_range bits t ht) hg
/-- The actual acquired unary q=h*(u-i) survives in its fixed cache ABI position. -/
theorem blocks_cached (bits:List Bool) (t:List Bool) (ht:t∈phases bits)
    (hg:SemiprimeD1StackPhaseGeometryGuardOriginal.originalGuard (exponentValue bits) (levelsValue bits) t) :
    wordAt (record (exponentValue bits) (levelsValue bits) (edgeValue bits) t) 32=
      List.replicate (SemiprimeD1ModeRate.jetHeight (edgeValue bits) (levelsValue bits)*
        (levelsValue bits-PO.originalOrder (exponentValue bits) t)) true :=by
  rw [record_word,role_blocks]
  exact PO.blocks_retained _ _ _ t [false,true] (phase_in_range bits t ht) hg
/-- Cached ABI40 is exact BINARY workingPrecision for every accepted original phase, p=2. -/
theorem precision_cached (bits:List Bool) (t:List Bool) (ht:t∈phases bits)
    (hg:SemiprimeD1StackPhaseGeometryGuardOriginal.originalGuard (exponentValue bits) (levelsValue bits) t) :
    bitValue (wordAt (record (exponentValue bits) (levelsValue bits) (edgeValue bits) t) 40)=
      SemiprimeD1ModeRate.workingPrecision (edgeValue bits) (levelsValue bits) (exponentValue bits)
        (PO.originalOrder (exponentValue bits) t) 2 :=by
  rw [record_word,role_precision]
  exact PO.precision_original _ _ _ t [false,true] (phase_in_range bits t ht) hg
/-- Cached ABI47 is exact BINARY dyadic D for every accepted original phase. -/
theorem power_cached (bits:List Bool) (t:List Bool) (ht:t∈phases bits)
    (hg:SemiprimeD1StackPhaseGeometryGuardOriginal.originalGuard (exponentValue bits) (levelsValue bits) t) :
    bitValue (wordAt (record (exponentValue bits) (levelsValue bits) (edgeValue bits) t) 47)=
      2^(exponentValue bits-PO.originalOrder (exponentValue bits) t) :=by
  rw [record_word,role_power]
  exact PO.power_original _ _ _ t [false,true] (phase_in_range bits t ht) hg
/-- Rejected original phases still occupy their complete actual48-word record;
its binary P/D fields are exactly empty and all old acquired words remain present. -/
theorem rejected_cached (bits:List Bool) (t:List Bool) (ht:t∈phases bits)
    (hg:¬SemiprimeD1StackPhaseGeometryGuardOriginal.originalGuard (exponentValue bits) (levelsValue bits) t) :
    wordAt (record (exponentValue bits) (levelsValue bits) (edgeValue bits) t) 40=[] ∧
      wordAt (record (exponentValue bits) (levelsValue bits) (edgeValue bits) t) 47=[] :=by
  rw [record_word,record_word,role_precision,role_power]
  exact PO.rejected_outputs _ _ _ t [false,true] (phase_in_range bits t ht) hg
/-- The actual stopped-state bank is the exact acquired original-N cache result. -/
theorem done_data (bits:List Bool) : (done bits).data=result bits :=rfl
attribute [local irreducible] SemiprimeD1StackRootPhaseParametersEncoding.result
  SemiprimeD1StackRootPhaseParametersEncoding.done
/-- Whole ORIGINAL binary-N actual source, exact full stopped-bank heap and ordered
stable references, with its OWN fixed polynomial bit clock and all126 source words retained. -/
theorem source_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃t ≤ 10^150*(bits.length+1)^20,
      SemiprimeD1StackCalls.run program t (initial bits)=some (done bits) ∧
      (done bits).data heap=SemiprimeD1StackHeapAllocate.heapBytes
        (records (exponentValue bits) (levelsValue bits) (edgeValue bits) (phases bits)) ∧
      (done bits).data output=SemiprimeD1TensorTapeCodec.vectorBits (references (phases bits).length) ∧
      ∀k:G.Stack,(done bits).data (gridStack k)=SemiprimeD1StackRootPhaseGridEncoding.result bits k :=by
  obtain ⟨t,ht,hr⟩:=source_run_polynomial bits hc hN
  refine ⟨t,ht,hr,?_,?_,?_⟩
  · rw [done_data]
    exact heap_original bits
  · rw [done_data]
    exact output_original bits
  · intro k
    rw [done_data]
    exact grid_preserved bits k
end RiemannGaussian.SemiprimeD1StackRootPhaseParametersOriginal
