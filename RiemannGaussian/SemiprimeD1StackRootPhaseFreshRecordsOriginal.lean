/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsStorage
/-! # Exact full85-field original Fresh caches in chronological stable-reference heaps
This is complete N-only phase coefficient-cache acquisition. Phase bodies,
packet execution and the recursive full counter remain separate open consumers.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
set_option exponentiation.threshold 4096
namespace RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsOriginal
open SemiprimeD1StackRootPhaseFreshRecords SemiprimeD1StackRootPhaseFreshRecordsEncoding
open SemiprimeD1StackRootPhaseFreshRecordsBinding SemiprimeD1StackRootPhaseFreshRecordsExecution
open SemiprimeD1StackRootPhaseFreshRecordsBounds
open SemiprimeBitArithmetic (bitValue)
open SemiprimeSourceHistogramKeyBits (frame split)
namespace D
export SemiprimeD1StackRootPhaseParametersOriginal (readWords phase_in_range)
end D
attribute [local irreducible] result done SemiprimeD1StackRootPhaseParametersEncoding.result
/-- Proof-side exact decoding covers all85 fixed physical roles, including empty and rejected fields. -/
theorem read_frames (keys:List F.Stack) (bank:F.Stack→List Bool) (tail:List Bool) :
    D.readWords keys.length (keys.foldr (fun k rest=>frame (bank k) rest) tail)=keys.map bank :=by
  induction keys generalizing tail with
  | nil=>rfl
  | cons k ks ih=>
    simp only [List.length_cons,List.foldr_cons,D.readWords,List.map_cons,
      (SemiprimeSourceHistogramKeyBits.split_frame (bank k) _).1,
      (SemiprimeSourceHistogramKeyBits.split_frame (bank k) _).2.1,ih]
/-- Every cached record contains EXACTLY the entire85-word actual stopped Fresh bank. -/
theorem record_words (a u edges:Nat) (t:List Bool) :
    D.readWords 85 (record a u edges t)=SemiprimeD1StackRootPhaseFreshRecordsInventory.roles.map (freshResult a u edges t) :=by
  have h:=read_frames SemiprimeD1StackRootPhaseFreshRecordsInventory.roles (freshResult a u edges t) []
  rw [SemiprimeD1StackRootPhaseFreshRecordsInventory.roles_length] at h
  exact h
/-- Fixed full-cache ABI readout; no runtime getter is added to the program. -/
def wordAt (bytes:List Bool) (i:Fin 85) :List Bool :=((D.readWords 85 bytes)[i.val]?).getD []
/-- Every fixed ABI role is its exact actual stopped word, with binary/unary encodings unchanged. -/
theorem record_word (a u edges:Nat) (t:List Bool) (i:Fin 85) :
    wordAt (record a u edges t) i=freshResult a u edges t (SemiprimeD1StackRootPhaseFreshRecordsInventory.role i) :=by
  unfold wordAt
  rw [record_words,List.getElem?_map,List.getElem?_eq_getElem
    (show i.val<SemiprimeD1StackRootPhaseFreshRecordsInventory.roles.length by
      rw [SemiprimeD1StackRootPhaseFreshRecordsInventory.roles_length];exact i.isLt)]
  rfl
/-- Exact allocated output heap projection is independent of concrete native N reductions. -/
theorem finished_heap (root:R.Stack→List Bool) (cached:List (List Bool)) :
    finished root cached heap=SemiprimeD1StackHeapAllocate.heapBytes cached :=rfl
/-- Actual allocator references are0,...,K-1 in their original chronological order. -/
theorem finished_output (root:R.Stack→List Bool) (cached:List (List Bool)) :
    finished root cached output=SemiprimeD1TensorTapeCodec.vectorBits (O.references cached.length) :=rfl
/-- Actual fresh allocator counter has exactly one physical marker per issued record. -/
theorem finished_counter (root:R.Stack→List Bool) (cached:List (List Bool)) :
    finished root cached (aux .counter)=List.replicate cached.length true :=rfl
/-- The actual output heap contains all85-field original phase Fresh caches, in phase order. -/
theorem heap_original (bits:List Bool) :
    result bits heap=SemiprimeD1StackHeapAllocate.heapBytes
      (records (O.exponentValue bits) (O.levelsValue bits) (O.edgeValue bits) (O.phases bits)) :=by
  unfold result
  exact finished_heap _ _
/-- Every originally issued reference is retained in exactly the source phase order. -/
theorem output_original (bits:List Bool) :
    result bits output=SemiprimeD1TensorTapeCodec.vectorBits (O.references (O.phases bits).length) :=by
  unfold result
  rw [finished_output]
  simp only [records,List.length_map]
/-- Exact final physical allocation count follows from the actual complete original phase list. -/
theorem counter_original (bits:List Bool) :
    result bits (aux .counter)=List.replicate (O.phases bits).length true :=by
  unfold result
  rw [finished_counter]
  simp only [records,List.length_map]
/-- All188 acquired root/grid/sourceheap/reference cells survive literally; source is never replayed. -/
theorem source_preserved (bits:List Bool) (k:R.Stack) :result bits (rootStack k)=O.result bits k :=by
  unfold result
  exact finished_root _ _ k
/-- Original binary N survives byte for byte. -/
theorem input_preserved (bits:List Bool) :result bits originalInput=bits :=
  (source_preserved bits R.originalInput).trans (SemiprimeD1StackRootPhaseParametersOriginal.input_preserved bits)
/-- Stable logical references remain valid under every subsequent physical allocation. -/
theorem stable_reference (cached future:List (List Bool)) (address:Nat) (ha:address<cached.length) :
    (cached++future)[address]?=cached[address]? :=List.getElem?_append_left ha
/-- Presence of an actually acquired phase establishes the ORIGINAL active parent u≤ M fact. -/
theorem phase_levels (bits:List Bool) (t:List Bool) (ht:t∈O.phases bits) :O.levelsValue bits ≤ O.edgeValue bits :=by
  have ha:SemiprimeD1StackRootPhaseGridEncoding.active bits=true:=by
    unfold O.phases at ht
    split at ht
    · assumption
    · cases ht
  have hh:SemiprimeD1Schedule.Active (SemiprimeD1StackRootRecursiveControlEncoding.scaleValue bits)
      (SemiprimeD1StackRootRecursiveControlEncoding.lambdaValue bits) 0 (O.edgeValue bits):=
    (SemiprimeD1RecursiveCounter.activeTest_correct _ _ _ _).mp ha
  exact hh.2.2
/-- For every original accepted grid phase, the cached coefficient vector is
EXACT original FreshJetBits.acquireFresh with actual native q/P and old empty axes. -/
theorem coefficients_original (bits:List Bool) (t:List Bool) (ht:t∈O.phases bits)
    (hg:SemiprimeD1StackPhaseGeometryGuardOriginal.originalGuard (O.exponentValue bits) (O.levelsValue bits) t) :
    freshResult (O.exponentValue bits) (O.levelsValue bits) (O.edgeValue bits) t
      (SemiprimeD1StackPhaseChildContextFresh.aux .output)=SemiprimeD1TensorTapeCodec.vectorBits
        (SemiprimeD1FreshJetBits.acquireFresh
          (SemiprimeD1StackPhaseChildContextOriginal.oldContext [] [false,true])
          (SemiprimeD1ModeRate.jetHeight (O.edgeValue bits) (O.levelsValue bits)*
            (O.levelsValue bits-SemiprimeD1StackPhaseWorkingPrecisionOriginal.originalOrder (O.exponentValue bits) t))
          (SemiprimeD1ModeRate.workingPrecision (O.edgeValue bits) (O.levelsValue bits) (O.exponentValue bits)
            (SemiprimeD1StackPhaseWorkingPrecisionOriginal.originalOrder (O.exponentValue bits) t) 2)).words :=by
  exact SemiprimeD1StackPhaseChildContextFreshOriginal.output_phase_original _ _ _ t [false,true] []
    (D.phase_in_range bits t ht) (phase_levels bits t ht) hg
/-- A physically rejected cache is still serialized in its exact chronological
position, with its actual EMPTY coefficient output retained in the full85word record. -/
theorem coefficients_rejected (a u edges:Nat) (t:List Bool)
    (hg:SemiprimeD1StackPhaseChildContextArithmetic.good a u edges t=false) :
    freshResult a u edges t (SemiprimeD1StackPhaseChildContextFresh.aux .output)=[] :=
  SemiprimeD1StackPhaseChildContextFreshOriginal.rejected_output a u edges t [false,true] [] hg
/-- Abstract genuine halt projection avoids reducing the concrete original-N cache list. -/
theorem done_data (bits:List Bool) :(done bits).data=result bits :=by unfold done;rfl
/-- SAME complete original-N source, exact whole85cache heap and ordered references,
with its own closed polynomial bit-clock; no phase-body callback or native source supplier remains. -/
theorem source_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃q ≤ 10^650*(bits.length+1)^80,SemiprimeD1StackCalls.run program q (initial bits)=some (done bits) ∧
      (done bits).data heap=SemiprimeD1StackHeapAllocate.heapBytes
        (records (O.exponentValue bits) (O.levelsValue bits) (O.edgeValue bits) (O.phases bits)) ∧
      (done bits).data output=SemiprimeD1TensorTapeCodec.vectorBits (O.references (O.phases bits).length) :=by
  obtain ⟨q,hq,hr⟩:=source_run_polynomial bits hc hN
  refine ⟨q,hq,hr,?_,?_⟩
  · rw [done_data];exact heap_original bits
  · rw [done_data];exact output_original bits
end RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsOriginal
