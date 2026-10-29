/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFreshBankRestoreBounds
import RiemannGaussian.SemiprimeD1StackFreshBankRestoreLineage
import RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsOriginal
/-! # Actual Root345 issued-reference lineage and complete Fresh85 restoration
The physical root producer determines the heap, allocation count and ordered
reference vector. This consumer restores their exact original stopped words;
it never reruns phase geometry, contexts or coefficient acquisition.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackFreshBankRestoreOriginal
open SemiprimeD1StackFreshBankRestore SemiprimeD1StackFreshBankRestoreExecution
open SemiprimeD1StackFreshBankRestoreBounds
namespace R
export SemiprimeD1StackRootPhaseFreshRecords (Stack heap output aux program initial)
end R
namespace E
export SemiprimeD1StackRootPhaseFreshRecordsEncoding (freshRecord freshResult records result done)
end E
namespace O
export SemiprimeD1StackRootPhaseParametersEncoding (phases references exponentValue levelsValue edgeValue)
end O
namespace Old
export SemiprimeD1StackRootPhaseFreshRecordsOriginal
  (heap_original counter_original output_original source_original)
end Old
namespace L
export SemiprimeD1StackFreshBankRestoreLineage (history issued)
end L
attribute [local irreducible] SemiprimeD1StackRootPhaseFreshRecordsEncoding.result
  SemiprimeD1StackRootPhaseFreshRecordsEncoding.freshResult
  SemiprimeD1StackRootPhaseParametersEncoding.phases
  SemiprimeD1StackRootPhaseParametersEncoding.exponentValue
  SemiprimeD1StackRootPhaseParametersEncoding.levelsValue
  SemiprimeD1StackRootPhaseParametersEncoding.edgeValue
/-- Generic physical initial-state bridge, before any original arithmetic source is instantiated. -/
theorem initial_from (bs:List (F.Stack→List Bool)) (i:Fin bs.length) (heap counter reference:List Bool)
    (hh:heap=SemiprimeD1StackHeapAllocate.heapBytes (records bs))
    (hc:counter=List.replicate bs.length true) (hr:reference=List.replicate i.val true):
    initial heap counter reference=source bs i:=by
  subst heap;subst counter;subst reference;rfl
/-- Generic complete physical target bridge avoids expanding any native original bank. -/
theorem done_from (bs:List (F.Stack→List Bool)) (i:Fin bs.length) (bank:F.Stack→List Bool)
    (heap counter reference:List Bool) (hb:bank=bs[i.val])
    (hh:heap=SemiprimeD1StackHeapAllocate.heapBytes (records bs))
    (hc:counter=List.replicate bs.length true) (hr:reference=List.replicate i.val true):
    done bank heap counter reference=target bs i:=by
  subst bank;subst heap;subst counter;subst reference;rfl
/-- Generic physical-byte bound bridge uses only the actual three input words. -/
theorem cap_from (bs:List (F.Stack→List Bool)) (i:Fin bs.length) (heap counter reference:List Bool)
    (hh:heap=SemiprimeD1StackHeapAllocate.heapBytes (records bs))
    (hc:counter=List.replicate bs.length true) (hr:reference=List.replicate i.val true):
    1000*resource heap counter reference=linearBound bs i:=by
  subst heap;subst counter;subst reference;rfl
/-- Exact generic physical-byte resource equality, independent of native original graph definitions. -/
theorem resource_from (bs:List (F.Stack→List Bool)) (i:Fin bs.length) (heap counter reference:List Bool)
    (hh:heap=SemiprimeD1StackHeapAllocate.heapBytes (records bs))
    (hc:counter=List.replicate bs.length true) (hr:reference=List.replicate i.val true):
    resource heap counter reference=inputSize bs i:=by
  subst heap;subst counter;subst reference;rfl
/-- The consumer's fixed85 consecutive frames are IDENTICAL to the actual producer's record ABI. -/
theorem record_abi (bank:F.Stack→List Bool):record bank=E.freshRecord bank:=rfl
/-- Proof-side names of every actual originally stopped Fresh bank, in original phase order. -/
def banks (bits:List Bool):List (F.Stack→List Bool):=
  (O.phases bits).map (E.freshResult (O.exponentValue bits) (O.levelsValue bits) (O.edgeValue bits))
/-- The phase ordinal is only cast across the exact original bank-list length. -/
def ordinal (bits:List Bool) (i:Fin (O.phases bits).length):Fin (banks bits).length:=
  ⟨i.val,by simpa only [banks,List.length_map] using i.isLt⟩
/-- Every complete record follows the exact original chronological phase, including rejected/repeated banks. -/
theorem records_original (bits:List Bool):records (banks bits)=
    E.records (O.exponentValue bits) (O.levelsValue bits) (O.edgeValue bits) (O.phases bits):=by
  simp only [records,banks,E.records,List.map_map,Function.comp_def,record_abi]
  rfl
/-- The actual original allocation counter counts the entire acquired phase list. -/
theorem banks_length (bits:List Bool):(banks bits).length=(O.phases bits).length:=by
  simp only [banks,List.length_map]
/-- Exact selected original stopped bank, without decoding or recomputing any field. -/
theorem bank_at (bits:List Bool) (i:Fin (O.phases bits).length):
    (banks bits)[(ordinal bits i).val]=E.freshResult (O.exponentValue bits) (O.levelsValue bits)
      (O.edgeValue bits) (O.phases bits)[i.val]:=by
  simp only [banks,ordinal,List.getElem_map]
/-- Original reference bytes are the literal i-th entry of the physically produced ordered vector. -/
def reference (bits:List Bool) (i:Fin (O.phases bits).length):List Bool:=
  (O.references (O.phases bits).length)[i.val]'(by
    simpa only [O.references,List.length_map,List.length_range] using i.isLt)
/-- The actual issued byte word at chronological position i has exactly i unary markers. -/
theorem reference_eq (bits:List Bool) (i:Fin (O.phases bits).length):reference bits i=List.replicate i.val true:=by
  simp only [reference,O.references,List.getElem_map,List.getElem_range]
/-- The ENTIRE actual source reference output has its original chronological byte layout. -/
theorem output_references (bits:List Bool):E.result bits R.output=
    SemiprimeD1TensorTapeCodec.vectorBits (List.ofFn (fun i:Fin (O.phases bits).length=>reference bits i)):=by
  rw [Old.output_original]
  simp only [reference_eq]
  congr 1
  unfold O.references
  simpa only [List.length_range,List.getElem_range,Fin.val_cast] using
    (List.ofFn_getElem_eq_map (List.range (O.phases bits).length) (fun n=>List.replicate n true)).symm
/-- Genuine allocator transitions witness the exact physical original Root345 heap/counter history. -/
theorem root_history (bits:List Bool):SemiprimeD1StackHeapReadBounds.History (records (banks bits))
    (E.result bits R.heap) (E.result bits (R.aux .counter)):=by
  have h:=L.history (records (banks bits))
  have hl:(records (banks bits)).length=(O.phases bits).length:=by
    simp only [records,List.length_map,banks_length]
  rw [hl] at h
  rw [Old.heap_original,Old.counter_original,←records_original]
  exact h
/-- Actual source heap bytes match the complete chronological stored bank records. -/
theorem root_heap (bits:List Bool):E.result bits R.heap=SemiprimeD1StackHeapAllocate.heapBytes (records (banks bits)):=
  (Old.heap_original bits).trans (congrArg SemiprimeD1StackHeapAllocate.heapBytes (records_original bits).symm)
/-- Actual source counter is the literal original complete bank count. -/
theorem root_counter (bits:List Bool):E.result bits (R.aux .counter)=List.replicate (banks bits).length true:=by
  rw [banks_length]
  exact Old.counter_original bits
/-- Every actual i-th output reference was physically issued and persists through subsequent allocations. -/
theorem root_issued (bits:List Bool) (i:Fin (O.phases bits).length):
    SemiprimeD1StackHeapReadBounds.Issued (records (banks bits)) (reference bits i):=by
  rw [reference_eq]
  have h:=L.issued (records (banks bits)) (index (banks bits) (ordinal bits i))
  exact h
/-- Actual N-only producer execution and issued-reference lineage hold together for the SAME reached heap. -/
theorem producer_lineage (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0<SemiprimeBitArithmetic.bitValue bits):
    ∃q ≤ SemiprimeD1StackRootPhaseFreshRecordsExecution.runBound bits,
      SemiprimeD1StackCalls.run R.program q (R.initial bits)=some (E.done bits) ∧
      SemiprimeD1StackHeapReadBounds.History (records (banks bits))
        (E.result bits R.heap) (E.result bits (R.aux .counter)) ∧
      E.result bits R.output=SemiprimeD1TensorTapeCodec.vectorBits
        (List.ofFn (fun i:Fin (O.phases bits).length=>reference bits i)) ∧
      ∀i:Fin (O.phases bits).length,
        SemiprimeD1StackHeapReadBounds.Issued (records (banks bits)) (reference bits i):=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackRootPhaseFreshRecordsExecution.source_run bits hc hN
  exact ⟨q,hq,hr,root_history bits,output_references bits,root_issued bits⟩
/-- Honest prepared consumer inputs are ONLY the actual reached heap/counter and its actual issued reference. -/
def initialRoot (bits:List Bool) (i:Fin (O.phases bits).length):C.State Stack Label:=
  initial (E.result bits R.heap) (E.result bits (R.aux .counter)) (reference bits i)
/-- Exact restored target contains ALL85 original stopped fields and ALL10 completed heap-reader roles. -/
def doneRoot (bits:List Bool) (i:Fin (O.phases bits).length):C.State Stack Label:=
  done (E.freshResult (O.exponentValue bits) (O.levelsValue bits) (O.edgeValue bits) (O.phases bits)[i.val])
    (E.result bits R.heap) (E.result bits (R.aux .counter)) (reference bits i)
/-- Original actual operands match the complete physical generic source, with no supplied answer tape. -/
theorem initialRoot_eq (bits:List Bool) (i:Fin (O.phases bits).length):
    initialRoot bits i=source (banks bits) (ordinal bits i):=by
  exact initial_from (banks bits) (ordinal bits i) _ _ _ (root_heap bits) (root_counter bits) (reference_eq bits i)
/-- Exact reached physical target is the original selected bank, including all rejected/empty caches. -/
theorem doneRoot_eq (bits:List Bool) (i:Fin (O.phases bits).length):doneRoot bits i=target (banks bits) (ordinal bits i):=by
  exact done_from (banks bits) (ordinal bits i) _ _ _ _ (bank_at bits i).symm
    (root_heap bits) (root_counter bits) (reference_eq bits i)
/-- Exact whole physical-input byte bound of the original cache consumer. -/
theorem capRoot_eq (bits:List Bool) (i:Fin (O.phases bits).length):
    1000*resource (E.result bits R.heap) (E.result bits (R.aux .counter)) (reference bits i)=
      linearBound (banks bits) (ordinal bits i):=
  cap_from (banks bits) (ordinal bits i) _ _ _ (root_heap bits) (root_counter bits) (reference_eq bits i)
/-- SAME actual95-role consumer restores the original selected bank at its actual input-byte linear clock. -/
theorem source_original (bits:List Bool) (i:Fin (O.phases bits).length):
    ∃q ≤1000*resource (E.result bits R.heap) (E.result bits (R.aux .counter)) (reference bits i),
      SemiprimeD1StackCalls.run program q (initialRoot bits i)=some (doneRoot bits i):=by
  obtain ⟨q,hq,hr⟩:=source_run_linear (banks bits) (ordinal bits i)
  refine ⟨q,?_,?_⟩
  · exact hq.trans (capRoot_eq bits i).ge
  · exact (congrArg (SemiprimeD1StackCalls.run program q) (initialRoot_eq bits i)).trans
      (hr.trans (congrArg some (doneRoot_eq bits i)).symm)
/-- ALL95 tapes and real return cells at every original-input consumer prefix use the SAME physical byte cap. -/
theorem prefix_original (bits:List Bool) (i:Fin (O.phases bits).length) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initialRoot bits i)=some out):
    (∑k:Stack,(out.data k).length)+out.frames.length ≤
      100000*resource (E.result bits R.heap) (E.result bits (R.aux .counter)) (reference bits i):=by
  have hr':SemiprimeD1StackCalls.run program fuel (source (banks bits) (ordinal bits i))=some out:=
    (congrArg (SemiprimeD1StackCalls.run program fuel) (initialRoot_eq bits i)).symm.trans hr
  have h:=prefix_cells (banks bits) (ordinal bits i) fuel out hr'
  have hs:=resource_from (banks bits) (ordinal bits i) _ _ _ (root_heap bits) (root_counter bits) (reference_eq bits i)
  exact h.trans (congrArg (fun n=>100000*n) hs).ge
/-- Every original Fresh field is restored literally; OLD and NEW precision/context banks stay distinct. -/
theorem fresh_restored (bits:List Bool) (i:Fin (O.phases bits).length) (k:F.Stack):
    (doneRoot bits i).data (freshStack k)=E.freshResult (O.exponentValue bits) (O.levelsValue bits)
      (O.edgeValue bits) (O.phases bits)[i.val] k:=rfl
/-- Every heap-reader role equals the real completed reader's preserved inputs and cleared private words. -/
theorem heap_retained (bits:List Bool) (i:Fin (O.phases bits).length) (k:H.Stack):
    (doneRoot bits i).data (heapStack k)=H.input (E.result bits R.heap)
      (E.result bits (R.aux .counter)) (reference bits i) k:=rfl
/-- Genuine compiled95-role endpoint consumes the actual original issued bytes at its own source clock. -/
noncomputable def restoreOriginalInTime (bits:List Bool) (i:Fin (O.phases bits).length):
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (initialRoot bits i))
      (some (SemiprimeD1StackCalls.configuration (doneRoot bits i)))
      (1000*resource (E.result bits R.heap) (E.result bits (R.aux .counter)) (reference bits i)):=by
  apply SemiprimeD1StackCalls.evalsCorrect originalInput output (.inl .start) program
  let h:=source_original bits i
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackFreshBankRestoreOriginal
