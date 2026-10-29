/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsLoop
/-! # Exact binding of physical issued references to original acquired phase banks -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsBinding
open SemiprimeD1StackRootPhaseFreshRecords SemiprimeD1StackRootPhaseFreshRecordsEncoding
open SemiprimeD1StackRootPhaseFreshRecordsSource SemiprimeD1StackRootPhaseFreshRecordsRows
open SemiprimeD1StackRootPhaseFreshRecordsLoop
namespace O
export SemiprimeD1StackRootPhaseParametersEncoding (exponentValue levelsValue edgeValue phases result references)
export SemiprimeD1StackRootPhaseParametersOriginal (heap_original counter_original output_original)
end O
/-- Literal chronological source indices and their corresponding phase words; proof specification only. -/
def entries (a u edges:Nat) (rows:List (List Bool)) :List (Entry (banks a u edges rows)) :=
  List.ofFn (fun i:Fin rows.length=>(⟨i.val,by simpa only [banks,List.length_map] using i.isLt⟩,rows[i.val]))
/-- Every actual issued ordinal refers to exactly its originally produced P48 bank. -/
theorem entries_bank (a u edges:Nat) (rows:List (List Bool)) (e:Entry (banks a u edges rows))
    (he:e∈entries a u edges rows) :
    (banks a u edges rows)[e.1.val]=SemiprimeD1StackPhaseCacheFreshComponents.phase a u edges e.2 [false,true] :=by
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp he
  exact bank_at a u edges rows i
/-- Finite original source ordinals retain their literal chronological numeric order. -/
theorem finRange_values (m:Nat) :(List.finRange m).map Fin.val=List.range m :=by
  induction m with
  | zero=>rfl
  | succ m ih=>simp only [List.finRange_succ,List.map_cons,List.map_map,Fin.val_zero,Fin.val_succ,
      List.range_succ_eq_map,←ih,List.map_map,Function.comp_def,Nat.succ_eq_add_one]
/-- The source's retained issued-reference vector is precisely the physical pointer-loop tape. -/
theorem entries_tape (a u edges:Nat) (rows:List (List Bool)) :
    tape (entries a u edges rows)=SemiprimeD1TensorTapeCodec.vectorBits (O.references rows.length) :=by
  rw [tape,A.rowTape_vector]
  congr 1
  unfold entries
  rw [List.ofFn_eq_map,List.map_map]
  change (List.finRange rows.length).map ((fun i=>List.replicate i true)∘Fin.val)=_
  rw [←List.map_map,finRange_values]
  rfl
/-- Full85-cache records follow the original phase list exactly, including rejected phases. -/
theorem entries_cached (a u edges:Nat) (rows:List (List Bool)) :
    cached a u edges (entries a u edges rows)=records a u edges rows :=by
  unfold cached entries records
  rw [List.map_ofFn]
  exact List.ofFn_getElem_eq_map rows (record a u edges)
/-- Actual N-only source heap, interpreted by the actual48-field restore grammar, with no new supplier. -/
theorem source_heap (bits:List Bool) :
    O.result bits R.heap=E.heap (banks (O.exponentValue bits) (O.levelsValue bits) (O.edgeValue bits) (O.phases bits)) :=by
  rw [O.heap_original]
  unfold E.heap
  rw [records_bridge]
/-- The physically retained source counter counts exactly the heap bank list. -/
theorem source_counter (bits:List Bool) :
    O.result bits (R.aux .counter)=List.replicate
      (banks (O.exponentValue bits) (O.levelsValue bits) (O.edgeValue bits) (O.phases bits)).length true :=by
  rw [O.counter_original]
  simp only [banks,List.length_map]
/-- The real source reference output is exactly the sweep reader, in its original forward order. -/
theorem source_reader (bits:List Bool) :
    O.result bits R.output=tape (entries (O.exponentValue bits) (O.levelsValue bits) (O.edgeValue bits) (O.phases bits)) :=by
  rw [O.output_original,entries_tape]
end RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsBinding
