/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseExecution
/-! # Actual four-input bit lengths pay all restored words and fold nodes
Every bound is derived from actual bytes or the SAME literal restorer run.
Neither selected-record height nor fold-node count is a runtime operand.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseInputBounds
open SemiprimeD1StackCachePhase SemiprimeD1StackCachePhaseExecution
open SemiprimeD1StackJetFoldWords SemiprimeD1StackJetFoldInputBounds
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Exactly the actual heap/counter/reference/child-tape bit cells, plus one. -/
def inputSize (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (modes:Modes) :Nat :=
  SemiprimeD1StackFreshBankRestoreBounds.inputSize banks i+(modeTape modes).length
/-- Actual nonempty input inventory, independently of phase acceptance. -/
theorem inputSize_pos (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (modes:Modes) :
    0 < inputSize banks i modes :=by
  unfold inputSize SemiprimeD1StackFreshBankRestoreBounds.inputSize SemiprimeD1StackFreshBankRestoreBounds.resource
  omega
/-- Each restored word is paid by the SAME actual heap-access run and its own linear clock. -/
theorem restored_word_le (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (modes:Modes) (k:Restore.Stack) :
    (restored banks i k).length≤1001*inputSize banks i modes :=by
  have hi:∀j,((SemiprimeD1StackFreshBankRestoreExecution.source banks i).data j).length≤
      SemiprimeD1StackFreshBankRestoreBounds.inputSize banks i:=
    SemiprimeD1StackFreshBankRestoreBounds.initial_length (heap banks) (counter banks) (reference banks i)
  have h:=SemiprimeD1StackReturnLink.run_data_bound Restore.program
    (SemiprimeD1StackFreshBankRestoreExecution.runBound banks i)
    (SemiprimeD1StackFreshBankRestoreBounds.inputSize banks i) _ _ hi
    (SemiprimeD1StackFreshBankRestoreExecution.run_exact banks i) k
  have ht:=SemiprimeD1StackFreshBankRestoreBounds.runBound_le banks i
  change (restored banks i k).length≤_ at h
  unfold SemiprimeD1StackFreshBankRestoreBounds.linearBound at ht
  unfold inputSize
  omega
/-- Every real vector field pays its tag, delimiter and all raw payload bits. -/
theorem vector_cons_length (word:List Bool) (words:List (List Bool)) :
    (vectorBits (word::words)).length=2*word.length+2+(vectorBits words).length :=by
  change (true::SemiprimeSourceHistogramKeyBits.frame word (vectorBits words)).length=_
  simp only [List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length]
  omega
/-- The actual vector bit length pays each field constructor, including empty fields. -/
theorem vector_count_le (words:List (List Bool)) :words.length≤(vectorBits words).length :=by
  have h:=SemiprimeD1StackNetworkRowsEncoding.vector_length words
  omega
/-- One physical group tape pays its actual largest child result without a supplied field-height cap. -/
theorem groupMax_le_tape (group:Group) :groupMax group≤(groupTape group).length :=by
  induction group with
  | nil=>exact Nat.zero_le _
  | cons x xs ih=>
    have hl:(groupTape (x::xs)).length=2*(jetTape x).length+2+(groupTape xs).length:=
      vector_cons_length (jetTape x) (xs.map jetTape)
    change max (jetTape x).length (groupMax xs)≤_
    exact max_le (by omega) (by omega)
/-- The four-input source pays its largest child field from actual nested tape bytes. -/
theorem childMax_le_tape (modes:Modes) :childMax modes≤(modeTape modes).length :=by
  induction modes with
  | nil=>exact Nat.zero_le _
  | cons x xs ih=>
    have hx:=groupMax_le_tape x
    have hl:(modeTape (x::xs)).length=2*(groupTape x).length+2+(modeTape xs).length:=
      vector_cons_length (groupTape x) (xs.map groupTape)
    change max (groupMax x) (childMax xs)≤_
    exact max_le (by omega) (by omega)
/-- Every actual sum/product node, including all base cases, is paid by actual source constructors. -/
theorem workNodes_le_tape (modes:Modes) :workNodes modes≤(modeTape modes).length :=by
  induction modes with
  | nil=>rfl
  | cons x xs ih=>
    have hx:x.length≤(groupTape x).length:=by
      simpa only [groupTape,List.length_map] using vector_count_le (x.map jetTape)
    have hl:(modeTape (x::xs)).length=2*(groupTape x).length+2+(modeTape xs).length:=
      vector_cons_length (groupTape x) (xs.map groupTape)
    change x.length+2+workNodes xs≤_
    omega
end RiemannGaussian.SemiprimeD1StackCachePhaseInputBounds
