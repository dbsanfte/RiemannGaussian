/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVectorTableSpec
import RiemannGaussian.SemiprimeD1StackVectorTablePrimitives
/-! # Actual complete-vector preserving copy, tree tag and history reversal -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 262144
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackVectorTableEmit
open SemiprimeD1StackVectorTable SemiprimeD1StackVectorTableSpec
open SemiprimeD1StackVectorTablePrimitives SemiprimeD1StackProcedureTrace
variable {K L : Type} [DecidableEq K] (s : Static K L)
/-- Actual preserving-copy output, buffer and restoration scratch remain distinct. -/
theorem vectorCopy_call (d : Stack K→List Bool) (hw : d (aux .work)=[]) (hs : d (aux .scratch)=[]) :
    Runs (program s) (5*(d (checker s.output)).length+4) .emitSentinel d .emitLeaf
      (Function.update d (aux .work) (d (checker s.output))) := by
  let word := d (checker s.output)
  let start := SemiprimeD1StackCopy.state 0 none word [] []
  let stop := SemiprimeD1StackCopy.done word word
  have hi : Link.DataRel (vectorCopyStack s) d start.store d := by
    constructor
    · intro k;fin_cases k
      · rfl
      · exact hw
      · exact hs
    · intro k _;rfl
  have ho := Link.data_update (vectorCopyStack s) (vectorCopy_injective s) d start.store d hi (1:Fin 3) word
  have he : Function.update start.store 1 word=stop.store := by
    funext k;fin_cases k <;> rfl
  rw [he] at ho
  exact included_call (program s) (vectorCopyStack s) (vectorCopyLabel s) (vectorCopy_injective s)
    SemiprimeD1StackCopy.code 0 (vectorCopy_program s) .emitSentinel .emitLeaf rfl _
    start stop d _ rfl rfl (by simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words word [] none) hi ho
omit [DecidableEq K] in
/-- The private record buffer is distinct from accumulated DFS history. -/
theorem recordReverse_injective : Function.Injective (recordReverseStack (K:=K)) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [recordReverseStack,aux]
/-- Actual consuming reversal appends exactly this record's reversed bytes to history. -/
theorem recordReverse_call (d : Stack K → List Bool) :
    Runs (program s) (2*(d (aux .work)).length+3) .emitReverse d .leafCleanup
      (Function.update (Function.update d (aux .work) []) (aux .reversed)
        ((d (aux .work)).reverse++d (aux .reversed))) := by
  let xs := d (aux .work)
  let ys := d (aux .reversed)
  let start := SemiprimeD1StackReverseWord.state none xs ys
  let stop := SemiprimeD1StackReverseWord.done (xs.reverse++ys)
  have hi : Link.DataRel recordReverseStack d start.store d := by
    constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  have h0 := Link.data_update recordReverseStack recordReverse_injective d start.store d hi (0:Fin 2) []
  have ho := Link.data_update recordReverseStack recordReverse_injective d _ _ h0 (1:Fin 2) (xs.reverse++ys)
  have he : Function.update (Function.update start.store 0 []) 1 (xs.reverse++ys)=stop.store := by
    funext k;fin_cases k <;> rfl
  rw [he] at ho
  exact included_call (program s) recordReverseStack _root_.RiemannGaussian.SemiprimeD1StackStaticWordTable.Label.recordReverse recordReverse_injective
    SemiprimeD1StackReverseWord.code 0 (fun _ => rfl) .emitReverse .leafCleanup rfl _
    start stop d _ rfl rfl (SemiprimeD1StackReverseWord.reverse_run xs ys none) hi ho
omit [DecidableEq K] in
/-- The complete ACTUAL vector payload receives exactly one tree-leaf FALSE tag. -/
def leafBytes (payload : List Bool) : List Bool := false::payload
omit [DecidableEq K] in
/-- No source vector framing is duplicated or interpreted by the compiler. -/
theorem leafBytes_length (payload : List Bool) : (leafBytes payload).length=payload.length+1 := rfl
/-- Proof-only view of the actual temporary framing buffer. -/
def emitData (live original : K → List Bool) (bank front hist buffer : List Bool) : Stack K → List Bool :=
  store live original (D.data bank [] [] [] [] [] []) front buffer [] hist []
/-- A physical buffer update preserves all checker, template and scanner words. -/
theorem update_buffer (live original : K → List Bool) (bank front hist buffer fresh : List Bool) :
    Function.update (emitData live original bank front hist buffer) (aux .work) fresh=
      emitData live original bank front hist fresh := by
  funext k;rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · cases k <;> rfl
/-- A physical history update preserves every other acquired word and empty helper. -/
theorem update_history (live original : K → List Bool) (bank front hist buffer fresh : List Bool) :
    Function.update (emitData live original bank front hist buffer) (aux .reversed) fresh=
      emitData live original bank front fresh buffer := by
  funext k;rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · cases k <;> rfl
/-- Complete actual vector copying, tree-leaf tagging and consuming reversal, with every call/return charged. -/
theorem emit_run (live original : K→List Bool) (bank front hist : List Bool) :
    Runs (program s) (7*(live s.output).length+8) .emitSentinel
      (withChecker (data original bank 0 front hist) live) .leafCleanup
      (withChecker (data original bank 0 front ((leafBytes (live s.output)).reverse++hist)) live) := by
  let payload := live s.output
  have h0 := vectorCopy_call s (emitData live original bank front hist []) rfl rfl
  change Runs (program s) (5*payload.length+4) .emitSentinel
    (emitData live original bank front hist []) .emitLeaf
    (Function.update (emitData live original bank front hist []) (aux .work) payload) at h0
  rw [update_buffer] at h0
  have h1 := push s .emitLeaf .emitReverse (aux .reversed) false rfl
    (emitData live original bank front hist payload)
  change Runs (program s) 1 .emitLeaf (emitData live original bank front hist payload) .emitReverse
    (Function.update (emitData live original bank front hist payload) (aux .reversed) (false::hist)) at h1
  rw [update_history] at h1
  have h2 := recordReverse_call s (emitData live original bank front (false::hist) payload)
  change Runs (program s) (2*payload.length+3) .emitReverse
    (emitData live original bank front (false::hist) payload) .leafCleanup
    (Function.update (Function.update (emitData live original bank front (false::hist) payload)
      (aux .work) []) (aux .reversed) (payload.reverse++false::hist)) at h2
  rw [update_buffer,update_history] at h2
  have he : payload.reverse++false::hist=(leafBytes payload).reverse++hist := by
    simp only [leafBytes,List.reverse_cons,List.append_assoc,List.singleton_append]
  rw [he] at h2
  have hh := runs_trans (program s) _ _ _ _ _ _ _ _ (runs_trans (program s) _ _ _ _ _ _ _ _ h0 h1) h2
  convert hh using 1
  · dsimp only [payload];omega
  · funext k;cases k <;> rfl
  · funext k;cases k <;> rfl
/-- Exact literal leaf bytes in the entire false-first table specification. -/
theorem leaf_bytes (answer : List Bool→List (List Bool)) (raw : List Bool) :
    leafBytes (SemiprimeD1TensorTapeCodec.vectorBits (answer raw))=SemiprimeD1TensorTapeCodec.tape (tree answer raw 0) := rfl
end RiemannGaussian.SemiprimeD1StackVectorTableEmit

