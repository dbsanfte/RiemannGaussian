/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackStaticWordTableSpec
import RiemannGaussian.SemiprimeD1StackStaticWordTablePrimitives
/-! # Actual binary coefficient Frame, vector/tree tags and history reversal -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 262144
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackStaticWordTableEmit
open SemiprimeD1StackStaticWordTable SemiprimeD1StackStaticWordTableSpec
open SemiprimeD1StackStaticWordTablePrimitives SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
variable {K L : Type} [DecidableEq K] (s : Static K L)
omit [DecidableEq K] in
/-- Static Frame operands never alias, for any fixed physical checker. -/
theorem frame_injective : Function.Injective (frameStack s) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [frameStack,checker,aux]
omit [DecidableEq K] in
/-- The private record buffer is distinct from the accumulated DFS history. -/
theorem recordReverse_injective : Function.Injective (recordReverseStack (K:=K)) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [recordReverseStack,aux]
/-- Real preserving Frame pays each coefficient bit and its real caller/return. -/
theorem frame_call (d : Stack K → List Bool) (hs : d (aux .scratch)=[]) :
    Runs (program s) (6*(d (checker s.output)).length+5) .emitFrame d .emitTag
      (Function.update d (aux .work) (frame (d (checker s.output)) (d (aux .work)))) := by
  let start := SemiprimeD1StackFrame.state 0 none (d (checker s.output)) (d (aux .work)) []
  let stop := SemiprimeD1StackFrame.done (d (checker s.output))
    (frame (d (checker s.output)) (d (aux .work)))
  have hi : Link.DataRel (frameStack s) d start.store d := by
    constructor
    · intro k;fin_cases k
      · rfl
      · rfl
      · exact hs
    · intro k _;rfl
  have ho := Link.data_update (frameStack s) (frame_injective s) d start.store d hi (1:Fin 3)
    (frame (d (checker s.output)) (d (aux .work)))
  have he : Function.update start.store 1 (frame (d (checker s.output)) (d (aux .work)))=stop.store := by
    funext k;fin_cases k <;> rfl
  rw [he] at ho
  exact included_call (program s) (frameStack s) Label.frame (frame_injective s)
    SemiprimeD1StackFrame.code 0 (fun _ => rfl) .emitFrame .emitTag rfl _
    start stop d _ rfl rfl (SemiprimeD1StackFrame.frame_words _ _ none) hi ho
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
  exact included_call (program s) recordReverseStack Label.recordReverse recordReverse_injective
    SemiprimeD1StackReverseWord.code 0 (fun _ => rfl) .emitReverse .leafCleanup rfl _
    start stop d _ rfl rfl (SemiprimeD1StackReverseWord.reverse_run xs ys none) hi ho
omit [DecidableEq K] in
/-- Literal one-coefficient tree leaf, including all framing and terminators. -/
def leafBytes (word : List Bool) : List Bool := false::SemiprimeD1TensorTapeCodec.vectorBits [word]
omit [DecidableEq K] in
/-- Every coefficient bit is retained in the physical prefix-free leaf. -/
theorem leafBytes_length (word : List Bool) : (leafBytes word).length=2*word.length+4 := by
  simp only [leafBytes,SemiprimeD1TensorTapeCodec.vectorBits,List.length_cons,
    SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
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
/-- COMPLETE actual coefficient serialization. Its cost pays Frame, each tag,
the whole leaf reversal, and every real call and return. -/
theorem emit_run (live original : K → List Bool) (bank front hist : List Bool) :
    Runs (program s) (10*(live s.output).length+19) .emitSentinel
      (withChecker (data original bank 0 front hist) live) .leafCleanup
      (withChecker (data original bank 0 front ((leafBytes (live s.output)).reverse++hist)) live) := by
  let d := emitData live original bank front hist
  have h0 := push s .emitSentinel .emitFrame (aux .work) false rfl (d [])
  change Runs (program s) 1 .emitSentinel (d []) .emitFrame (Function.update (d []) (aux .work) [false]) at h0
  rw [update_buffer] at h0
  have h1 := frame_call s (d [false]) rfl
  change Runs (program s) (6*(live s.output).length+5) .emitFrame (d [false]) .emitTag
    (Function.update (d [false]) (aux .work) (frame (live s.output) [false])) at h1
  rw [update_buffer] at h1
  have h2 := push s .emitTag .emitLeaf (aux .work) true rfl (d (frame (live s.output) [false]))
  change Runs (program s) 1 .emitTag (d (frame (live s.output) [false])) .emitLeaf
    (Function.update (d (frame (live s.output) [false])) (aux .work) (true::frame (live s.output) [false])) at h2
  rw [update_buffer] at h2
  have h3 := push s .emitLeaf .emitReverse (aux .work) false rfl (d (true::frame (live s.output) [false]))
  change Runs (program s) 1 .emitLeaf (d (true::frame (live s.output) [false])) .emitReverse
    (Function.update (d (true::frame (live s.output) [false])) (aux .work) (leafBytes (live s.output))) at h3
  rw [update_buffer] at h3
  have h4 := recordReverse_call s (d (leafBytes (live s.output)))
  change Runs (program s) (2*(leafBytes (live s.output)).length+3) .emitReverse
    (d (leafBytes (live s.output))) .leafCleanup
    (Function.update (Function.update (d (leafBytes (live s.output))) (aux .work) []) (aux .reversed)
      ((leafBytes (live s.output)).reverse++hist)) at h4
  rw [update_buffer,update_history] at h4
  have hh := runs_trans (program s) _ _ _ _ _ _ _ _
    (runs_trans (program s) _ _ _ _ _ _ _ _
      (runs_trans (program s) _ _ _ _ _ _ _ _ (runs_trans (program s) _ _ _ _ _ _ _ _ h0 h1) h2) h3) h4
  convert hh using 1
  · rw [leafBytes_length];omega
  · funext k;cases k <;> rfl
  · funext k;cases k <;> rfl
/-- Exact literal leaf bytes in the entire false-first table specification. -/
theorem leaf_bytes (answer : List Bool → List Bool) (raw : List Bool) :
    leafBytes (answer raw)=SemiprimeD1TensorTapeCodec.tape (tree answer raw 0) := rfl
end RiemannGaussian.SemiprimeD1StackStaticWordTableEmit

