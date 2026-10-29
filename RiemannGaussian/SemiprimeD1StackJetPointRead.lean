/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetPointExecution
/-! # Actual cached binary coefficient reads inside convolution
Each selected coefficient is physically parsed/copied from its existing encoded
vector. Original arrays appear only in the refinement proof, not in machine code.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackJetPointRead
open SemiprimeD1StackJetPoint SemiprimeD1StackJetPointExecution
open SemiprimeD1StackProcedureTrace (Runs)
namespace V
export SemiprimeD1StackJetRead (state store program)
end V

/-- Declarative invariant when one actual reader's index is prepared. -/
def reading (c : Cache) (i j acc query other : List Bool) (right : Bool) : Stack → List Bool :=
  Function.update (loaded c i j acc (if right then other else []) (if right then [] else other))
    (aux .index) query

/-- Real cached read and all cleanup, at either literal reader-call site.
The only cache relation is exact physical input encoding; no getter answer,
field-bound oracle, or execution-clock supplier is an argument. -/
theorem read_call (c : Cache) (i j acc query other : List Bool) (right : Bool)
    (words : List (List Bool))
    (hc : (if right then c.b else c.a)=SemiprimeD1TensorTapeCodec.vectorBits words) :
    Runs program (SemiprimeD1StackJetReadExecution.totalTime query words+1)
      (if right then .readRightCall else .readLeftCall) (reading c i j acc query other right)
      (if right then .multiply else .readRightCopy)
      (Function.update (Function.update (reading c i j acc query other right) (aux .index) [])
        (readStack right .output) ((words[query.length]?).getD [])) := by
  apply SemiprimeD1StackProcedureInclusion.included_call program (readStack right) (Label.read right)
    (readStack_injective right) V.program .start (fun _=>rfl)
    (if right then .readRightCall else .readLeftCall) (if right then .multiply else .readRightCopy)
    (by cases right <;> rfl) _
    (V.state (some .start) none none (SemiprimeD1TensorTapeCodec.vectorBits words) [] query [] [] [] [] [])
    (V.state none none none (SemiprimeD1TensorTapeCodec.vectorBits words) [] [] [] [] ((words[query.length]?).getD []) [] [])
  · rfl
  · rfl
  · rfl
  · rfl
  · exact SemiprimeD1StackJetReadExecution.source_run query words
  · constructor
    · intro k
      cases right <;> cases k <;>
        simp [reading,loaded,resting,readStack,aux,mulStack,
          SemiprimeD1StackMultiplier.input,SemiprimeD1StackMultiplier.factor,V.state,V.store] at hc ⊢ <;> assumption
    · intro k hk
      rfl
  · constructor
    · intro k
      cases right <;> cases k <;>
        simp [reading,loaded,resting,readStack,aux,mulStack,
          SemiprimeD1StackMultiplier.input,SemiprimeD1StackMultiplier.factor,V.state,V.store] at hc ⊢ <;> assumption
    · intro k hk
      have hi : k ≠ aux .index := fun he=>hk .index he.symm
      have ho : k ≠ readStack right .output := fun he=>hk .output he.symm
      simp only [Function.update_of_ne ho,Function.update_of_ne hi]

/-- The actual read result restores the loop workspace and loads only the
selected multiplier operand; padding is preserved verbatim. -/
theorem read_result (c : Cache) (i j acc query other : List Bool) (right : Bool) (word : List Bool) :
    Function.update (Function.update (reading c i j acc query other right) (aux .index) [])
      (readStack right .output) word=
    loaded c i j acc (if right then other else word) (if right then word else other) := by
  funext k
  cases right <;> rcases k with k|k
  · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k
        · cases k <;> rfl
        · rcases k with k|k
          · fin_cases k <;> rfl
          · cases k <;> rfl
      · cases k <;> rfl
    · rcases k with k|k
      · cases k <;> rfl
      · cases k <;> rfl
  · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k
        · cases k <;> rfl
        · rcases k with k|k
          · fin_cases k <;> rfl
          · cases k <;> rfl
      · cases k <;> rfl
    · rcases k with k|k
      · cases k <;> rfl
      · cases k <;> rfl

/-- Empty multiplier inputs are the actual clean loop invariant. -/
theorem loaded_empty (c : Cache) (i j acc : List Bool) :
    loaded c i j acc [] []=resting c i j acc := by
  unfold loaded
  have hi : resting c i j acc (mulStack (.inl SemiprimeD1StackMultiplier.input))=[] := rfl
  have hf : resting c i j acc (mulStack (.inl SemiprimeD1StackMultiplier.factor))=[] := rfl
  rw [(Function.update_eq_self_iff.mpr hi.symm :
    Function.update (resting c i j acc) (mulStack (.inl SemiprimeD1StackMultiplier.input)) []=resting c i j acc)]
  exact Function.update_eq_self_iff.mpr hf.symm

/-- Exact transition count of both physical cache reads and linked binary arithmetic. -/
def readPipelineTime (width i j acc : List Bool) (a b : List (List Bool)) : ℕ :=
  let left:=(a[i.length]?).getD []
  let right:=(b[j.length]?).getD []
  ((((5*i.length+4)+(SemiprimeD1StackJetReadExecution.totalTime i a+1))+(5*j.length+4))+
    (SemiprimeD1StackJetReadExecution.totalTime j b+1))+pipelineTime left right acc width

/-- Complete actual selected-pair path: real counter copies, two physical
vector reads, multiplication, modular addition and temporary cleanup. -/
theorem read_pipeline (c : Cache) (i j acc : List Bool) (a b : List (List Bool))
    (ha : c.a=SemiprimeD1TensorTapeCodec.vectorBits a)
    (hb : c.b=SemiprimeD1TensorTapeCodec.vectorBits b) :
    Runs program (readPipelineTime c.width i j acc a b) .readLeftCopy (resting c i j acc) .inner
      (resting c i j (SemiprimeD1StackJetScalarAddExecution.result
        (SemiprimeD1StackJetScalarMulExecution.result ((a[i.length]?).getD []) ((b[j.length]?).getD []) c.width)
        acc c.width)) := by
  let left:=(a[i.length]?).getD []
  let right:=(b[j.length]?).getD []
  have h1:=copy_call .readI .readLeftCopy .readLeftCall (resting c i j acc) rfl (by rfl) (by rfl)
  change Runs program (5*i.length+4) .readLeftCopy (resting c i j acc) .readLeftCall
    (Function.update (resting c i j acc) (aux .index) i) at h1
  have hprepare : Function.update (resting c i j acc) (aux .index) i=reading c i j acc i [] false := by
    simp only [reading,Bool.false_eq_true,ite_false,loaded_empty]
  rw [hprepare] at h1
  have h2:=read_call c i j acc i [] false a ha
  rw [read_result] at h2
  change Runs program _ .readLeftCall _ .readRightCopy (loaded c i j acc left []) at h2
  have h3:=copy_call .readJ .readRightCopy .readRightCall (loaded c i j acc left []) rfl (by rfl) (by rfl)
  change Runs program (5*j.length+4) .readRightCopy (loaded c i j acc left []) .readRightCall
    (reading c i j acc j left true) at h3
  have h4:=read_call c i j acc j left true b hb
  rw [read_result] at h4
  change Runs program _ .readRightCall _ .multiply (loaded c i j acc left right) at h4
  have h5:=pipeline_run c i j acc left right
  exact SemiprimeD1StackProcedureTrace.runs_trans program _ _ _ _ _ _ _ _
    (SemiprimeD1StackProcedureTrace.runs_trans program _ _ _ _ _ _ _ _
      (SemiprimeD1StackProcedureTrace.runs_trans program _ _ _ _ _ _ _ _
        (SemiprimeD1StackProcedureTrace.runs_trans program _ _ _ _ _ _ _ _ h1 h2) h3) h4) h5

end RiemannGaussian.SemiprimeD1StackJetPointRead
