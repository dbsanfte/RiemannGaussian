/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTransformSetup
/-! # Actual consecutive input/output vector acquisition from raw assignment
No prepared vector/word family, arity/count answer or getter is an executing
input. Count and width caches are the original acquisition's ACTUAL copies.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformWords
open SemiprimeD1StackPublicTransform SemiprimeD1StackPublicTransformState SemiprimeD1StackPublicTransformSetup
open SemiprimeD1StackProcedureTrace
/-- Actual physical M cache read, proof-side only. -/
def modulusWord (root : R.Stack→List Bool) : List Bool := root (.inl R.modulusKey)
/-- Actual acquired n-marker cache read, proof-side only. -/
def countWord (root : R.Stack→List Bool) (second : Bool) : List Bool := root (axisRole second)
/-- The actual unread raw source after first n physical word blocks. -/
def outputRaw (root : R.Stack→List Bool) (raw : List Bool) (second : Bool) : List Bool :=
  raw.drop ((countWord root second).length*(modulusWord root).length)
/-- The first actual acquired word family, specification only. -/
def inputs (root : R.Stack→List Bool) (raw : List Bool) (second : Bool) : List (List Bool) :=
  SemiprimeD1StackWordVectorSpec.blocks (modulusWord root) (countWord root second).length raw
/-- The second actual acquired word family, specification only. -/
def outputs (root : R.Stack→List Bool) (raw : List Bool) (second : Bool) : List (List Bool) :=
  SemiprimeD1StackWordVectorSpec.blocks (modulusWord root) (countWord root second).length (outputRaw root raw second)
/-- Actual raw copy after metadata/normalization has been physically constructed. -/
def inputReady (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) : Parts :=
  copied (normalizedParts root raw second inverse) .rawInput
/-- Exact complete state after whole first WordVector call. -/
def inputAcquired (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) : Parts :=
  {inputReady root raw second inverse with inputVector:=
    (SemiprimeD1StackWordVectorExecution.done raw (modulusWord root) (countWord root second)).data}
/-- The actual unread output block is physically copied to the second producer. -/
def outputReady (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) : Parts :=
  copied (inputAcquired root raw second inverse) .rawOutput
/-- Exact complete state after BOTH actual word-vector acquisitions. -/
def bothAcquired (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) : Parts :=
  {outputReady root raw second inverse with outputVector:=
    (SemiprimeD1StackWordVectorExecution.done (outputRaw root raw second) (modulusWord root) (countWord root second)).data}
/-- The original raw input is a real preserving copy, never a native grouping. -/
theorem input_copy (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) :
    Runs program (5*raw.length+4) .copyRawInput (data (normalizedParts root raw second inverse)) .acquireInput
      (data (inputReady root raw second inverse)) :=
  copy_run .rawInput .copyRawInput .acquireInput rfl (normalizedParts root raw second inverse) rfl rfl
/-- Original source/width/count placement equals the ACTUAL first producer input. -/
theorem input_initial (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) :
    (inputReady root raw second inverse).inputVector=(W.initial raw (modulusWord root) (countWord root second)).data := by
  funext k;rcases k with k|k <;> fin_cases k <;> rfl
/-- WHOLE first vector producer executes; every read/copy/pad/frame is retained. -/
theorem input_call (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) :
    ∃t≤SemiprimeD1StackWordVectorExecution.timeBound raw (modulusWord root) (countWord root second)+1,
      Runs program t .acquireInput (data (inputReady root raw second inverse)) .copyRawOutput
        (data (inputAcquired root raw second inverse)) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackWordVectorExecution.source_run raw (modulusWord root) (countWord root second)
  refine ⟨t+1,Nat.add_le_add_right ht 1,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program Stack.inputVector Label.inputWords
    (by intro i j h;exact Stack.inputVector.inj h) W.program (.control .start) (fun _=>rfl)
    .acquireInput .copyRawOutput rfl t (W.initial raw (modulusWord root) (countWord root second))
    (SemiprimeD1StackWordVectorExecution.done raw (modulusWord root) (countWord root second)) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;exact congrFun (input_initial root raw second inverse) k
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;cases k <;> first | rfl | exact (hk _ rfl).elim
/-- Output-source acquisition copies the ACTUAL first producer's unread suffix. -/
theorem output_copy (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) :
    Runs program (5*(outputRaw root raw second).length+4) .copyRawOutput
      (data (inputAcquired root raw second inverse)) .acquireOutput (data (outputReady root raw second inverse)) :=
  copy_run .rawOutput .copyRawOutput .acquireOutput rfl (inputAcquired root raw second inverse) rfl rfl
/-- Output producer is filled by physical source/caches, not supplied output words. -/
theorem output_initial (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) :
    (outputReady root raw second inverse).outputVector=
      (W.initial (outputRaw root raw second) (modulusWord root) (countWord root second)).data := by
  funext k;rcases k with k|k <;> fin_cases k <;> rfl
/-- WHOLE second producer executes on the physically copied unread suffix. -/
theorem output_call (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) :
    ∃t≤SemiprimeD1StackWordVectorExecution.timeBound (outputRaw root raw second) (modulusWord root) (countWord root second)+1,
      Runs program t .acquireOutput (data (outputReady root raw second inverse)) .copyInputDot
        (data (bothAcquired root raw second inverse)) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackWordVectorExecution.source_run (outputRaw root raw second) (modulusWord root) (countWord root second)
  refine ⟨t+1,Nat.add_le_add_right ht 1,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program Stack.outputVector Label.outputWords
    (by intro i j h;exact Stack.outputVector.inj h) W.program (.control .start) (fun _=>rfl)
    .acquireOutput .copyInputDot rfl t (W.initial (outputRaw root raw second) (modulusWord root) (countWord root second))
    (SemiprimeD1StackWordVectorExecution.done (outputRaw root raw second) (modulusWord root) (countWord root second))
    _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;exact congrFun (output_initial root raw second inverse) k
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;cases k <;> first | rfl | exact (hk _ rfl).elim
/-- Actual executed two-vector acquisition allowance, including all source copies. -/
def wordsBudget (root : R.Stack→List Bool) (raw : List Bool) (second : Bool) : ℕ :=
  (5*raw.length+4)+(SemiprimeD1StackWordVectorExecution.timeBound raw (modulusWord root) (countWord root second)+1)+
    (5*(outputRaw root raw second).length+4)+
    (SemiprimeD1StackWordVectorExecution.timeBound (outputRaw root raw second) (modulusWord root) (countWord root second)+1)
/-- ENTIRE literal raw→input/output vectors; no word/vector/count answer premise. -/
theorem words_run (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) :
    ∃t≤wordsBudget root raw second,Runs program t .copyRawInput
      (data (normalizedParts root raw second inverse)) .copyInputDot (data (bothAcquired root raw second inverse)) := by
  obtain ⟨u,hu,h0⟩:=input_call root raw second inverse
  obtain ⟨v,hv,h1⟩:=output_call root raw second inverse
  have h:=runs_trans program _ _ _ _ _ _ _ _
    (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ (input_copy root raw second inverse) h0)
      (output_copy root raw second inverse)) h1
  refine ⟨(5*raw.length+4)+u+(5*(outputRaw root raw second).length+4)+v,?_,h⟩
  unfold wordsBudget;omega
end RiemannGaussian.SemiprimeD1StackPublicTransformWords
