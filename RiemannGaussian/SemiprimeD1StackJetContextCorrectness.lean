/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetContextExecution
/-! # Closed original-context physical acquisition
The only input payloads are the encoded positive axes and binary precision.
No rank, decoded precision, suffix or context-answer word is supplied.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 8192
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackJetContextCorrectness
open SemiprimeD1StackJetContext SemiprimeD1StackJetContextExecution
open SemiprimeD1StackProcedureTrace (At runs_trans)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeBitArithmetic (bitValue)

/-- Exact final bank: original inputs, acquired rank/precision markers, no work. -/
def finalData (axes : List ℕ) (precision : List Bool) : Stack → List Bool :=
  bank (vectorBits (axes.map unary)) precision (ready (unary axes.prod) [] [])
    (SemiprimeD1StackAdder.store [] [] [] (SemiprimeD1StackUnaryCounterExecution.markers (bitValue precision)))

/-- Actual full producer cost, including physically discarded suffix records.
Precision conversion pays for its VALUE, not merely its binary input length. -/
def budget (axes : List ℕ) (precision : List Bool) : ℕ :=
  5*(vectorBits (axes.map unary)).length+100*(axes.length+1)*(axes.prod+1)+
    (SemiprimeD1StackJetSuffixOriginal.recordTape axes 1 []).length+
    11*precision.length+7*bitValue precision+17

/-- Every original context field is physically acquired by the same fixed program. -/
theorem source_run (axes : List ℕ) (hp : ∀q∈axes,0<q) (precision : List Bool) :
    ∃ m ≤ budget axes precision,
      SemiprimeD1StackCalls.run program m (initial (vectorBits (axes.map unary)) precision)=
        some (⟨none,none,none,finalData axes precision,[]⟩:SemiprimeD1StackCalls.State Stack Label) := by
  have h1:=axes_copy axes precision
  obtain ⟨ms,hs,h2⟩:=suffix_call axes hp precision
  have h3:=suffix_flag (vectorBits (axes.map unary)) precision (unary axes.prod)
    (SemiprimeD1StackJetSuffixOriginal.recordTape axes 1 [])
  have h4:=clear_records (vectorBits (axes.map unary)) precision (unary axes.prod)
    (SemiprimeD1StackJetSuffixOriginal.recordTape axes 1 [])
  have h5:=precision_copy (vectorBits (axes.map unary)) precision (unary axes.prod)
  obtain ⟨mu,hu,h6⟩:=unary_call (vectorBits (axes.map unary)) precision (unary axes.prod)
  have h:=runs_trans program _ _ _ _ _ _ _ _
    (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _
      (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h1 h2) h3) h4) h5) h6
  have hinit : At .start (initial (vectorBits (axes.map unary)) precision).data []
      (initial (vectorBits (axes.map unary)) precision) := ⟨rfl,rfl,rfl⟩
  obtain ⟨out,hout,hAt⟩:=h [] _ hinit
  have hh:=SemiprimeD1StackProcedureTrace.halt_run program .done rfl (finalData axes precision) [] out hAt
  refine ⟨(5*(vectorBits (axes.map unary)).length+4+ms+1+
    ((SemiprimeD1StackJetSuffixOriginal.recordTape axes 1 []).length+1)+(5*precision.length+4)+mu)+1,?_,?_⟩
  · unfold budget
    omega
  · rw [SemiprimeD1StackReturnLink.run_add,hout,Option.bind_some]
    exact hh

/-- Final physically acquired rank, with no native rank supplier. -/
theorem rank_value (axes : List ℕ) (precision : List Bool) :
    finalData axes precision rankCache=unary axes.prod := rfl
/-- Final physically acquired precision count, with no decoded-count supplier. -/
theorem width_value (axes : List ℕ) (precision : List Bool) :
    (finalData axes precision widthCache).length=bitValue precision := by
  simp [finalData,widthCache,bank,SemiprimeD1StackAdder.store,SemiprimeD1StackUnaryCounterExecution.markers]
/-- Both original physical context inputs are retained exactly. -/
theorem inputs_preserved (axes : List ℕ) (precision : List Bool) :
    finalData axes precision axesCache=vectorBits (axes.map unary) ∧
      finalData axes precision precisionBits=precision := ⟨rfl,rfl⟩

/-- Genuine actual fixed finite-stack acquisition certificate. -/
noncomputable def machineAcquire (axes : List ℕ) (hp : ∀q∈axes,0<q) (precision : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial (vectorBits (axes.map unary)) precision))
      (some (SemiprimeD1StackCalls.configuration
        (⟨none,none,none,finalData axes precision,[]⟩:SemiprimeD1StackCalls.State Stack Label)))
      (budget axes precision) := by
  let h:=source_run axes hp precision
  let m:=Classical.choose h
  have hm:=Classical.choose_spec h
  apply SemiprimeD1StackCalls.evalsCorrect axesCache rankCache Label.start program
  exact ⟨⟨m,hm.2⟩,hm.1⟩

end RiemannGaussian.SemiprimeD1StackJetContextCorrectness
