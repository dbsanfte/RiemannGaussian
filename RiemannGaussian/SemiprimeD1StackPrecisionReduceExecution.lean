/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPrecisionReduce

/-! # Actual parsed binary-precision reduction
The only loaded input is a framed pair of binary words. Every parser, counter
construction and scalar reduction executes in the one fixed finite machine.
This is an internal arithmetic caller, not the full semiprime factor machine.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPrecisionReduceExecution
open SemiprimeD1StackPrecisionReduce SemiprimeD1StackProcedureTrace SemiprimeBitArithmetic
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeD1StackUnaryCounterExecution (markers)

/-- The original framed input has only two binary words, no marker advice. -/
def input (word precision : List Bool) : List Bool := frame word (frame precision [])

/-- Literal new result bytes, specified by the existing canonical reducer. -/
def result (word precision : List Bool) : List Bool :=
  (SemiprimeD1JetScalarBits.reduce (bitValue precision) word).bits

/-- Exact actual binary-to-unary trace length, including input reversal. -/
def unaryTime (precision : List Bool) : ℕ :=
  2*precision.length+1+SemiprimeD1StackUnaryCounterExecution.loopTime precision.reverse 0

/-- Exact actual reducer trace length after the marker counter has been built. -/
def reduceTime (word precision : List Bool) : ℕ :=
  SemiprimeD1StackReduceExecution.trimTime
    (word.take (markers (bitValue precision)).length).reverse+
      SemiprimeD1StackReduceExecution.prefixTime word (markers (bitValue precision))

/-- Four real procedure calls, two real flag pops and the final actual halt. -/
def totalTime (word precision : List Bool) : ℕ :=
  (8*word.length+7)+1+(8*precision.length+7)+1+
    (unaryTime precision+1)+(reduceTime word precision+1)+1

/-- Full source execution: both actual parsed fields, physical precision
acquisition, literal reduction, all workspace and return frames cleared. -/
theorem source_run (word precision : List Bool) :
    C.run program (totalTime word precision)
      (⟨some .start,none,none,store (input word precision) [] [] [] [] [] [] [],[]⟩:C.State Stack Label)=
      some (⟨none,none,none,store [] [] [] [] [] [] (result word precision) [],[]⟩:C.State Stack Label) := by
  let d0:=store (input word precision) [] [] [] [] [] [] []
  let d1:=store (frame precision []) word [] [] [] [] [] [true]
  let d2:=store (frame precision []) word [] [] [] [] [] []
  let d3:=store [] word precision [] [] [] [] [true]
  let d4:=store [] word precision [] [] [] [] []
  let d5:=store [] word [] (markers (bitValue precision)) [] [] [] []
  let d6:=store [] [] [] [] [] [] (result word precision) []
  have h0 : Runs program (8*word.length+7) .start d0 .wordValid d1 := by
    apply included_call program (fieldStack false) (Label.field false) (fieldStack_injective false)
      Field.code (Field.active .tagPop (none,false)) (fun _=>rfl) .start .wordValid rfl
      (8*word.length+6) (Field.initial (input word precision) [])
      (⟨none,none,Sum.elim
        (SemiprimeD1TensorTapeFieldMachine.contents (frame precision []) [] word)
        (fun _=>[true])⟩:B.State Field.Stack Field.Label) d0 d1
    · rfl
    · rfl
    · exact Field.framed_run word (frame precision []) []
    · constructor
      · intro k;rcases k with k|k <;> cases k <;> rfl
      · intro k _;rfl
    · constructor
      · intro k;rcases k with k|k <;> cases k <;> rfl
      · intro k hk
        have hi:=hk (.inl .input)
        have ho:=hk (.inl .output)
        have hv:=hk (.inr ())
        cases k <;> simp_all [d0,d1,store,fieldStack]
  have h1 : Runs program 1 .wordValid d1 .precisionCall d2 := by
    apply one_base program .wordValid .precisionCall (.pop .valid .done .done .precisionCall) d1 d2 rfl
    · rfl
    · funext k;cases k <;> rfl
  have h2 : Runs program (8*precision.length+7) .precisionCall d2 .precisionValid d3 := by
    apply included_call program (fieldStack true) (Label.field true) (fieldStack_injective true)
      Field.code (Field.active .tagPop (none,false)) (fun _=>rfl) .precisionCall .precisionValid rfl
      (8*precision.length+6) (Field.initial (frame precision []) [])
      (⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents [] [] precision)
        (fun _=>[true])⟩:B.State Field.Stack Field.Label) d2 d3
    · rfl
    · rfl
    · exact Field.framed_run precision [] []
    · constructor
      · intro k;rcases k with k|k <;> cases k <;> rfl
      · intro k _;rfl
    · constructor
      · intro k;rcases k with k|k <;> cases k <;> rfl
      · intro k hk
        have hi:=hk (.inl .input)
        have ho:=hk (.inl .output)
        have hv:=hk (.inr ())
        cases k <;> simp_all [d2,d3,store,fieldStack]
  have h3 : Runs program 1 .precisionValid d3 .counterCall d4 := by
    apply one_base program .precisionValid .counterCall (.pop .valid .done .done .counterCall) d3 d4 rfl
    · rfl
    · funext k;cases k <;> rfl
  have h4 : Runs program (unaryTime precision+1) .counterCall d4 .counterDone d5 := by
    apply included_call program unaryStack Label.unary unaryStack_injective Unary.code .reverse
      (fun _=>rfl) .counterCall .counterDone rfl (unaryTime precision)
      (Unary.state (some .reverse) none precision [] [] [])
      (Unary.state none none [] [] [] (markers (bitValue precision))) d4 d5
    · rfl
    · rfl
    · exact SemiprimeD1StackUnaryCounterExecution.source_run precision
    · constructor
      · intro k;cases k <;> rfl
      · intro k _;rfl
    · constructor
      · intro k;cases k <;> rfl
      · intro k hk
        have hp:=hk .left
        have hw:=hk .output
        cases k <;> simp_all [d4,d5,store,unaryStack]
  have h5 : Runs program (reduceTime word precision+1) .counterDone d5 .done d6 := by
    apply included_call program reduceStack Label.reduce reduceStack_injective Reduce.code .take
      (fun _=>rfl) .counterDone .done rfl (reduceTime word precision)
      (Reduce.state (some .take) none word (markers (bitValue precision)) [] [])
      (Reduce.state none none [] [] [] (result word precision)) d5 d6
    · rfl
    · rfl
    · have hh := SemiprimeD1StackReduceExecution.source_run word (markers (bitValue precision))
      simpa only [reduceTime,result,SemiprimeD1StackUnaryCounterExecution.marker_count] using hh
    · constructor
      · intro k;cases k <;> rfl
      · intro k _;rfl
    · constructor
      · intro k;cases k <;> rfl
      · intro k hk
        have hw:=hk .left
        have hp:=hk .right
        have ho:=hk .output
        cases k <;> simp_all [d5,d6,store,reduceStack]
  have h01:=runs_trans program _ _ _ _ _ _ _ _ h0 h1
  have h012:=runs_trans program _ _ _ _ _ _ _ _ h01 h2
  have h0123:=runs_trans program _ _ _ _ _ _ _ _ h012 h3
  have h01234:=runs_trans program _ _ _ _ _ _ _ _ h0123 h4
  have h012345:=runs_trans program _ _ _ _ _ _ _ _ h01234 h5
  obtain ⟨finish,hfinish,hout⟩:=h012345 []
    (⟨some .start,none,none,d0,[]⟩:C.State Stack Label) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl d6 [] finish hout
  rw [totalTime,SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hh]

/-- Every acquisition and cleanup operation is included in a linear bound in
word width, precision bit width and precision VALUE. -/
theorem totalTime_le (word precision : List Bool) :
    totalTime word precision ≤ 13*word.length+14*precision.length+12*bitValue precision+32 := by
  have hu:=SemiprimeD1StackUnaryCounterExecution.source_time precision
  have hr:= (SemiprimeD1StackReduceExecution.sourceReduce word (markers (bitValue precision))).steps_le_m
  change reduceTime word precision ≤ 5*(word.length+(markers (bitValue precision)).length)+10 at hr
  rw [SemiprimeD1StackUnaryCounterExecution.marker_count] at hr
  unfold totalTime unaryTime
  omega

/-- Real source certificate starts with only the framed binary pair. -/
def sourceReduce (word precision : List Bool) :
    StateTransition.EvalsToInTime (C.step program)
      (⟨some .start,none,none,store (input word precision) [] [] [] [] [] [] [],[]⟩:C.State Stack Label)
      (some (⟨none,none,none,store [] [] [] [] [] [] (result word precision) [],[]⟩:C.State Stack Label))
      (13*word.length+14*precision.length+12*bitValue precision+32) :=
  ⟨⟨_,source_run word precision⟩,totalTime_le word precision⟩

/-- Physical start is the actual single-input initialization, with no other operands loaded. -/
theorem start_configuration (bits : List Bool) :
    SemiprimeD1StackCalls.configuration
      (⟨some .start,none,none,store bits [] [] [] [] [] [] [],[]⟩:C.State Stack Label)=
        Turing.initList machine bits := by
  have hs : (⟨some .start,none,none,store bits [] [] [] [] [] [] [],[]⟩:C.State Stack Label)=
      SemiprimeD1StackCalls.initial Stack.input Label.start bits := by
    congr 1
    funext k
    cases k <;> rfl
  rw [hs]
  exact SemiprimeD1StackCalls.initial_correct Stack.input Stack.result Label.start program bits

/-- Actual halt has only the computed reducer result; return and work stacks are empty. -/
theorem finish_configuration (bits : List Bool) :
    SemiprimeD1StackCalls.configuration
      (⟨none,none,none,store [] [] [] [] [] [] bits [],[]⟩:C.State Stack Label)=
        Turing.haltList machine bits := by
  have hs : (⟨none,none,none,store [] [] [] [] [] [] bits [],[]⟩:C.State Stack Label)=
      SemiprimeD1StackCalls.final Stack.result bits := by
    congr 1
    funext k
    cases k <;> rfl
  rw [hs]
  exact SemiprimeD1StackCalls.final_correct Stack.input Stack.result Label.start program bits

/-- The single original framed binary input suffices for actual canonical
modular reduction. Counter construction and all physical parses are paid. -/
def machineReduce (word precision : List Bool) :
    Turing.TM2OutputsInTime machine (input word precision) (some (result word precision))
      (13*word.length+14*precision.length+12*bitValue precision+32) := by
  have hh:=SemiprimeD1StackCalls.evalsCorrect Stack.input Stack.result Label.start program _ _ _
    (sourceReduce word precision)
  change StateTransition.EvalsToInTime machine.step
    (SemiprimeD1StackCalls.configuration
      (⟨some .start,none,none,store (input word precision) [] [] [] [] [] [] [],[]⟩:C.State Stack Label))
    (some (SemiprimeD1StackCalls.configuration
      (⟨none,none,none,store [] [] [] [] [] [] (result word precision) [],[]⟩:C.State Stack Label)))
      (13*word.length+14*precision.length+12*bitValue precision+32) at hh
  have hh0:=Eq.mp (congrArg (fun start : machine.Cfg=>
    StateTransition.EvalsToInTime machine.step start
      (some (SemiprimeD1StackCalls.configuration
        (⟨none,none,none,store [] [] [] [] [] [] (result word precision) [],[]⟩:C.State Stack Label)))
        (13*word.length+14*precision.length+12*bitValue precision+32))
        (start_configuration (input word precision))) hh
  exact Eq.mp (congrArg (fun finish : machine.Cfg=>
    StateTransition.EvalsToInTime machine.step (Turing.initList machine (input word precision))
      (some finish) (13*word.length+14*precision.length+12*bitValue precision+32))
        (finish_configuration (result word precision))) hh0

end RiemannGaussian.SemiprimeD1StackPrecisionReduceExecution
