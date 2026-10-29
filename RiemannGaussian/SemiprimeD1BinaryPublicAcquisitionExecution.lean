/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BinaryPublicAcquisitionComponents

/-! # One binary-input public preprocessing execution
The entire elapsed bound counts digit acquisition, shared-metadata constant and
axis construction, all three real call/return traces and the actual final halt.
-/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1BinaryPublicAcquisitionExecution
open SemiprimeD1BinaryPublicAcquisition SemiprimeD1BinaryPublicAcquisitionComponents
open SemiprimeD1StackProcedureTrace

/-- One fixed original-width transition bound. -/
def timeBound (bits : List Bool) : ℕ := 800000*(bits.length+1)^2

/-- Complete actual source trace from binary N ONLY. All retained words are
produced by literal code; no supplied parameter, index or digit is required. -/
theorem source_run (bits : List Bool) (hb : bits≠[]) :
    ∃time ≤ timeBound bits,C.run program time (initial bits)=
      some (⟨none,none,none,result bits,[]⟩:C.State Stack Label) := by
  obtain ⟨t,ht,h0⟩:=digit_call bits hb
  have h1:=fermat_call bits
  have h2:=axes_call bits
  have h01:=runs_trans program _ _ _ _ _ _ _ _ h0 h1
  have h012:=runs_trans program _ _ _ _ _ _ _ _ h01 h2
  obtain ⟨finish,hfinish,hout⟩:=h012 [] (initial bits) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (mainLabel .done) rfl (result bits) [] finish hout
  refine ⟨(t+1)+(fermatTime bits.length+1)+(axesTime bits.length+1)+1,?_,?_⟩
  · have hf:=SemiprimeD1StackFermatExecution.totalTime_le bits.length
    have ha:=SemiprimeD1StackAxesArithmetic.totalTime_le bits.length
    have hfl : fermatTime bits.length ≤ SemiprimeD1StackFermatExecution.totalTime bits.length := by
      unfold fermatTime SemiprimeD1StackFermatExecution.totalTime
      omega
    have hal : axesTime bits.length ≤ SemiprimeD1StackAxesArithmetic.totalTime bits.length := by
      unfold axesTime SemiprimeD1StackAxesArithmetic.totalTime
      omega
    have hf':=hfl.trans hf
    have ha':=hal.trans ha
    unfold timeBound SemiprimeD1BinaryDigitAcquisitionExecution.timeBound at *
    have hp : 0 < (bits.length+1)^2 := by positivity
    omega
  · rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hh]

/-- The only initial cells agree with the genuine binary finite-machine input. -/
theorem initial_configuration (bits : List Bool) :
    SemiprimeD1StackCalls.configuration (initial bits)=Turing.initList machine bits := by
  have hs : initial bits=SemiprimeD1StackCalls.initial
      (digitStack (Digits.metaStack .input)) (mainLabel .start) bits := by
    unfold initial input store SemiprimeD1StackCalls.initial
    congr 1
    funext k
    rcases k with k|k
    · rcases k with k|k
      · cases k <;> rfl
      · rcases k with k|k <;> rfl
    · rcases k with k|k <;> rfl
  rw [hs]
  exact SemiprimeD1StackCalls.initial_correct
    (digitStack (Digits.metaStack .input))
    (digitStack (Digits.bankStack SemiprimeD1StackDigitBank.output)) (mainLabel .start) program bits

/-- Proof-side choice of a proved actual trace length; the executing instruction
table itself is fully computable and contains no choice/evaluator opcode. -/
noncomputable def sourceAcquire (bits : List Bool) (hb : bits≠[]) :
    StateTransition.EvalsToInTime (C.step program) (initial bits)
      (some (⟨none,none,none,result bits,[]⟩:C.State Stack Label)) (timeBound bits) := by
  let h:=source_run bits hb
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩

/-- Actual finite-machine preprocessing from the single original binary input,
with the same acquired constants, axes, metadata and EVERY input digit. -/
noncomputable def acquireInTime (bits : List Bool) (hb : bits≠[]) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (⟨none,none,none,result bits,[]⟩:C.State Stack Label)))
      (timeBound bits) := by
  have hh:=SemiprimeD1StackCalls.evalsCorrect
    (digitStack (Digits.metaStack .input))
    (digitStack (Digits.bankStack SemiprimeD1StackDigitBank.output)) (mainLabel .start)
    program _ _ _ (sourceAcquire bits hb)
  change StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (initial bits))
    (some (SemiprimeD1StackCalls.configuration (⟨none,none,none,result bits,[]⟩:C.State Stack Label)))
      (timeBound bits) at hh
  exact Eq.mp (congrArg (fun start : machine.Cfg=>StateTransition.EvalsToInTime machine.step start
    (some (SemiprimeD1StackCalls.configuration (⟨none,none,none,result bits,[]⟩:C.State Stack Label)))
      (timeBound bits)) (initial_configuration bits)) hh

end RiemannGaussian.SemiprimeD1BinaryPublicAcquisitionExecution
