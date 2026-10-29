/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackAxesArithmetic
import RiemannGaussian.SemiprimeD1StackAxesStages

/-! # Original-input axes and depth execution
The reusable stage reads actual retained metadata. The complete fixed machine
initializes only binary N and literally executes the metadata procedure first.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackAxesExecution
open SemiprimeD1StackAxes SemiprimeD1StackAxesComponents SemiprimeD1StackAxesStages
open SemiprimeD1StackAxesLoop SemiprimeD1StackAxesArithmetic
open SemiprimeD1StackProcedureFragments (At Runs)
open SemiprimeMacroParameters
namespace MetaOut
export SemiprimeD1StackTransformExecution (result)
end MetaOut

/-- Mathematical view of the actually emitted unary axes and depth. -/
def result (bits:List Bool) : Stack→List Bool :=
  data (MetaOut.result bits) [] [] [] (List.replicate (firstAxis bits.length) true)
    (List.replicate (secondAxis bits.length) true) (List.replicate (macroDepth bits.length) true)
/-- Actual stopped source state, with no remaining continuation. -/
def done (bits:List Bool) : C.State Stack Label := ⟨none,none,none,result bits,[]⟩

/-- Reusable physical stage; original metadata can be shared by a larger fixed program. -/
theorem ready (bits:List Bool) :
    Runs program (10*transformExponent bits.length+11+
      loopTime 0 (transformExponent bits.length/2) (odd (transformExponent bits.length)))
      (.inl .ready) (data (MetaOut.result bits) [] [] [] [] [] []) (.inl .halt) (result bits) := by
  let E:=transformExponent bits.length
  have he:(MetaOut.result bits) .exponent=List.replicate E true:=rfl
  have h0:=initialize_axes (MetaOut.result bits)
  have h1:=copy_exponent (MetaOut.result bits) E he [true] [true] []
  have h2:=loop_run (E/2) (odd E) 0 (MetaOut.result bits) []
  rw [exponent_parts] at h2
  simp only [Nat.zero_add,pow_zero] at h2
  have h3:=finish_depth (MetaOut.result bits) E he (List.replicate (2^(E/2)) true)
    (List.replicate (2^(E/2+tailBit (odd E))) true)
  have h:=h0.trans (h1.trans (h2.trans h3))
  rw [second_exponent] at h
  simpa only [result,firstAxis,secondAxis_eq_power,macroDepth,
    show 2+((5*E+4)+(loopTime 0 (E/2) (odd E)+(5*E+5)))=
      10*E+11+loopTime 0 (E/2) (odd E) by omega] using h

/-- Complete original binary-input execution includes actual nested metadata calls and halt. -/
theorem acquire_run (bits:List Bool) :
    C.run program (totalTime bits.length) (initial bits)=some (done bits) := by
  have h:=(metadata_call bits).trans (ready bits)
  obtain ⟨finish,hfinish,hout⟩:=h [] (initial bits) ⟨rfl,rfl,rfl⟩
  have ht:totalTime bits.length=
      (SemiprimeD1StackTransformArithmetic.totalTime bits.length+1+
        (10*transformExponent bits.length+11+
          loopTime 0 (transformExponent bits.length/2) (odd (transformExponent bits.length))))+1:=by
    unfold totalTime;omega
  rw [ht,SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some]
  rcases hout with ⟨hpc,hdata,hframes⟩
  change C.step program finish=some (done bits)
  simp [C.step,SemiprimeD1StackCalls.step,hpc,program,C.execute,SemiprimeD1StackCalls.execute,
    hdata,hframes,done]

/-- Only binary N is supplied at initialization. -/
theorem initial_eq (bits:List Bool) :
    Turing.initList machine bits=SemiprimeD1StackCalls.configuration (initial bits) := by
  have he:initial bits=SemiprimeD1StackCalls.initial (.inl .input) (.inl .start) bits:=by
    dsimp only [initial,SemiprimeD1StackCalls.initial]
    congr 1
    funext k
    cases k with
    | inl k => cases k <;> simp [input,Meta.input]
    | inr k => fin_cases k <;> simp [input]
  rw [he]
  exact (SemiprimeD1StackCalls.initial_correct (.inl .input) (.inr 2) (.inl .start) program bits).symm

/-- Actual finite-machine time, not a retained arithmetic/list report. -/
def acquireInTime (bits:List Bool) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits))) (400000*(bits.length+1)^2) := by
  rw [initial_eq]
  apply SemiprimeD1StackCalls.evalsCorrect (.inl .input) (.inr 2) (.inl .start) program
  exact ⟨⟨totalTime bits.length,acquire_run bits⟩,totalTime_le bits.length⟩
end RiemannGaussian.SemiprimeD1StackAxesExecution
