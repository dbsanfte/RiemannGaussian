/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackDigitCountLoop

/-! # Complete physical cached-record counting
The only input of this internal machine is the actual cached byte vector.
It acquires the reader by a real Copy and counts records by actual parser
calls. The graph frontend will supply the cache from original N acquisition.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackDigitCountExecution
open SemiprimeD1StackDigitCount SemiprimeD1StackDigitCountComponents SemiprimeD1StackDigitCountLoop
open SemiprimeD1StackProcedureFragments (At Runs)
open SemiprimeD1TensorTapeCodec (vectorBits)

/-- Actual bank-only input; no record count or reader is supplied. -/
def initial (bank:List Bool) : C.State Stack Label := ⟨some (.inl .main),none,none,data bank [] [] [] [] [] [],[]⟩
/-- Actual acquired unary count with the original cached bytes retained. -/
def done (words:List (List Bool)) : C.State Stack Label :=
  ⟨none,none,none,data (vectorBits words) [] (List.replicate words.length true) [] [] [] [],[]⟩
/-- Exact complete transition count, including copy and final halt. -/
def totalTime (words:List (List Bool)) : ℕ := 5*(vectorBits words).length+4+loopTime words+1

/-- Reusable actual cache-count stage before final halt, retaining the entire source cache. -/
theorem ready (words:List (List Bool)) :
    Runs program (5*(vectorBits words).length+4+loopTime words) (.inl .main)
      (data (vectorBits words) [] [] [] [] [] []) (.inl .halt)
      (data (vectorBits words) [] (List.replicate words.length true) [] [] [] []) := by
  have h:=(copy_call (vectorBits words)).trans (loop_run words (vectorBits words) [])
  simpa only [List.append_nil] using h

/-- The whole physical scanner acquires the exact count; zero-valued empty fields still count. -/
theorem acquire_run (words:List (List Bool)) :
    C.run program (totalTime words) (initial (vectorBits words))=some (done words) := by
  obtain ⟨finish,hfinish,hout⟩:=ready words [] (initial (vectorBits words)) ⟨rfl,rfl,rfl⟩
  unfold totalTime
  rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some]
  rcases hout with ⟨hpc,hdata,hframes⟩
  change C.step program finish=some (done words)
  simp [C.step,SemiprimeD1StackCalls.step,hpc,program,C.execute,SemiprimeD1StackCalls.execute,hdata,hframes,done]

/-- One actual whole-cache linear transition bound. -/
theorem totalTime_le (words:List (List Bool)) : totalTime words≤11*(vectorBits words).length+5 := by
  have h:=loopTime_le words
  unfold totalTime
  omega

/-- Actual initialization uses only cache bytes, never a count/field-value answer. -/
theorem initial_eq (bank:List Bool) :
    Turing.initList machine bank=SemiprimeD1StackCalls.configuration (initial bank) := by
  have he:initial bank=SemiprimeD1StackCalls.initial Stack.bank (.inl .main) bank:=by
    dsimp only [initial,SemiprimeD1StackCalls.initial]
    congr 1
    funext k
    cases k <;> simp [data]
  rw [he]
  exact (SemiprimeD1StackCalls.initial_correct Stack.bank Stack.count (.inl .main) program bank).symm

/-- Real finite-machine time from an actually acquired well-formed cache, not from its count. -/
def countInTime (words:List (List Bool)) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine (vectorBits words))
      (some (SemiprimeD1StackCalls.configuration (done words))) (11*(vectorBits words).length+5) := by
  rw [initial_eq]
  apply SemiprimeD1StackCalls.evalsCorrect Stack.bank Stack.count (.inl .main) program
  exact ⟨⟨totalTime words,acquire_run words⟩,totalTime_le words⟩
end RiemannGaussian.SemiprimeD1StackDigitCountExecution
