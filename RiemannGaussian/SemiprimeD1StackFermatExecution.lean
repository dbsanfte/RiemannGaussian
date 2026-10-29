/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFermatStages
import RiemannGaussian.SemiprimeD1StackFermatWords

/-! # Original binary-input acquisition of both Fermat constant words
The fixed program executes the original metadata machine and literal word
construction. Powers below specify its result; they are not machine opcodes.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackFermatExecution
open SemiprimeD1StackFermatConstants SemiprimeD1StackFermatComponents SemiprimeD1StackFermatStages
open SemiprimeD1StackProcedureFragments (At Runs)
open SemiprimeMacroParameters
namespace MetaOut
export SemiprimeD1StackTransformExecution (result)
end MetaOut

/-- Proof-side original-input output specification. -/
def result (bits:List Bool) : Stack→List Bool :=
  data (MetaOut.result bits) [] [] [] (Words.modulusWord (transformLength bits.length))
    (Words.normalizerWord (transformLength bits.length) (transformExponent bits.length))
/-- Actual terminal source configuration. -/
def done (bits:List Bool) : C.State Stack Label := ⟨none,none,none,result bits,[]⟩
/-- Exact instruction count, including original metadata and the final halt. -/
def totalTime (n:ℕ) : ℕ := SemiprimeD1StackTransformArithmetic.totalTime n+
  14*transformLength n+6*transformExponent n+18

/-- Both constants are built from the actually retained metadata counters. -/
theorem ready (bits:List Bool) :
    Runs program (14*transformLength bits.length+6*transformExponent bits.length+16)
      (.inl .modStart) (data (MetaOut.result bits) [] [] [] [] []) (.inl .halt) (result bits) := by
  let E:=transformExponent bits.length
  let R:=transformLength bits.length
  have hRE:E+1≤R:=by
    change E+1≤2^E
    have h:E<2^E:=Nat.lt_two_pow_self
    omega
  have hR:0<R:=by dsimp [R,transformLength]; positivity
  have hr:(MetaOut.result bits) .radius=List.replicate R true:=rfl
  have he:(MetaOut.result bits) .exponent=List.replicate E true:=rfl
  have h1:=modulus_run (MetaOut.result bits) (R-1) (by simpa only [Nat.sub_add_cancel hR] using hr)
  have heq:E+(R-E-1)+1=R:=by omega
  have h2:=normalizer_run (MetaOut.result bits) E (R-E-1) (by simpa only [heq] using hr) he
    (Words.modulusWord R)
  rw [heq] at h2
  rw [Nat.sub_add_cancel hR] at h1
  have h:=h1.trans h2
  simpa only [result,show (7*R+6)+(7*R+6*E+10)=14*R+6*E+16 by omega] using h

/-- Complete executed acquisition from N alone, including real nested calls and final halt. -/
theorem acquire_run (bits:List Bool) :
    C.run program (totalTime bits.length) (initial bits)=some (done bits) := by
  have h:=(metadata_call bits).trans (ready bits)
  obtain ⟨finish,hfinish,hout⟩:=h [] (initial bits) ⟨rfl,rfl,rfl⟩
  have ht:totalTime bits.length=
      (SemiprimeD1StackTransformArithmetic.totalTime bits.length+1+
        (14*transformLength bits.length+6*transformExponent bits.length+16))+1:=by
    unfold totalTime;omega
  rw [ht,SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some]
  rcases hout with ⟨hpc,hdata,hframes⟩
  change C.step program finish=some (done bits)
  simp [C.step,SemiprimeD1StackCalls.step,hpc,program,C.execute,SemiprimeD1StackCalls.execute,
    hdata,hframes,done]

/-- No parameter or constant supplier is present at initialization. -/
theorem initial_eq (bits:List Bool) :
    Turing.initList machine bits=SemiprimeD1StackCalls.configuration (initial bits) := by
  have he:initial bits=SemiprimeD1StackCalls.initial (.inl .input) (.inl .start) bits:=by
    dsimp only [initial,SemiprimeD1StackCalls.initial]
    congr 1
    funext k
    cases k with
    | inl k => cases k <;> simp [input,Meta.input]
    | inr bit => cases bit <;> simp [input]
  rw [he]
  exact (SemiprimeD1StackCalls.initial_correct (.inl .input) (.inr true) (.inl .start) program bits).symm

/-- The complete actual acquisition is polynomial in physical input width. -/
theorem totalTime_le (n:ℕ) : totalTime n≤150000*(n+1)^2 := by
  have hm:=SemiprimeD1StackTransformArithmetic.totalTime_le n
  have he:=SemiprimeD1StackTransformArithmetic.exponent_bound n
  have hr:=SemiprimeD1StackTransformArithmetic.prefix_powers n (transformExponent n) (le_refl _)
  change 2^transformExponent n≤64*n+1 ∧ _ at hr
  unfold totalTime transformLength
  nlinarith [hr.1]

/-- Real fixed finite-machine execution from Turing.initList of the binary input alone. -/
def acquireInTime (bits:List Bool) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits))) (150000*(bits.length+1)^2) := by
  rw [initial_eq]
  apply SemiprimeD1StackCalls.evalsCorrect (.inl .input) (.inr true) (.inl .start) program
  exact ⟨⟨totalTime bits.length,acquire_run bits⟩,totalTime_le bits.length⟩
end RiemannGaussian.SemiprimeD1StackFermatExecution
