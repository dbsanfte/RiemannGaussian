/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackTransformComparison
import RiemannGaussian.SemiprimeD1StackTransformGrowth
import RiemannGaussian.SemiprimeD1StackTransformRadix
import RiemannGaussian.SemiprimeD1StackTransformArithmetic

/-! # Original-input actual least-dyadic transform and radix execution
The mathematical target exponent supplies no runtime answer: every earlier
state takes the actual failed comparison, and the original least stop takes
the actual success branch. R, square, exponent and radix are physically built.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackTransformExecution
open SemiprimeD1StackTransform SemiprimeD1StackTransformComponents
open SemiprimeD1StackTransformComparison SemiprimeD1StackTransformGrowth
open SemiprimeD1StackTransformRadix SemiprimeD1StackTransformArithmetic
open SemiprimeD1StackProcedureFragments (At Runs)
open SemiprimeMacroParameters

/-- Proof-side counter view of the actually visited kth growth state. -/
def counters (bits:List Bool) (k:ℕ) : Stack→List Bool :=
  data bits (List.replicate (16*bits.length) true) (List.replicate ((2:ℕ)^k) true)
    (List.replicate ((4:ℕ)^k) true) (List.replicate k true) [] [] [] []

/-- Proof-side output specification; powers are not called by the machine. -/
def result (bits:List Bool) : Stack→List Bool :=
  data bits (List.replicate (16*bits.length) true) (List.replicate (transformLength bits.length) true)
    (List.replicate ((4:ℕ)^transformExponent bits.length) true)
    (List.replicate (transformExponent bits.length) true) [] [] [] (List.replicate (radixBits bits.length) true)

/-- Every round is actually executed; its guard is derived from the original least-stop parameter. -/
theorem loop_run (bits:List Bool) (k n:ℕ) (hk:k+n=transformExponent bits.length) :
    Runs program (loopTime bits.length k n) (.inl .copySquare) (counters bits k)
      (.inl .radixStart) (counters bits (transformExponent bits.length)) := by
  induction n generalizing k with
  | zero =>
    have he:k=transformExponent bits.length:=by omega
    subst k
    exact compare_success _ _ (at_stop bits.length) bits
      (List.replicate ((2:ℕ)^transformExponent bits.length) true)
      (List.replicate (transformExponent bits.length) true) []
  | succ n ih =>
    have hlt:k<transformExponent bits.length:=by omega
    have h0:=compare_failure ((4:ℕ)^k) (16*bits.length) (before_stop bits.length k hlt) bits
      (List.replicate ((2:ℕ)^k) true) (List.replicate k true) []
    have h1:=grow ((2:ℕ)^k) ((4:ℕ)^k) bits (List.replicate (16*bits.length) true)
      (List.replicate k true) []
    have hp2:2*(2:ℕ)^k=(2:ℕ)^(k+1):=by rw [pow_succ']
    have hp4:4*(4:ℕ)^k=(4:ℕ)^(k+1):=by rw [pow_succ']
    rw [hp2,hp4,←List.replicate_succ] at h1
    have hnext:(k+1)+n=transformExponent bits.length:=by omega
    have h2:=ih (k+1) hnext
    have h:=h0.trans (h1.trans h2)
    simpa only [loopTime,failCost,counters,Nat.add_assoc] using h

/-- Actual terminal radius quartering matches the original radix parameter, including zero width. -/
theorem radix_finish (bits:List Bool) :
    Runs program (radixTime bits.length) (.inl .radixStart)
      (counters bits (transformExponent bits.length)) (.inl .halt) (result bits) := by
  by_cases hz:bits.length=0
  · have h:=radix_zero bits (List.replicate (16*bits.length) true)
      (List.replicate ((4:ℕ)^transformExponent bits.length) true)
      (List.replicate (transformExponent bits.length) true)
    simpa [counters,result,radixTime,hz,exponent_zero,radixBits,transformLength] using h
  · have hpos:0<bits.length:=Nat.pos_of_ne_zero hz
    have hr:((2:ℕ)^transformExponent bits.length)=4*radixBits bits.length:=transform_eq_four_radixBits hpos
    have h:=radix_run (radixBits bits.length) bits (List.replicate (16*bits.length) true)
      (List.replicate ((4:ℕ)^transformExponent bits.length) true)
      (List.replicate (transformExponent bits.length) true)
    rw [←hr] at h
    simpa only [radixTime,hz,ite_false,counters,result,transformLength] using h

/-- Actual final source configuration; every comparison/scaling work stack and return frame is empty. -/
def done (bits:List Bool) : C.State Stack Label := ⟨none,none,none,result bits,[]⟩

/-- Whole actual source execution from original binary input, with no parameter/value supplier. -/
theorem acquire_run (bits:List Bool) :
    C.run program (totalTime bits.length) (initial bits)=some (done bits) := by
  have h0:=SemiprimeD1StackTransformSetup.prepare bits
  change Runs program (85*bits.length+71) (.inl .start) (input bits) (.inl .copySquare) (counters bits 0) at h0
  have h1:=loop_run bits 0 (transformExponent bits.length) (by omega)
  have h2:=radix_finish bits
  have h:=h0.trans (h1.trans h2)
  have hs:At (.inl .start) (input bits) [] (initial bits):=⟨rfl,rfl,rfl⟩
  obtain ⟨finish,hfinish,hout⟩:=h [] (initial bits) hs
  unfold totalTime
  rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some]
  rcases hout with ⟨hpc,hdata,hframes⟩
  change C.step program finish=some (done bits)
  simp [C.step,SemiprimeD1StackCalls.step,hpc,program,C.execute,SemiprimeD1StackCalls.execute,
    hdata,hframes,done]

/-- The whole machine starts from Turing.initList N alone, with no prepared width or counter. -/
theorem initial_eq (bits:List Bool) :
    Turing.initList machine bits=SemiprimeD1StackCalls.configuration (initial bits) := by
  have he:initial bits=SemiprimeD1StackCalls.initial Stack.input (.inl .start) bits:=by
    dsimp only [initial,SemiprimeD1StackCalls.initial]
    congr 1
    funext k
    cases k <;> simp [input]
  rw [he]
  exact (SemiprimeD1StackCalls.initial_correct Stack.input Stack.radix (.inl .start) program bits).symm

/-- Original-input real machine time is one fixed polynomial in physical input width. -/
def acquireInTime (bits:List Bool) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits))) (120000*(bits.length+1)^2) := by
  rw [initial_eq]
  apply SemiprimeD1StackCalls.evalsCorrect Stack.input Stack.radix (.inl .start) program
  exact ⟨⟨totalTime bits.length,acquire_run bits⟩,totalTime_le bits.length⟩
end RiemannGaussian.SemiprimeD1StackTransformExecution
