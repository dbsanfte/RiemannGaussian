/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionMetadataStages
/-! # Whole guarded original metadata source and genuine finite-machine halt -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionMetadataExecution
open SemiprimeD1StackPhaseWorkingPrecisionMetadata SemiprimeD1StackPhaseWorkingPrecisionMetadataPrimitives
open SemiprimeD1StackPhaseWorkingPrecisionMetadataArithmetic SemiprimeD1StackProcedureTrace
/-- Actual accepted/rejected metadata; rejection leaves EVERY new output empty. -/
def resultCounts (a u M : Nat) (t : List Bool) : Counts :=
  if accepted a u t then SemiprimeD1StackPhaseWorkingPrecisionMetadataStages.completed a u M t else empty
/-- Exact physical acquired guard plus retained M/binaryp and actual bounded outputs. -/
def result (a u M : Nat) (t p : List Bool) : Stack→List Bool :=context a u M t p (resultCounts a u M t)
/-- Actual halt clears both flags and the source's internal real-return frames. -/
def done (a u M : Nat) (t p : List Bool) : C.State Stack Label :=⟨none,none,none,result a u M t p,[]⟩
/-- Own fixed polynomial includes ALL original physical metadata/index/precision bytes. -/
def runBound (a u M : Nat) (t p : List Bool) : Nat :=1000000*(M+a+u+t.length+p.length+1)^2
/-- The actual acquired verdict is peeked physically; false branches directly to halt. -/
theorem branch_run (a u M : Nat) (t p : List Bool) :
    Runs program 1 .branch (context a u M t p empty)
      (if accepted a u t then .numerator 0 else .done) (context a u M t p empty) :=by
  apply one_base program .branch _ (.peek (guardStack (G.aux .output)) .done .done (.numerator 0)) _ _ rfl
  · change some (SemiprimeD1StackBytecode.choose Label.done Label.done (Label.numerator 0)
      ([accepted a u t].head?))=some _
    cases accepted a u t <;> rfl
  · rfl
/-- Rejected guard executes one actual peek and stops before EVERY division/product entry. -/
theorem rejected_after_guard (a u M : Nat) (t p : List Bool) (h : accepted a u t=false) :
    Runs program 1 .branch (context a u M t p empty) .done (context a u M t p empty) :=by
  have hh:=branch_run a u M t p
  rw [h] at hh
  exact hh
/-- Whole original-only trace executes guarded height/product/count acquisition exactly once. -/
theorem source_trace (a u M : Nat) (t p : List Bool) :
    ∃q,q+1≤ runBound a u M t p ∧ Runs program q .start (input a u M t p) .done (result a u M t p) :=by
  obtain ⟨g,hg,h0⟩:=guard_call a u M t p
  have h1:=branch_run a u M t p
  let I:=M+a+u+t.length+p.length+1
  have hI:1≤ I:=by dsimp [I];omega
  have hsq:I≤ I^2:=by nlinarith
  have hbig:M+a+u+1≤ I:=by dsimp [I];omega
  have hs:(M+a+u+1)^2≤ I^2:=Nat.pow_le_pow_left hbig 2
  have hg':g≤10000*I+1:=by dsimp [I];omega
  cases hacc:accepted a u t with
  | false=>
    rw [hacc] at h1
    have hh:=join h0 h1
    refine ⟨g+1,?_,?_⟩
    · change g+1+1≤1000000*I^2
      omega
    · simpa only [result,resultCounts,hacc,Bool.false_eq_true,ite_false] using hh
  | true=>
    rw [hacc] at h1
    have hbounds:=accepted_bounds a u t hacc
    obtain ⟨b,hb,h2⟩:=SemiprimeD1StackPhaseWorkingPrecisionMetadataHeight.source_run a u M t p
      (accepted_positive a u t hacc)
    obtain ⟨c,hc,h3⟩:=SemiprimeD1StackPhaseWorkingPrecisionMetadataStages.source_run a u M t p hbounds.1 hbounds.2
    have hh:=join (join (join h0 h1) h2) h3
    refine ⟨_,?_,by simpa only [result,resultCounts,hacc,ite_true] using hh⟩
    have hb':b≤1000*I:=by dsimp [I];omega
    have hc':c≤1000*I^2:=by omega
    change _≤1000000*I^2
    omega
/-- Complete actual halt on one fixed finite source for all original operands. -/
theorem source_run (a u M : Nat) (t p : List Bool) :
    ∃q≤ runBound a u M t p,SemiprimeD1StackCalls.run program q (initial a u M t p)=some (done a u M t p) :=by
  obtain ⟨q,hq,hr⟩:=source_trace a u M t p
  obtain ⟨finish,hf,hAt⟩:=hr [] (initial a u M t p) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl (result a u M t p) [] finish hAt
  exact ⟨q+1,hq,by rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some];exact hh⟩
/-- Genuine finite Boolean-stack certificate from ONLY original a/u/M/binaryt/binaryp. -/
noncomputable def metadataInTime (a u M : Nat) (t p : List Bool) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (initial a u M t p))
      (some (SemiprimeD1StackCalls.configuration (done a u M t p))) (runBound a u M t p) :=by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .edges) (aux .q) .start program
  let h:=source_run a u M t p
  let q:=Classical.choose h
  have hq:=Classical.choose_spec h
  exact ⟨⟨q,hq.2⟩,hq.1⟩
end RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionMetadataExecution
