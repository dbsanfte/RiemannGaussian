/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseEncoding
/-! # Complete actual three-input normalized inverse through TRUE halt
This is a prepared physical array/q/W source. The denominator producer and its
literal caller join are separate; no N-only initial-input claim is made here.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseExecution
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseReadBuffers SemiprimeD1StackNormalizedInverseCalls
open SemiprimeD1StackNormalizedInverseAcquisition SemiprimeD1StackNormalizedInverseFinishLoop
open SemiprimeD1StackNormalizedInverseEncoding SemiprimeD1StackNormalizedInverseFinalCleanup
open SemiprimeD1StackNormalizedInverseCleanup (mass)
open SemiprimeD1StackProcedureTrace
/-- Sum of SAME-program bootstrap, actual loop, complete row reversal,54 drains and literal halt. -/
def runBound (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool) : ℕ :=
  acquireBound a width q+finishTime (outputWords a q width).reverse+
    54*(mass (store (beforeCleanup a q width))+1)+1
/-- The actual whole source reaches its real done label with exact old coefficient bytes and all54 private words empty. -/
theorem source_trace (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool) :
    ∃t≤runBound a q width-1,Runs program t (ctl .start) (input (tape a) (unary q) width)
      (ctl .done) (result a q width) := by
  obtain ⟨t0,ht0,h0⟩:=acquire_run a q width
  have h1:=finish_run (ready a q width) (outputWords a q width).reverse [false] rfl rfl rfl rfl
  rw [ready_finish,outputRows_reverse,List.reverse_reverse] at h1
  obtain ⟨t2,ht2,h2⟩:=final_run (store (beforeCleanup a q width))
  rw [clean_before] at h2
  have h:=PTrace.join (PTrace.join h0 h1) h2
  refine ⟨t0+finishTime (outputWords a q width).reverse+t2,?_,h⟩
  simp only [runBound,Nat.add_sub_cancel]
  omega
/-- Actual whole source TRUEhalts and clears both transient flags and all actual return cells. -/
theorem source_run (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool) :
    ∃t≤runBound a q width,SemiprimeD1StackCalls.run program t (initial (tape a) (unary q) width)=some (done a q width) := by
  obtain ⟨t,ht,hr⟩:=source_trace a q width
  obtain ⟨finish,hfinish,hAt⟩:=hr [] (initial (tape a) (unary q) width) ⟨rfl,rfl,rfl⟩
  refine ⟨t+1,?_,?_⟩
  · simp only [runBound,Nat.add_sub_cancel] at ht ⊢
    omega
  · rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some]
    exact halt_run program (ctl .done) rfl (result a q width) [] finish hAt
/-- SAME actual fixed58-role compiled machine, from ONLY the physical typed array/q/W bank. -/
noncomputable def inverseInTime (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial (tape a) (unary q) width))
      (some (SemiprimeD1StackCalls.configuration (done a q width))) (runBound a q width) := by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .denominator) (aux .output) (ctl .start) program
  let t:=Classical.choose (source_run a q width)
  have ht:=Classical.choose_spec (source_run a q width)
  exact ⟨⟨t,ht.2⟩,ht.1⟩
end RiemannGaussian.SemiprimeD1StackNormalizedInverseExecution
