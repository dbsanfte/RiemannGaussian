/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryPowersLoop
import RiemannGaussian.SemiprimeD1StackRecoveryPowersStages
/-! # Complete four-input cached-power source, actual halt and genuine finite machine -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryPowersExecution
open SemiprimeD1StackRecoveryPowers
open SemiprimeD1StackRecoveryPowersView hiding Stack
open SemiprimeD1StackRecoveryPowersSpec (signed array)
open SemiprimeD1StackRecoveryPowersEncoding SemiprimeD1StackRecoveryPowersLoop SemiprimeD1StackRecoveryPowersStages
open SemiprimeD1StackRecoveryPowersOperationInput SemiprimeD1StackProcedureTrace
open SemiprimeRationalBits (RationalWord)
/-- Whole own source budget: q-copy/literal seed, SAME complete loop, one reversal and actual halt. -/
def timeBound (argument:RationalWord) (width:List Bool):Nat→Nat
  | 0=>10
  | n+1=>5*(n+1)+8+loopBound argument (n+1) width SemiprimeJetBits.oneWord [] n+
      (2*(payload (array width argument (n+1))).length+4)+1
/-- Complete entry-to-before-halt trace acquires every row internally, with original argument/q/W retained. -/
theorem source_trace (argument:RationalWord) (q:Nat) (width:List Bool):
    ∃time≤timeBound argument width q-1,
      Runs program time (.local .start) (input (signed argument) argument.denominator (List.replicate q true) width)
        (.local .done) (result argument q width):=by
  cases q with
  | zero=>
    have h0:=initialize_zero argument width
    have h1:=finish_run argument 0 width []
    have hh:=PTrace.join h0 h1
    refine ⟨9,le_rfl,?_⟩
    exact hh
  | succ n=>
    have h0:=initialize_succ argument n width
    obtain ⟨m,hm,h1⟩:=loop_run argument (n+1) width n SemiprimeJetBits.oneWord []
    have h2:=finish_run argument (n+1) width ((payload (array width argument (n+1))).reverse)
    change Runs program m _ _ _ (bank (stoppedWords argument (n+1) width
      ((payload (array width argument (n+1))).reverse++[]))) at h1
    rw [List.append_nil] at h1
    have hh:=PTrace.join (PTrace.join h0 h1) h2
    refine ⟨5*(n+1)+8+m+(2*(payload (array width argument (n+1))).length+4),?_,?_⟩
    · simp only [timeBound,Nat.add_sub_cancel]
      omega
    · simpa only [List.length_reverse,List.reverse_reverse,←vector_payload,result] using hh
/-- Complete actual source ends at true halt, with flags and real internal returns empty. -/
theorem source_run (argument:RationalWord) (q:Nat) (width:List Bool):
    ∃time≤timeBound argument width q,SemiprimeD1StackCalls.run program time
      (initial (signed argument) argument.denominator (List.replicate q true) width)=some (done argument q width):=by
  obtain ⟨time,ht,hr⟩:=source_trace argument q width
  obtain ⟨finish,hfin,hAt⟩:=hr [] (initial (signed argument) argument.denominator (List.replicate q true) width) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (.local .done) rfl (result argument q width) [] finish hAt
  refine ⟨time+1,?_,?_⟩
  · have hp:0<timeBound argument width q:=by cases q <;> simp only [timeBound] <;> omega
    omega
  · rw [SemiprimeD1StackReturnLink.run_add,hfin,Option.bind_some]
    exact hh
/-- SAME fixed47-role genuine machine, with no count/power/clock/evaluator operand. -/
noncomputable def powersInTime (argument:RationalWord) (q:Nat) (width:List Bool):
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial (signed argument) argument.denominator (List.replicate q true) width))
      (some (SemiprimeD1StackCalls.configuration (done argument q width))) (timeBound argument width q):=by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .argumentSigned) (aux .output) (.local .start) program
  let h:=source_run argument q width
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackRecoveryPowersExecution
