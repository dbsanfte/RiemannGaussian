/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BinaryDigitAcquisitionComponents

/-! # Whole original-binary-input metadata and digit acquisition trace
The original binary input is the only initially populated stack. Every metadata
constructor, inter-stage copy, block call, frame, cleanup and return executes in
this one fixed program. Derived caches remain live for the later graph caller.
-/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1BinaryDigitAcquisitionExecution
open SemiprimeD1BinaryDigitAcquisition SemiprimeD1BinaryDigitAcquisitionComponents
open SemiprimeD1StackProcedureTrace

/-- Mathematical view of the ACTUALLY executed whole-stage final data. -/
def result (bits : List Bool) : Stack→List Bool :=
  store (SemiprimeD1StackTransformExecution.result bits)
    (SemiprimeD1StackDigitBank.store bits [] (radix bits) [] []
      (SemiprimeD1StackDigitBankExecution.result bits (radix bits))) []

/-- The complete real nested bank trace executes with the acquired operands,
preserving all metadata and the original input; no operands are caller advice. -/
theorem bank_call (bits : List Bool) (hb : bits≠[]) :
    ∃t ≤ SemiprimeD1StackDigitBankExecution.timeBound bits (radix bits),
      Runs program (t+1) (mainLabel .bankCall) (afterRadixCopy bits)
        (mainLabel .done) (result bits) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackDigitBankExecution.source_run bits (radix bits) (radix_nonempty bits hb)
  refine ⟨t,ht,?_⟩
  have hinj : Function.Injective bankStack := by
    intro i j h
    exact Sum.inl_injective (Sum.inr_injective h)
  apply SemiprimeD1StackProcedureCallsTrace.included_call program bankStack bankLabel hinj
    Bank.program (SemiprimeD1StackDigitBank.control .start) (fun _=>rfl)
    (mainLabel .bankCall) (mainLabel .done) rfl t
    (⟨some (SemiprimeD1StackDigitBank.control .start),none,none,
      SemiprimeD1StackDigitBank.store bits [] (radix bits) [] [] [],[]⟩:C.State Bank.Stack Bank.Label)
    (⟨none,none,none,SemiprimeD1StackDigitBank.store bits [] (radix bits) [] []
      (SemiprimeD1StackDigitBankExecution.result bits (radix bits)),[]⟩:C.State Bank.Stack Bank.Label)
    (afterRadixCopy bits) (result bits)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · exact False.elim (hk k rfl)
        · rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · exact False.elim (hk k rfl)
        · rfl

/-- One fixed whole-stage budget in ORIGINAL binary input length. -/
def timeBound (bits : List Bool) : ℕ := 150000*(bits.length+1)^2

/-- Complete original-input source trace; no metadata/width/digit/value/count
supplier appears in its input or in the executing program. -/
theorem source_run (bits : List Bool) (hb : bits≠[]) :
    ∃time ≤ timeBound bits,C.run program time (initial bits)=
      some (⟨none,none,none,result bits,[]⟩:C.State Stack Label) := by
  have h0:=metadata_call bits
  have h1:=input_copy bits
  have h2:=radix_copy bits
  obtain ⟨t,ht,h3⟩:=bank_call bits hb
  have h01:=runs_trans program _ _ _ _ _ _ _ _ h0 h1
  have h012:=runs_trans program _ _ _ _ _ _ _ _ h01 h2
  have h0123:=runs_trans program _ _ _ _ _ _ _ _ h012 h3
  obtain ⟨finish,hfinish,hout⟩:=h0123 [] (initial bits) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (mainLabel .done) rfl (result bits) [] finish hout
  refine ⟨(SemiprimeD1StackTransformArithmetic.totalTime bits.length+1)+(5*bits.length+4)+
    (5*(radix bits).length+4)+(t+1)+1,?_,?_⟩
  · have hn : 0 < bits.length := List.length_pos_iff.mpr hb
    have hm:=SemiprimeD1StackTransformArithmetic.totalTime_le bits.length
    have hB:=SemiprimeD1StackDigitBankBounds.original_width bits.length hn (radix bits) (radix_length bits)
    have hd:=SemiprimeD1StackDigitBankBounds.original_time bits.length hn bits (radix bits) rfl (radix_length bits)
    have ht':=ht.trans hd
    unfold timeBound
    nlinarith [Nat.zero_le (bits.length^2)]
  · rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hh]

/-- Its sole initial source input is EXACTLY the genuine finite-machine binary input. -/
theorem initial_configuration (bits : List Bool) :
    SemiprimeD1StackCalls.configuration (initial bits)=Turing.initList machine bits := by
  have hs : initial bits=SemiprimeD1StackCalls.initial (metaStack .input) (mainLabel .start) bits := by
    unfold initial SemiprimeD1BinaryDigitAcquisition.input store SemiprimeD1StackCalls.initial
    congr 1
    funext k
    rcases k with k|k
    · cases k <;> rfl
    · rcases k with k|k <;> rfl
  rw [hs]
  exact SemiprimeD1StackCalls.initial_correct (metaStack .input) (bankStack Bank.output) (mainLabel .start) program bits

/-- Proof-side actual trace certificate. Only its proved elapsed-length witness
uses choice; the executed finite instruction table is fully computable. -/
noncomputable def sourceAcquire (bits : List Bool) (hb : bits≠[]) :
    StateTransition.EvalsToInTime (C.step program) (initial bits)
      (some (⟨none,none,none,result bits,[]⟩:C.State Stack Label)) (timeBound bits) := by
  let h:=source_run bits hb
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩

/-- ONE fixed finite machine starts from binary N alone and physically acquires
the full transform/radix metadata and EVERY original radix digit, retaining N. -/
noncomputable def acquireInTime (bits : List Bool) (hb : bits≠[]) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (⟨none,none,none,result bits,[]⟩:C.State Stack Label)))
      (timeBound bits) := by
  have hh:=SemiprimeD1StackCalls.evalsCorrect (metaStack .input) (bankStack Bank.output) (mainLabel .start)
    program _ _ _ (sourceAcquire bits hb)
  change StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (initial bits))
    (some (SemiprimeD1StackCalls.configuration (⟨none,none,none,result bits,[]⟩:C.State Stack Label))) (timeBound bits) at hh
  exact Eq.mp (congrArg (fun start : machine.Cfg=>StateTransition.EvalsToInTime machine.step start
    (some (SemiprimeD1StackCalls.configuration (⟨none,none,none,result bits,[]⟩:C.State Stack Label))) (timeBound bits))
    (initial_configuration bits)) hh

end RiemannGaussian.SemiprimeD1BinaryDigitAcquisitionExecution
