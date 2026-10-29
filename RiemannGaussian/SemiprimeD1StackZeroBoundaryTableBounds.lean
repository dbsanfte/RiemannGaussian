/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackZeroBoundaryTableExecution
/-! # Actual N-only machine time, all-prefix inventory and original boundary tape -/
set_option autoImplicit false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeD1StackZeroBoundaryTableBounds
open SemiprimeD1StackZeroBoundaryTable SemiprimeD1StackZeroBoundaryTableExecution
open SemiprimeBitArithmetic (bitValue)
/-- The old public source really begins with N alone; no cache/template is input. -/
theorem public_input (bits : List Bool) (k : P.Stack) : P.input bits k=
    if k=P.digitStack (SemiprimeD1BinaryPublicAcquisition.Digits.metaStack .input) then bits else [] := by
  have hi:=SemiprimeD1StackCalls.initial_correct
    (P.digitStack (SemiprimeD1BinaryPublicAcquisition.Digits.metaStack .input))
    (P.digitStack (SemiprimeD1BinaryPublicAcquisition.Digits.bankStack SemiprimeD1StackDigitBank.output))
    (P.mainLabel .start) P.program bits
  have he:=hi.trans (SemiprimeD1BinaryPublicAcquisitionExecution.initial_configuration bits).symm
  have hd:=congrArg (fun cfg:SemiprimeD1BinaryPublicAcquisition.machine.Cfg=>cfg.stk (some k)) he
  exact hd.symm
/-- Actual standalone initialization is original binary N ONLY. -/
theorem initial_eq (bits : List Bool) :
    Turing.initList machine bits=SemiprimeD1StackCalls.configuration (initial bits) := by
  have hs:initial bits=SemiprimeD1StackCalls.initial original (.inl .start) bits := by
    unfold initial SemiprimeD1StackCalls.initial
    congr 1
    funext k
    rcases k with k|k
    · simp [store,public_input,original]
    · cases k <;> simp [store,original,SemiprimeD1StackBooleanTree.store]
  rw [hs]
  exact (SemiprimeD1StackCalls.initial_correct original output (.inl .start) program bits).symm
/-- Whole N-only genuine finite-machine certificate, with no table/depth advice. -/
noncomputable def boundaryInTime (bits : List Bool) (hb : bits≠[]) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits))) (timeBound bits) := by
  rw [initial_eq bits]
  apply SemiprimeD1StackCalls.evalsCorrect original output (.inl .start) program
  let h:=source_run bits hb
  let t:=Classical.choose h
  have ht:=Classical.choose_spec h
  exact ⟨⟨t,ht.2⟩,ht.1⟩
/-- The complete actual halt bounds ALL executed prefixes. -/
theorem prefix_fuel_le (bits : List Bool) (hb : bits≠[]) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial bits)=some out) : fuel≤timeBound bits := by
  obtain ⟨time,ht,he⟩:=source_run bits hb
  have hf:fuel≤time := by
    by_contra hn
    have h:fuel=time+(1+(fuel-(time+1))) := by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz:C.run program 1 (done bits)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- ALL32 Boolean data registers and ALL real recursive return cells at EVERY prefix. -/
theorem prefix_cells (bits : List Bool) (hb : bits≠[]) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial bits)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤33*(bits.length+timeBound bits+1) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel bits.length _ out (by
    intro k
    rcases k with k|k
    · change (P.input bits k).length≤bits.length
      rw [public_input]
      split <;> simp
    · cases k <;> exact Nat.zero_le _) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs : (∑k:Stack,(out.data k).length)≤32*(bits.length+fuel) := by
    calc
      _≤∑_k:Stack,(bits.length+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _= _:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le bits hb fuel out hr
  omega
/-- Same complete inventory bound for the ACTUAL compiled finite machine. -/
theorem machine_prefix_cells (bits : List Bool) (hb : bits≠[]) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤33*(bits.length+timeBound bits+1) := by
  have he:=SemiprimeD1StackCalls.run_correct original output (.inl .start) program fuel (initial bits)
  change (C.run program fuel (initial bits)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (initial bits))) at he
  have hh : (C.run program fuel (initial bits)).map SemiprimeD1StackCalls.configuration=some cfg :=
    he.trans ((congrArg (fun start:machine.Cfg=>
      (fun q:Option machine.Cfg=>q.bind machine.step)^[fuel] (some start)) (initial_eq bits).symm).trans hr)
  cases hrun:C.run program fuel (initial bits) with
  | none=>rw [hrun] at hh;cases hh
  | some out=>
    rw [hrun] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells bits hb fuel out hrun
/-- Exact actual binary source/depth arity for original canonical N. -/
theorem original_depth (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) :
    (cached bits).length=SemiprimeMacroParameters.firstAxis (SemiprimeMacroParameters.bitLength (bitValue bits))*
      SemiprimeMacroParameters.secondAxis (SemiprimeMacroParameters.bitLength (bitValue bits))+1 :=
  SemiprimeD1StackPublicZeroOriginal.public_width bits hc
/-- Quadratic original public acquisition PLUS the actual exponential-output
writer, with only constant call/seed/halt overhead. -/
theorem original_time (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) :
    timeBound bits=800000*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^2+
      40*2^(SemiprimeMacroParameters.firstAxis (SemiprimeMacroParameters.bitLength (bitValue bits))*
        SemiprimeMacroParameters.secondAxis (SemiprimeMacroParameters.bitLength (bitValue bits))+1)+4 := by
  rw [timeBound,SemiprimeD1BinaryPublicAcquisitionExecution.timeBound,original_depth bits hc,
    SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc]
/-- Exact original INITIAL boundary tree bytes, acquired from N alone. -/
theorem initial_output (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    (done bits).data output=SemiprimeD1TensorTapeCodec.tape
      (SemiprimeD1BooleanRootTablesOriginal.reference (bitValue bits) hN (.inl .carryInitial)) := by
  change SemiprimeD1BooleanTreeStream.bytes (cached bits).length [true]=_
  rw [original_depth bits hc]
  exact congrArg SemiprimeD1TensorTapeCodec.tape (SemiprimeD1ZeroBoundaryTables.initial_reference bits hc hN)
/-- SAME acquired table is the exact original TERMINAL boundary tensor. -/
theorem terminal_output (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    (done bits).data output=SemiprimeD1TensorTapeCodec.tape
      (SemiprimeD1BooleanRootTablesOriginal.reference (bitValue bits) hN (.inl .carryTerminal)) := by
  change SemiprimeD1BooleanTreeStream.bytes (cached bits).length [true]=_
  rw [original_depth bits hc]
  exact congrArg SemiprimeD1TensorTapeCodec.tape (SemiprimeD1ZeroBoundaryTables.terminal_reference bits hc hN)
/-- All actual public metadata, including every shared depth marker, are restored. -/
theorem retained_public (bits : List Bool) (k : P.Stack) : (done bits).data (.inl k)=context bits k := rfl
end RiemannGaussian.SemiprimeD1StackZeroBoundaryTableBounds
