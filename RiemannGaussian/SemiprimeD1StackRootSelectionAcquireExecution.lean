/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootSelectionAcquireEncoding
/-! # One actual binary-N-only selected-key acquisition trace
All three actual source calls, four physical copies and the true final halt
belong to the same program. No semantic or mixed report clock is transported.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootSelectionAcquireExecution
open SemiprimeD1StackRootSelectionAcquire SemiprimeD1StackRootSelectionAcquireEncoding
open SemiprimeD1StackRootSelectionAcquireInput SemiprimeD1StackRootSelectionAcquireCalls
open SemiprimeD1StackRootSelectionAcquirePrimitives SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (bitValue)
local notation "ctl" => Label.local
attribute [local irreducible] SemiprimeD1IncidenceSearch.run SemiprimeD1IncidenceAcquisition.acquire
/-- Generic acquired-output projection is proved before instantiating an original network or N. -/
theorem data_output (root:R.Stack→List Bool) (parameters:P.Stack→List Bool) (acquisition:Q.Stack→List Bool) :
    data root parameters acquisition output=acquisition
      (Q.keyStack (SemiprimeD1StackSourceSelectedKeys.aux .output)) :=rfl
/-- One whole actual source trace starts with binary N alone and ends after complete selected-key acquisition. -/
theorem source_trace (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits) :
    ∃q,q+1 ≤timeBound bits hN ∧ Runs program q (ctl (.copy .number)) (input bits) (ctl .done) (result bits hN) :=by
  have h0:=number_input_run bits
  obtain ⟨p,hp,h1⟩:=parameters_call bits hc hN (R.initial bits).data (fun _=>[])
  obtain ⟨r,hr,h2⟩:=root_call bits hc hN (parameterDone bits).data (fun _=>[])
  have h3:=acquisition_input_run (rootDone bits hN).data (parameterDone bits).data
  rw [acquisitionReady_original bits hc hN] at h3
  obtain ⟨s,hs,h4⟩:=acquisition_call (net bits hN) (dimension bits) (rootDone bits hN).data (parameterDone bits).data
  have h:=join (join (join (join h0 h1) h2) h3) h4
  refine ⟨_,?_,h⟩
  unfold timeBound
  omega
/-- The identical source executes its genuine halt from its sole actual original binary input. -/
theorem source_run (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits) :
    ∃q ≤timeBound bits hN,SemiprimeD1StackCalls.run program q (initial bits)=some (done bits hN) :=by
  obtain ⟨q,hq,hr⟩:=source_trace bits hc hN
  obtain ⟨out,he,ha⟩:=hr [] (initial bits) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (result bits hN) [] out ha
  refine ⟨q+1,hq,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,he,Option.bind_some]
  exact hh
/-- Every original row/record/index source word is retained literally at the complete halt. -/
theorem root_retained (bits:List Bool) (hN:0 < bitValue bits) (k:R.Stack) :
    (done bits hN).data (rootStack k)=(rootDone bits hN).data k :=rfl
/-- Every acquired original scheduling source word remains physically available. -/
theorem parameters_retained (bits:List Bool) (hN:0 < bitValue bits) (k:P.Stack) :
    (done bits hN).data (parameterStack k)=(parameterDone bits).data k :=rfl
/-- The entire154-role source cache, selected environment, alphabet and output remain physically available. -/
theorem acquisition_retained (bits:List Bool) (hN:0 < bitValue bits) (k:Q.Stack) :
    (done bits hN).data (acquisitionStack k)=(acquisitionDone bits hN).data k :=rfl
/-- Exact output meaning is established for abstract banks/network before original-N instantiation. -/
theorem generic_output (root:R.Stack→List Bool) (parameters:P.Stack→List Bool)
    (network:SemiprimeD1TensorNetwork.Network) (a:Nat) :
    data root parameters (E.done network a).data output=SemiprimeD1TensorTapeCodec.vectorBits
      (SemiprimeD1IncidenceAcquisition.acquire network.leftCount network.rows.length 64 a
        (SemiprimeD1TensorNetwork.arity network.rows) (SemiprimeD1TensorNetwork.owner network.rows)).keys :=by
  rw [data_output]
  exact SemiprimeD1StackSourceSelectionAcquireOriginal.output_original network a
/-- Exact complete original selected-key vector, acquired by the same actual binary-N-only execution. -/
theorem output_original (bits:List Bool) (hN:0 < bitValue bits) :
    (done bits hN).data output=SemiprimeD1TensorTapeCodec.vectorBits
      (SemiprimeD1IncidenceAcquisition.acquire (net bits hN).leftCount (net bits hN).rows.length 64 (dimension bits)
        (SemiprimeD1TensorNetwork.arity (net bits hN).rows) (SemiprimeD1TensorNetwork.owner (net bits hN).rows)).keys :=by
  have h:=generic_output (rootDone bits hN).data (parameterDone bits).data (net bits hN) (dimension bits)
  simpa only [done,result,acquisitionDone] using h
end RiemannGaussian.SemiprimeD1StackRootSelectionAcquireExecution
