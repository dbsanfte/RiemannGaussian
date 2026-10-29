/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPacketPaddingEncoding
/-! # Whole actual original-input selected-key/frequency/padding execution
The actual stopped source provides both consumer operands through real paid
copies. Both actual source calls and the final halt use this same program.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPacketPaddingExecution
open SemiprimeD1StackRootPacketPadding SemiprimeD1StackRootPacketPaddingEncoding
open SemiprimeD1StackRootPacketPaddingInput SemiprimeD1StackRootPacketPaddingCalls
open SemiprimeD1StackRootPacketPaddingPrimitives SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (bitValue)
local notation "ctl" => Label.local
attribute [local irreducible] SemiprimeD1IncidenceAcquisition.acquire SemiprimeD1PacketPadding.acquire
/-- SAME whole source starts with binary N and acquires the actual entire padding bank. -/
theorem source_trace (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits) :
    ∃t,t+1 ≤timeBound bits hN ∧ Runs program t (ctl .start) (input bits) (ctl .done) (result bits hN) :=by
  obtain ⟨r,hr,h0⟩:=root_call bits hc hN (fun _=>[])
  have h1:=padding_input_run (rootDone bits hN).data (root_scratch bits hN)
  rw [paddingReady_original bits hc hN] at h1
  obtain ⟨p,hp,h2⟩:=padding_call (keys bits hN) (A.dimension bits) (rootDone bits hN).data
  have h:=join (join h0 h1) h2
  refine ⟨_,?_,h⟩
  unfold timeBound
  omega
/-- The same literal binary-input program actually halts after both full sources and all actual handoffs. -/
theorem source_run (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits) :
    ∃t ≤timeBound bits hN,SemiprimeD1StackCalls.run program t (initial bits)=some (done bits hN) :=by
  obtain ⟨t,ht,h⟩:=source_trace bits hc hN
  obtain ⟨out,he,ha⟩:=h [] (initial bits) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (result bits hN) [] out ha
  refine ⟨t+1,ht,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,he,Option.bind_some]
  exact hh
/-- Every original2114 source/cache/selection word survives the real frequency/rounding acquisition. -/
theorem root_retained (bits:List Bool) (hN:0 < bitValue bits) (k:R.Stack) :
    (done bits hN).data (rootStack k)=(rootDone bits hN).data k :=rfl
/-- The entire actual25-role frequency/rounding bank has its exact physical stopped projection. -/
theorem padding_retained (bits:List Bool) (hN:0 < bitValue bits) (k:Q.Stack) :
    (done bits hN).data (paddingStack k)=(paddingDone bits hN).data k :=rfl
/-- Entire original padding meaning is proved for abstract network/source before instantiating N. -/
theorem generic_output (root:R.Stack→List Bool) (network:SemiprimeD1TensorNetwork.Network) (a:Nat) :
    data root (E.done (SemiprimeD1IncidenceAcquisition.acquire network.leftCount network.rows.length 64 a
      (SemiprimeD1TensorNetwork.arity network.rows) (SemiprimeD1TensorNetwork.owner network.rows)).keys a).data output=
        (SemiprimeD1PacketPadding.acquire network.leftCount network.rows.length 64 a
          (SemiprimeD1TensorNetwork.arity network.rows) (SemiprimeD1TensorNetwork.owner network.rows)).padding :=by
  rw [show output=paddingStack (Q.aux .padding) from rfl,SemiprimeD1StackRootPacketPaddingView.padding_word]
  exact SemiprimeD1StackSourcePacketPaddingOriginal.packet_output_original network.leftCount network.rows.length 64 a
    (SemiprimeD1TensorNetwork.arity network.rows) (SemiprimeD1TensorNetwork.owner network.rows)
/-- Complete actual binary-N-only output is the EXACT original compact packet-padding word. -/
theorem output_original (bits:List Bool) (hN:0 < bitValue bits) :
    (done bits hN).data output=
      (SemiprimeD1PacketPadding.acquire (A.net bits hN).leftCount (A.net bits hN).rows.length 64 (A.dimension bits)
        (SemiprimeD1TensorNetwork.arity (A.net bits hN).rows) (SemiprimeD1TensorNetwork.owner (A.net bits hN).rows)).padding :=by
  have h:=generic_output (rootDone bits hN).data (A.net bits hN) (A.dimension bits)
  simpa only [done,result,paddingDone,keys] using h
end RiemannGaussian.SemiprimeD1StackRootPacketPaddingExecution
