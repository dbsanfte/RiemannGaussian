/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPacketInventoryStorage
import RiemannGaussian.SemiprimeD1StackRootPacketInventoryMonomial
import RiemannGaussian.SemiprimeD1StackRootPacketInventoryMeaning
/-! # Whole original-binary-input sparse packets and placements, with width retained
One real root acquisition supplies every selected key/catalogue and the width
template. The real complete sparse replay uses its OWN physically acquired OLD
indices and empty maps. No native report clock becomes a machine-time premise.
Mode/recursive child factories, full recovery and public factorer remain open.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPacketInventoryOriginal
open SemiprimeD1StackRootPacketInventory SemiprimeD1StackRootPacketInventoryEncoding
open SemiprimeD1StackRootPacketInventoryExecution SemiprimeD1StackRootPacketInventoryBounds
open SemiprimeD1StackRootPacketInventoryMonomial SemiprimeD1StackRootPacketInventoryMeaning
open SemiprimeBitArithmetic (bitValue)
/-- Original padding-then-replay specification, never a runtime input or executing getter. -/
def originalInventory (bits:List Bool) (hN:0 < bitValue bits):=
  Native.acquire (N.net bits hN).leftCount (N.net bits hN).rows.length 64 (A.dimension bits)
    (SemiprimeD1TensorNetwork.arity (N.net bits hN).rows) (SemiprimeD1TensorNetwork.owner (N.net bits hN).rows)
/-- Generic original placement bytes precede any large original-N/network instantiation. -/
theorem generic_output (root:R.Stack→List Bool) (net:SemiprimeD1TensorNetwork.Network) (a:Nat):
    data root (SemiprimeD1StackPacketInventoryEncoding.done
      (SemiprimeD1TensorTapeCodec.vectorBits (IOld.originalKeys net.leftCount net.rows.length a
        (SemiprimeD1TensorNetwork.arity net.rows) (SemiprimeD1TensorNetwork.owner net.rows)))
      (SemiprimeD1StackPacketInventoryEncoding.alphabet a)
      (IE.acquire a (IOld.originalKeys net.leftCount net.rows.length a
        (SemiprimeD1TensorNetwork.arity net.rows) (SemiprimeD1TensorNetwork.owner net.rows)))).data output=
      SemiprimeD1TensorTapeCodec.vectorBits
        ((Native.acquire net.leftCount net.rows.length 64 a
          (SemiprimeD1TensorNetwork.arity net.rows) (SemiprimeD1TensorNetwork.owner net.rows)).placements.map IE.placementBytes):=by
  change SemiprimeD1TensorTapeCodec.vectorBits
    ((IE.acquire a (IOld.originalKeys net.leftCount net.rows.length a
      (SemiprimeD1TensorNetwork.arity net.rows) (SemiprimeD1TensorNetwork.owner net.rows))).placements.map IE.placementBytes)=_
  rw [generic_placements]
/-- Exact chronological six-field placement tape from original binary N alone. -/
theorem output_original (bits:List Bool) (hN:0 < bitValue bits):
    (done bits hN).data output=SemiprimeD1TensorTapeCodec.vectorBits
      ((originalInventory bits hN).placements.map IE.placementBytes):=by
  have h:=generic_output (rootDone bits hN).data (N.net bits hN) (A.dimension bits)
  simpa only [done,result,inventoryDone,A.keys,A.dimension,
    SemiprimeD1StackRootPacketPaddingEncoding.keys,IOld.originalKeys,originalInventory] using h
/-- Exact actual packet discovery vector, including original first-discovery order and every raw byte. -/
theorem packets_original (bits:List Bool) (hN:0 < bitValue bits):
    (done bits hN).data packets=SemiprimeD1TensorTapeCodec.vectorBits (originalInventory bits hN).state.packets:=by
  have h:=generic_packets (rootDone bits hN).data (N.net bits hN) (A.dimension bits)
  simpa only [done,result,inventoryDone,A.keys,A.dimension,
    SemiprimeD1StackRootPacketPaddingEncoding.keys,IOld.originalKeys,originalInventory] using h
/-- All sparse map reads, compact edge words and packet order match the original same-family replay. -/
theorem state_original (bits:List Bool) (hN:0 < bitValue bits):
    IM.Rel (IE.acquire (A.dimension bits) (A.keys bits hN)) (originalInventory bits hN).state:=by
  have h:=generic_state (N.net bits hN) (A.dimension bits)
  simpa only [A.keys,A.dimension,SemiprimeD1StackRootPacketPaddingEncoding.keys,IOld.originalKeys,originalInventory] using h
/-- SAME whole actual source, exact original placements AND packets, starting with binary N only. -/
theorem source_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits):
    ∃q ≤ runBound bits,SemiprimeD1StackCalls.run program q (initial bits)=some (done bits hN) ∧
      (done bits hN).data output=SemiprimeD1TensorTapeCodec.vectorBits
        ((originalInventory bits hN).placements.map IE.placementBytes) ∧
      (done bits hN).data packets=SemiprimeD1TensorTapeCodec.vectorBits (originalInventory bits hN).state.packets:=by
  obtain ⟨q,hq,hr⟩:=source_run_bounded bits hc hN
  exact ⟨q,hq,hr,output_original bits hN,packets_original bits hN⟩
/-- Fixed coefficient and degree precede ALL canonical positive binary inputs, for this SAME whole source. -/
theorem uniform_original:∃coef degree:Nat,∀(bits:List Bool)
    (_hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits),
    ∃q ≤ coef*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^degree*
      2^(114000*SemiprimeMacroParameters.scopeBound (SemiprimeMacroParameters.bitLength (bitValue bits))),
      SemiprimeD1StackCalls.run program q (initial bits)=some (done bits hN) ∧
      (done bits hN).data output=SemiprimeD1TensorTapeCodec.vectorBits
        ((originalInventory bits hN).placements.map IE.placementBytes) ∧
      (done bits hN).data packets=SemiprimeD1TensorTapeCodec.vectorBits (originalInventory bits hN).state.packets:=by
  obtain ⟨coef,degree,hbound⟩:=runBound_monomial
  refine ⟨coef,degree,?_⟩
  intro bits hc hN
  obtain ⟨q,hq,hr,ho,hp⟩:=source_original bits hc hN
  have hw:=SemiprimeD1StackRootScheduleOriginal.width_original bits hc
  have hb:runBound bits ≤ coef*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^degree*
      2^(114000*SemiprimeMacroParameters.scopeBound (SemiprimeMacroParameters.bitLength (bitValue bits))):=by
    simpa only [Arity.arityCapacity,hw] using hbound bits
  exact ⟨q,hq.trans hb,hr,ho,hp⟩
/-- One fixed whole-family bound pays ALL2270 actual data roles and every genuine return. -/
theorem cells_cap_monomial:∃coef degree:Nat,∀bits:List Bool,
    2271*(bits.length+runBound bits) ≤ coef*(bits.length+1)^degree*2^(114000*Arity.arityCapacity bits):=by
  obtain ⟨coef,degree,hbound⟩:=runBound_monomial
  refine ⟨2271*(coef+1),degree+1,?_⟩
  intro bits
  let H:Nat:=(bits.length+1)^(degree+1)
  let E:Nat:=2^(114000*Arity.arityCapacity bits)
  have hpos:1 ≤ bits.length+1:=by omega
  have he:1 ≤ E:=Nat.pow_pos (by decide)
  have hd:(bits.length+1)^degree ≤ H:=Nat.pow_le_pow_right hpos (by omega)
  have hb0:bits.length+1 ≤ H:=by
    simpa only [pow_one] using Nat.pow_le_pow_right hpos (by omega:1 ≤ degree+1)
  have hpay:bits.length ≤ bits.length*E:=by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left bits.length he
  have hb:bits.length ≤ H*E:=hpay.trans (Nat.mul_le_mul_right E (by omega))
  have ht:runBound bits ≤ coef*H*E:=
    (hbound bits).trans (Nat.mul_le_mul_right E (Nat.mul_le_mul_left coef hd))
  change 2271*(bits.length+runBound bits) ≤ (2271*(coef+1))*H*E
  nlinarith only [hb,ht]
/-- Every actual compiled prefix starts at genuine Turing.initList of original binary N alone. -/
theorem uniform_prefix_cells:∃coef degree:Nat,∀(bits:List Bool)
    (_hc:SemiprimeSourceCompactBits.Compact bits) (_hN:0 < bitValue bits) (fuel:Nat) (cfg:machine.Cfg),
    (fun c=>c.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg→
      (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
        coef*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^degree*
          2^(114000*SemiprimeMacroParameters.scopeBound (SemiprimeMacroParameters.bitLength (bitValue bits))):=by
  obtain ⟨coef,degree,hbound⟩:=cells_cap_monomial
  refine ⟨coef,degree,?_⟩
  intro bits hc hN fuel cfg hr
  have h:=(SemiprimeD1StackRootPacketInventoryStorage.machine_prefix_cells bits hc hN fuel cfg hr).trans (hbound bits)
  have hw:=SemiprimeD1StackRootScheduleOriginal.width_original bits hc
  simpa only [Arity.arityCapacity,hw] using h
end RiemannGaussian.SemiprimeD1StackRootPacketInventoryOriginal
