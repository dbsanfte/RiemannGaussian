/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketModeAcquireMonomial
import RiemannGaussian.SemiprimeD1OriginalModeAcquisition
/-! # Exact original mode bytes after physical packet-count/tile-count acquisition
This component's honest inputs remain the actual packet tape, phase-order
markers and actual WIDTH. Their producers and the literal original-N caller
join remain upstream; no native producer/report clock is transported here.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketModeAcquireOriginal
open SemiprimeD1StackPacketModeAcquire SemiprimeD1StackPacketModeAcquireEncoding
open SemiprimeD1StackPacketModeAcquireExecution SemiprimeD1StackPacketModeAcquireBounds
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace Up
export SemiprimeD1OriginalModeAcquisition (acquire)
end Up
/-- The actual output is the complete original acquired-mode vector, including original tuple order. -/
theorem output_acquireModes (packets:List (List Bool)) (i precision:Nat):
    (done packets i precision).data output=vectorBits
      ((SemiprimeD1ModeCatalog.acquireModes packets.length (2^(i+1)) (precision-1)).values.map
        SemiprimeD1StackWeightedModeView.vector):=by
  rw [SemiprimeD1ModeCatalog.acquireModes_values]
  exact output_original packets i precision
/-- Exact original byte identity for the full original family, using the actual original packets and actual working precision. -/
theorem output_original_family (n F r a u i p:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n):
    (done (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets i
      (Up.acquire n F r a u i p arity owner).precision).data output=
      vectorBits ((Up.acquire n F r a u i p arity owner).modes.values.map
        SemiprimeD1StackWeightedModeView.vector):=by
  exact output_acquireModes _ _ _
/-- SAME actual source execution for every original instance; its three physical input tapes are explicit. -/
theorem source_original_family (n F r a u i p:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n):
    let packets:=(SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets
    let precision:=(Up.acquire n F r a u i p arity owner).precision
    ∃q ≤ runBound packets i precision,
      SemiprimeD1StackCalls.run program q (source packets i precision)=some (done packets i precision) ∧
      (done packets i precision).data output=vectorBits
        ((Up.acquire n F r a u i p arity owner).modes.values.map SemiprimeD1StackWeightedModeView.vector):=by
  dsimp only
  obtain ⟨q,hq,hr⟩:=source_run_bounded
    (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets i
    (Up.acquire n F r a u i p arity owner).precision
  exact ⟨q,hq,hr,output_original_family n F r a u i p arity owner⟩
end RiemannGaussian.SemiprimeD1StackPacketModeAcquireOriginal
