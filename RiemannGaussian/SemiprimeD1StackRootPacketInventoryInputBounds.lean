/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPacketInventoryEncoding
/-! # Actual retained source words pay both copies and the complete real inventory
Both input byte lengths follow the SAME actual original-input producer trace.
No native key/catalogue/report size or supplied resource is transported.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPacketInventoryInputBounds
open SemiprimeD1StackRootPacketInventory SemiprimeD1StackRootPacketInventoryEncoding
open SemiprimeD1StackRootPacketInventoryInput SemiprimeD1StackRootPacketInventoryCalls
open SemiprimeBitArithmetic (bitValue)
/-- Sole binary input bytes plus the SAME real producer's paid complete clock. -/
def envelope (bits:List Bool):Nat:=bits.length+SemiprimeD1StackRootRecoveryWidthBounds.runBound bits+1
/-- Every actual stopped producer word is bounded by its own actual executed trace. -/
theorem root_word_bound (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits) (k:R.Stack):
    ((rootDone bits hN).data k).length ≤ envelope bits:=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackRootRecoveryWidthBounds.source_run_bounded bits hc hN
  have h:=SemiprimeD1StackReturnLink.run_data_bound R.program q bits.length _ _
    (SemiprimeD1StackRootRecoveryWidthStorage.initial_length bits) hr k
  change ((rootDone bits hN).data k).length ≤ bits.length+q at h
  unfold envelope
  omega
/-- Both consumer input lengths are physically paid, not estimated by an external key-count oracle. -/
theorem input_bytes (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits):
    (SemiprimeD1TensorTapeCodec.vectorBits (A.keys bits hN)).length ≤ envelope bits ∧
      (E.alphabet (A.dimension bits)).length ≤ envelope bits:=by
  have hk:=root_word_bound bits hc hN Source.keysRole
  have ha:=root_word_bound bits hc hN Source.catalogueRole
  dsimp only [rootDone] at hk ha
  rw [SemiprimeD1StackRootPacketInventorySources.keys_acquired bits hN] at hk
  rw [SemiprimeD1StackRootPacketInventorySources.catalogue_acquired bits hN] at ha
  exact ⟨hk,ha⟩
/-- The actual source envelope pays each real metadata byte and every actual call/return. -/
theorem copy_time_bound (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits):
    inventoryCopyTime (rootDone bits hN).data ≤ 18*envelope bits:=by
  have hk:=root_word_bound bits hc hN Source.keysRole
  have ha:=root_word_bound bits hc hN Source.catalogueRole
  have hp:1 ≤ envelope bits:=by unfold envelope;omega
  unfold inventoryCopyTime
  omega
/-- SAME real59-role source cost is bounded from its actual two source-produced words. -/
theorem inventory_clock_bound (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits):
    B.byteBound (SemiprimeD1TensorTapeCodec.vectorBits (A.keys bits hN)) (E.alphabet (A.dimension bits)) ≤
      1000000000000*3^4*(envelope bits)^4:=by
  obtain ⟨hk,ha⟩:=input_bytes bits hc hN
  have hp:1 ≤ envelope bits:=by unfold envelope;omega
  have hs:(SemiprimeD1TensorTapeCodec.vectorBits (A.keys bits hN)).length+
      (E.alphabet (A.dimension bits)).length+1 ≤ 3*envelope bits:=by omega
  have h:=Nat.mul_le_mul_left 1000000000000 (Nat.pow_le_pow_left hs 4)
  simpa only [B.byteBound,mul_pow,Nat.mul_assoc] using h
end RiemannGaussian.SemiprimeD1StackRootPacketInventoryInputBounds
