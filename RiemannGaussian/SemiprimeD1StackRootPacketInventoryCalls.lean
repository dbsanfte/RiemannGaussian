/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPacketInventoryPrimitives
/-! # Both actual whole calls, retaining every word of the other bank -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPacketInventoryCalls
open SemiprimeD1StackRootPacketInventory SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (bitValue)
namespace B
export SemiprimeD1StackPacketInventoryBounds (ValidKeys byteBound source_run_keys)
end B
namespace E
export SemiprimeD1StackPacketInventoryEncoding (done alphabet acquire)
end E
local notation "ctl"=>Label.local
/-- The sole actual original-input root call preserves the initially empty/new inventory bank. -/
theorem root_call (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits)
    (inventory:I.Stack→List Bool):
    ∃q ≤ SemiprimeD1StackRootRecoveryWidthBounds.runBound bits+1,Runs program q (ctl .start)
      (data (R.initial bits).data inventory) (ctl (.copy .keys))
      (data (SemiprimeD1StackRootRecoveryWidthEncoding.done bits hN).data inventory):=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackRootRecoveryWidthBounds.source_run_bounded bits hc hN
  refine ⟨q+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program rootStack Label.root Sum.inl_injective
    R.program (.local .start) (fun _=>rfl) (ctl .start) (ctl (.copy .keys)) rfl q
    (R.initial bits) (SemiprimeD1StackRootRecoveryWidthEncoding.done bits hN) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
/-- Real complete Inventory59 receives precisely the copied two-word front door; root frequency/width caches stay foreign. -/
theorem inventory_call (a:Nat) (keys:List (List Bool)) (hv:B.ValidKeys a keys) (root:R.Stack→List Bool):
    ∃q ≤ B.byteBound (SemiprimeD1TensorTapeCodec.vectorBits keys) (E.alphabet a)+1,
      Runs program q (ctl .inventory)
        (data root (I.initial (SemiprimeD1TensorTapeCodec.vectorBits keys) (E.alphabet a)).data) (ctl .done)
        (data root (E.done (SemiprimeD1TensorTapeCodec.vectorBits keys) (E.alphabet a) (E.acquire a keys)).data):=by
  obtain ⟨q,hq,hr⟩:=B.source_run_keys a keys hv
  refine ⟨q+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program inventoryStack Label.inventory Sum.inr_injective
    I.program (.local .start) (fun _=>rfl) (ctl .inventory) (ctl .done) rfl q
    (I.initial (SemiprimeD1TensorTapeCodec.vectorBits keys) (E.alphabet a))
    (E.done (SemiprimeD1TensorTapeCodec.vectorBits keys) (E.alphabet a) (E.acquire a keys))
    _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · exact (hk k rfl).elim
end RiemannGaussian.SemiprimeD1StackRootPacketInventoryCalls
