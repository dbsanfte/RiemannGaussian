/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPacketInventoryEncoding
/-! # Whole actual binary-input shared-root and sparse-inventory execution -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPacketInventoryExecution
open SemiprimeD1StackRootPacketInventory SemiprimeD1StackRootPacketInventoryEncoding
open SemiprimeD1StackRootPacketInventoryInput SemiprimeD1StackRootPacketInventoryCalls
open SemiprimeD1StackRootPacketInventoryPrimitives SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (bitValue)
local notation "ctl"=>Label.local
/-- ONE real root, both acquired-word copies and the whole real59-role source form this SAME original-input trace. -/
theorem source_trace (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits):
    ∃q,q+1 ≤ timeBound bits hN ∧ Runs program q (ctl .start) (input bits) (ctl .done) (result bits hN):=by
  obtain ⟨r,hr,h0⟩:=root_call bits hc hN (fun _=>[])
  have h1:=inventory_input_run (rootDone bits hN).data (root_scratch bits hN)
  rw [inventoryReady_original bits hN] at h1
  obtain ⟨i,hi,h2⟩:=inventory_call (A.dimension bits) (A.keys bits hN) (keys_valid bits hN) (rootDone bits hN).data
  have h:=join (join h0 h1) h2
  refine ⟨_,?_,h⟩
  unfold timeBound
  omega
/-- Actual true halt from canonical positive binary N alone, with no supplied row/count/class/packet/state. -/
theorem source_run (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits):
    ∃q ≤ timeBound bits hN,SemiprimeD1StackCalls.run program q (initial bits)=some (done bits hN):=by
  obtain ⟨q,hq,hr⟩:=source_trace bits hc hN
  obtain ⟨out,he,ha⟩:=hr [] (initial bits) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (result bits hN) [] out ha
  refine ⟨q+1,hq,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,he,Option.bind_some]
  exact hh
/-- Every earlier root/selection/frequency/padding/width cache is literally retained. -/
theorem root_retained (bits:List Bool) (hN:0 < bitValue bits) (k:R.Stack):
    (done bits hN).data (rootStack k)=(rootDone bits hN).data k:=rfl
/-- Every actual inventory map/history/packet/edge/output/shadow role is retained exactly. -/
theorem inventory_retained (bits:List Bool) (hN:0 < bitValue bits) (k:I.Stack):
    (done bits hN).data (inventoryStack k)=(inventoryDone bits hN).data k:=rfl
/-- Exact original root width template survives the entire real sparse replay. -/
theorem template_retained (bits:List Bool) (hN:0 < bitValue bits):
    (done bits hN).data template=List.replicate
      (SemiprimeD1RecoveryNodeBits.width (SemiprimeD1StackRecoveryWidthOriginal.originalA bits)
        (SemiprimeD1StackRecoveryWidthOriginal.originalM bits)) false:=
  SemiprimeD1StackRootRecoveryWidthExecution.output_original bits hN
end RiemannGaussian.SemiprimeD1StackRootPacketInventoryExecution
