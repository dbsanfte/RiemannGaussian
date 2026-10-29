/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootRecoveryWidthPrimitives
/-! # Both real whole source calls, retaining the complete other bank -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootRecoveryWidthCalls
open SemiprimeD1StackRootRecoveryWidth SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (bitValue)
local notation "ctl"=>Label.local
/-- The actual binary-N source executes once with every actual width-source word retained. -/
theorem root_call (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits)
    (width:W.Stack→List Bool):
    ∃q ≤ SemiprimeD1StackRootPacketPaddingBounds.runBound bits+1,Runs program q (ctl .start)
      (data (R.initial bits).data width) (ctl (.copy .exponent))
      (data (SemiprimeD1StackRootPacketPaddingEncoding.done bits hN).data width):=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackRootPacketPaddingBounds.source_run_bounded bits hc hN
  refine ⟨q+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program rootStack Label.root Sum.inl_injective
    R.program (.local .start) (fun _=>rfl) (ctl .start) (ctl (.copy .exponent)) rfl q
    (R.initial bits) (SemiprimeD1StackRootPacketPaddingEncoding.done bits hN) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
/-- Only the two physically copied acquired metadata words enter the real complete width source. -/
theorem width_call (a M:Nat) (root:R.Stack→List Bool):
    ∃q ≤ SemiprimeD1StackRecoveryWidthBounds.polynomial a M+1,Runs program q (ctl .width)
      (data root (W.initial (List.replicate a true) (List.replicate M true)).data) (ctl .done)
      (data root (SemiprimeD1StackRecoveryWidthEncoding.done a M).data):=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackRecoveryWidthBounds.source_run_bounded a M
  refine ⟨q+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program widthStack Label.width Sum.inr_injective
    W.program .start (fun _=>rfl) (ctl .width) (ctl .done) rfl q
    (W.initial (List.replicate a true) (List.replicate M true)) (SemiprimeD1StackRecoveryWidthEncoding.done a M)
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
end RiemannGaussian.SemiprimeD1StackRootRecoveryWidthCalls
