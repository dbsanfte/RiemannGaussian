/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPacketPaddingPrimitives
/-! # Both real whole sources with all other2139-role words retained -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPacketPaddingCalls
open SemiprimeD1StackRootPacketPadding SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (bitValue)
local notation "ctl" => Label.local
/-- One actual original-input selected-key call, preserving the complete initially supplied padding bank. -/
theorem root_call (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits)
    (padding:Q.Stack→List Bool) :
    ∃t ≤SemiprimeD1StackRootSelectionAcquireBounds.runBound bits+1,Runs program t (ctl .start)
      (data (R.initial bits).data padding) (ctl (.copy .keys))
      (data (SemiprimeD1StackRootSelectionAcquireEncoding.done bits hN).data padding) :=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackRootSelectionAcquireBounds.source_run_bounded bits hc hN
  refine ⟨t+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program rootStack Label.root Sum.inl_injective
    R.program (.local (.copy .number)) (fun _=>rfl) (ctl .start) (ctl (.copy .keys)) rfl t
    (R.initial bits) (SemiprimeD1StackRootSelectionAcquireEncoding.done bits hN) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
/-- One actual frequency+rounding source, reading only its actual copied key/dimension words. -/
theorem padding_call (keys:List (List Bool)) (a:Nat) (root:R.Stack→List Bool) :
    ∃t ≤SemiprimeD1StackSourcePacketPaddingBounds.polynomial keys a+1,Runs program t (ctl .padding)
      (data root (SemiprimeD1StackSourcePacketPaddingEncoding.source keys a).data) (ctl .done)
      (data root (SemiprimeD1StackSourcePacketPaddingEncoding.done keys a).data) :=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackSourcePacketPaddingBounds.source_run_bounded keys a
  refine ⟨t+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program paddingStack Label.padding Sum.inr_injective
    Q.program .start (fun _=>rfl) (ctl .padding) (ctl .done) rfl t
    (SemiprimeD1StackSourcePacketPaddingEncoding.source keys a) (SemiprimeD1StackSourcePacketPaddingEncoding.done keys a)
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
end RiemannGaussian.SemiprimeD1StackRootPacketPaddingCalls
