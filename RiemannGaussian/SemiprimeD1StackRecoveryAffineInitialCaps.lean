/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineWordCaps
import RiemannGaussian.SemiprimeD1StackRecoveryAffineOriginalInput
/-! # Same actual Grid boundary has semantic fitted-register and physical-byte caps
All reused old-store bounds are mathematical byte invariants of the SAME
included producer. No native report clock or elapsed operand bound is used.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineInitialCaps
namespace Q
export SemiprimeD1StackRecoveryGrid (Stack program aux)
end Q
namespace V
export SemiprimeD1StackRecoveryGridView (Words bank)
end V
namespace R
export SemiprimeD1StackRecoveryGridResource (resource cacheWidth dataWidth cache_data width_cache)
end R
namespace C
export SemiprimeD1StackRecoveryGridWordCaps (Registers Data auxiliary_data)
export SemiprimeD1StackRecoveryGridBoundaryCaps (transient_registers transient_data)
end C
/-- All actual final Grid writes and EOF drains retain the same semantic widths and physical word caps. -/
theorem stopped_caps (a M u:Nat) (t width:List Bool):
    C.Registers (SemiprimeD1StackRecoveryGridFinal.result (SemiprimeD1StackRecoveryGridExecution.beforeFinish a M u t width) width)
      (R.cacheWidth a width) ∧
    C.Data (SemiprimeD1StackRecoveryGridFinal.result (SemiprimeD1StackRecoveryGridExecution.beforeFinish a M u t width) width)
      (R.dataWidth a M u t width):=by
  obtain ⟨hr,hd⟩:=SemiprimeD1StackRecoveryGridBounds.finish_caps a M u t width
  have hW:=R.width_cache a width
  have hBL:=R.cache_data a M u t width
  obtain ⟨hr0,hd0⟩:=SemiprimeD1StackRecoveryGridFinalBounds.front_caps _ width _ _ hW hBL hr hd
  obtain ⟨hr1,hd1⟩:=SemiprimeD1StackRecoveryGridFinalBounds.tail_caps _ width _ _ hW hBL hr0 hd0
  change C.Registers (SemiprimeD1StackRecoveryGridFinal.clean
    (SemiprimeD1StackRecoveryGridFinal.argument (SemiprimeD1StackRecoveryGridExecution.beforeFinish a M u t width) width)) _ ∧_
  constructor
  · exact C.transient_registers _ _ hr1
  · apply C.auxiliary_data _ .q [] _ (C.transient_data _ _ hd1)
    exact Nat.zero_le _
/-- Entire actual original104 retained bank inherits those semantic caps, without a source-clock recurrence. -/
theorem original_caps (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val):
    C.Registers (SemiprimeD1StackRecoveryGridEncoding.resultWords a M u selected t width) (R.cacheWidth a width) ∧
    C.Data (SemiprimeD1StackRecoveryGridEncoding.resultWords a M u selected t width) (R.dataWidth a M u t width):=by
  have he:=SemiprimeD1StackRecoveryGridOriginal.result_original a M u selected t width ht
  have h:=stopped_caps a M u t width
  have hd:V.bank (SemiprimeD1StackRecoveryGridFinal.result (SemiprimeD1StackRecoveryGridExecution.beforeFinish a M u t width) width)=
      V.bank (SemiprimeD1StackRecoveryGridEncoding.resultWords a M u selected t width):=he
  constructor
  · intro r b
    have hh:=congrFun hd (SemiprimeD1StackRecoveryGrid.reg r b)
    change (SemiprimeD1StackRecoveryGridFinal.result (SemiprimeD1StackRecoveryGridExecution.beforeFinish a M u t width) width).registers (r,b)=
      (SemiprimeD1StackRecoveryGridEncoding.resultWords a M u selected t width).registers (r,b) at hh
    rw [←hh]
    exact h.1 r b
  · intro slot
    rw [←hd]
    exact h.2 slot
end RiemannGaussian.SemiprimeD1StackRecoveryAffineInitialCaps
