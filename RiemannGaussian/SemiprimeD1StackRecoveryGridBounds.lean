/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridFrontClock
import RiemannGaussian.SemiprimeD1StackRecoveryGridLoopClock
import RiemannGaussian.SemiprimeD1StackRecoveryGridFinalBounds
/-! # Whole SAME fixed104-role source with its own paid-VALUE polynomial clock
The actual N=2^(a+1) enumeration and W template are charged by physical VALUE.
The original binary t remains binary. No old report clock is transported.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridBounds
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView
namespace Exec
export SemiprimeD1StackRecoveryGridExecution (beforeFinish runBound source_run done firstWord)
end Exec
namespace R
export SemiprimeD1StackRecoveryGridResource (resource cacheWidth dataWidth resource_pos cache_le width_cache cache_data)
end R
namespace Caps
export SemiprimeD1StackRecoveryGridWordCaps (Registers Data)
end Caps
/-- Actual final arithmetic inputs have semantic fitted/literal cache widths and all104 physical-word caps. -/
theorem finish_caps (a M u:Nat) (t width:List Bool) :
    Caps.Registers (Exec.beforeFinish a M u t width) (R.cacheWidth a width) ∧
    Caps.Data (Exec.beforeFinish a M u t width) (R.dataWidth a M u t width):=by
  have hp:=SemiprimeD1StackRecoveryGridLoopClock.payload_bounded a M u t width
  have hq:(SemiprimeD1StackRecoveryGridLoopPrimitives.zeroWord a).length≤a+2:=by
    change (List.replicate (a+2) false).length≤a+2
    rw [List.length_replicate]
  exact ⟨SemiprimeD1StackRecoveryGridModelBounds.registers_le a M u 0 _ t _ width _ hp,
    SemiprimeD1StackRecoveryGridModelBounds.data_le a M u 0 _ t _ width _ hp (by omega) hq⟩
/-- Six actual final rational operations and every EOF drain have a fixed paid-source polynomial. -/
theorem finish_le (a M u:Nat) (t width:List Bool) :
    SemiprimeD1StackRecoveryGridFinal.runBound (Exec.beforeFinish a M u t width) width≤10^53*(R.resource a M u t width)^8:=by
  let r:=R.resource a M u t width
  let B:=R.cacheWidth a width
  let L:=R.dataWidth a M u t width
  have hR:1≤r:=R.resource_pos a M u t width
  have hB:B≤2*r:=R.cache_le a M u t width
  have hBL:B≤L:=R.cache_data a M u t width
  have hWB:width.length+2≤B:=R.width_cache a width
  obtain ⟨hr,hd⟩:=finish_caps a M u t width
  have hf:=SemiprimeD1StackRecoveryGridFinalBounds.finish_le (Exec.beforeFinish a M u t width) width B L hWB hBL hr hd
  have hs:=SemiprimeD1StackRecoveryGridEnvelope.site_le r B L hR hB (by dsimp [L,R.dataWidth,r];omega)
  have hL:L=10^9*r^3:=rfl
  have h38:r^3≤r^8:=Nat.pow_le_pow_right hR (by decide:3≤8)
  have h68:r^6≤r^8:=Nat.pow_le_pow_right hR (by decide:6≤8)
  have h08:1≤r^8:=Nat.one_le_pow 8 _ hR
  rw [hL] at hf hs
  change _≤10^53*r^8
  norm_num1 at hf hs ⊢
  omega
/-- Fixed coefficients and degree precede every actual original dimension, binary input and template. -/
def polynomial (a M u:Nat) (t width:List Bool) :Nat:=10^60*(R.resource a M u t width)^12
/-- Complete own source clock includes actual acquisition, all rows, all repeated frames, finish, real returns and true halt. -/
theorem runBound_le (a M u:Nat) (t width:List Bool) :Exec.runBound a M u t width≤polynomial a M u t width:=by
  let r:=R.resource a M u t width
  have hR:1≤r:=R.resource_pos a M u t width
  have hf:=SemiprimeD1StackRecoveryGridFrontClock.front_le a M u t width
  have hl:=SemiprimeD1StackRecoveryGridLoopClock.whole_le a M u t width
  dsimp only [SemiprimeD1StackRecoveryGridResource.gridSize] at hl
  have he:=finish_le a M u t width
  change _≤10^54*r^8 at hf
  change _≤10^56*r^9 at hl
  change _≤10^53*r^8 at he
  have h8:r^8≤r^12:=Nat.pow_le_pow_right hR (by decide:8≤12)
  have h9:r^9≤r^12:=Nat.pow_le_pow_right hR (by decide:9≤12)
  have h0:1≤r^12:=Nat.one_le_pow 12 _ hR
  unfold Exec.runBound polynomial
  change _≤10^60*r^12
  norm_num1 at hf hl he ⊢
  omega
/-- SAME actual original-input source closes its fixed polynomial, with no supplied coefficients or advised geometry. -/
theorem source_run_bounded (a M u:Nat) (t width:List Bool) :
    ∃q≤polynomial a M u t width,SemiprimeD1StackCalls.run program q
      (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)=some (Exec.done a M u t width):=by
  obtain ⟨q,hq,hr⟩:=Exec.source_run a M u t width
  exact ⟨q,hq.trans (runBound_le a M u t width),hr⟩
/-- Genuine finite104-role source from the honest five acquired physical words has that same whole polynomial clock. -/
noncomputable def machineGrid (a M u:Nat) (t width:List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width))
      (some (SemiprimeD1StackCalls.configuration (Exec.done a M u t width))) (polynomial a M u t width):=by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .originalA) (aux .slopes) (.local .start) program
  let h:=source_run_bounded a M u t width
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackRecoveryGridBounds
