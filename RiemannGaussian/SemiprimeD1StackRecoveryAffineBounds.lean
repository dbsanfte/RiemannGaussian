/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineLoopClock
import RiemannGaussian.SemiprimeD1StackRecoveryAffineRetainedBounds
/-! # Whole SAME112-role affine acquisition has its own fixed paid-VALUE polynomial clock
All true grid and materialized template VALUES are paid. Numerical t and
rational coefficients remain binary. No old/native report clock is transported.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineBounds
open SemiprimeD1StackRecoveryAffine
namespace R
export SemiprimeD1StackRecoveryGridResource (resource resource_pos)
end R
namespace E
export SemiprimeD1StackRecoveryAffineEncoding (done)
end E
namespace Exec
export SemiprimeD1StackRecoveryAffineExecution (timeBound source_run)
end Exec
/-- Constants and degree precede every original metadata/index/template input and every native array. -/
def polynomial (a M u:Nat) (t width:List Bool):Nat:=10^75*(R.resource a M u t width)^14
/-- Actual whole Grid call and physically acquired true-q prefix have their SAME source clock. -/
theorem entry_le (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val):
    SemiprimeD1StackRecoveryAffineSource.entryBound a M u selected t width≤ 10^61*(R.resource a M u t width)^12:=by
  let r:=R.resource a M u t width
  have hr:1≤ r:=R.resource_pos a M u t width
  have h:=SemiprimeD1StackRecoveryAffineRetainedBounds.source_le a M u selected t width ht
  change _≤10^16*r^3 at h
  have h3:r^3≤ r^12:=Nat.pow_le_pow_right hr (by decide:3≤12)
  have h0:1≤ r^12:=Nat.one_le_pow _ _ hr
  unfold SemiprimeD1StackRecoveryAffineSource.entryBound SemiprimeD1StackRecoveryGridBounds.polynomial
  change _≤10^61*r^12
  dsimp only [r] at h h3 h0 ⊢
  omega
/-- One actual preserving original-tape copy, row reversal and literal seed pay every acquired slope byte. -/
theorem slopes_le (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool):
    SemiprimeD1StackRecoveryAffineSlopes.runBound (SemiprimeD1StackRecoveryAffineOriginalInput.slopes a M u selected width)≤
      10^12*(R.resource a M u t width)^3:=by
  let r:=R.resource a M u t width
  have hr:1≤ r:=R.resource_pos a M u t width
  have h:=SemiprimeD1StackRecoveryAffineSlopesBounds.source_le
    (SemiprimeD1StackRecoveryAffineOriginalInput.slopes a M u selected width)
  have hb:=SemiprimeD1StackRecoveryAffineResource.slopes_bytes a M u selected t width
  change _≤10^9*r^3 at hb
  have h1:1≤ r^3:=Nat.one_le_pow _ _ hr
  change _≤10^12*r^3
  omega
/-- Whole own budget includes the actual original Grid, true q, every array term, all physical I/O, cleanup, real returns and halt. -/
theorem timeBound_le (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val):Exec.timeBound a M u selected t width≤ polynomial a M u t width:=by
  let r:=R.resource a M u t width
  have hr:1≤ r:=R.resource_pos a M u t width
  have he:=entry_le a M u selected t width ht
  have hs:=slopes_le a M u selected t width
  have hl:=SemiprimeD1StackRecoveryAffineLoopClock.whole_le a M u selected t width ht
  change _≤10^61*r^12 at he
  change _≤10^12*r^3 at hs
  change _≤10^60*r^10 at hl
  have h12:r^12≤ r^14:=Nat.pow_le_pow_right hr (by decide:12≤14)
  have h3:r^3≤ r^14:=Nat.pow_le_pow_right hr (by decide:3≤14)
  have h10:r^10≤ r^14:=Nat.pow_le_pow_right hr (by decide:10≤14)
  have h0:1≤ r^14:=Nat.one_le_pow _ _ hr
  unfold Exec.timeBound polynomial
  change _≤10^75*r^14
  omega
/-- SAME actual fixed program has a whole fixed polynomial source bound from ONLY its five physical words. -/
theorem source_run_bounded (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val):
    ∃s≤ polynomial a M u t width,SemiprimeD1StackCalls.run program s
      (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)=some (E.done a M u selected t width):=by
  obtain ⟨s,hs,hr⟩:=Exec.source_run a M u selected t width ht
  exact ⟨s,hs.trans (timeBound_le a M u selected t width ht),hr⟩
/-- Genuine compiled112-role affine source uses the SAME actual five-word initial state and its own whole polynomial clock. -/
noncomputable def machineAffine (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val):
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width))
      (some (SemiprimeD1StackCalls.configuration (E.done a M u selected t width))) (polynomial a M u t width):=by
  apply SemiprimeD1StackCalls.evalsCorrect (oldAux .originalA) (aux .array) (.local .start) program
  let h:=source_run_bounded a M u selected t width ht
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackRecoveryAffineBounds
