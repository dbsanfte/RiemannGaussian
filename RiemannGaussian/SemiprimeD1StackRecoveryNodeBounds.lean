/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryNodeExecution
/-! # SAME complete141-role source has fixed own polynomial time from semantic operand bytes
True grid enumeration and W are paid by VALUE. All coefficient words stay
binary; no operand bound comes from a recursive child's elapsed runtime.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryNodeBounds
open SemiprimeD1StackRecoveryNode SemiprimeD1StackRecoveryNodeEncoding
open SemiprimeD1StackRecoveryNodeExecution
namespace R
export SemiprimeD1StackRecoveryGridResource (resource resource_pos)
end R
/-- Constants and degree are fixed before all original inputs and all local coefficients. -/
def polynomial (a M u:ℕ) (t width:List Bool):ℕ:=10^151*(R.resource a M u t width)^30
/-- Actual weights use acquired q/W and semantically bounded inverse/powers/scalar bytes only. -/
theorem weightBound_le (a M u:ℕ) (selected:Fin (2^(a+1))) (t width:List Bool):
    weightBound a M u selected width≤10^80*(R.resource a M u t width)^20:=
  SemiprimeD1StackRecoveryWeightsOriginalResources.grid_clock a M u selected t width
/-- Pure actual two-call accounting is proved before substitution of large native byte specifications. -/
theorem sum_le (n w r:ℕ) (hr:1≤r) (hn:n≤10^150*r^30) (hw:w≤10^80*r^20):
    n+w+3≤10^151*r^30:=by
  have h20:r^20≤r^30:=Nat.pow_le_pow_right hr (by decide:20≤30)
  have h1:1≤r^30:=Nat.one_le_pow _ _ hr
  omega
/-- Both real complete sources, both actual caller/returns, final halt and every byte of cleanup are paid. -/
theorem runBound_le (a M u:ℕ) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val):runBound a M u selected t width≤polynomial a M u t width:=
  sum_le _ _ _ (R.resource_pos a M u t width)
    (SemiprimeD1StackRecoveryNodeInputsBounds.runBound_le a M u selected t width ht)
    (weightBound_le a M u selected t width)
/-- SAME actual Grid-cache ready sum omits Grid and never repeats any acquired array source. -/
theorem readyBound_le (a M u:ℕ) (selected:Fin (2^(a+1))) (t width:List Bool):
    readyBound a M u selected t width≤runBound a M u selected t width:=by
  have h:=SemiprimeD1StackRecoveryNodeInputsBounds.readyBound_le a M u selected t width
  unfold readyBound runBound
  omega
/-- Original FIVE physical words internally acquire every coefficient within one fixed whole source clock. -/
theorem source_run_bounded (a M u:ℕ) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val):
    ∃s≤polynomial a M u t width,SemiprimeD1StackCalls.run program s
      (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)=some (done a M u selected t width):=by
  obtain ⟨s,hs,hr⟩:=source_run a M u selected t width ht
  exact ⟨s,hs.trans (runBound_le a M u selected t width ht),hr⟩
/-- Actual whole Grid cache ready source has the SAME literal program, own clock and exact true halt. -/
theorem ready_run_bounded (a M u:ℕ) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val):
    ∃s≤polynomial a M u t width,SemiprimeD1StackCalls.run program s
      (gridReady a M u selected t width)=some (done a M u selected t width):=by
  obtain ⟨s,hs,hr⟩:=ready_run a M u selected t width ht
  exact ⟨s,hs.trans ((readyBound_le a M u selected t width).trans (runBound_le a M u selected t width ht)),hr⟩
/-- Genuine finite141-role machine executes that SAME proved five-word whole source. -/
noncomputable def machineSource (a M u:ℕ) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val):
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width))
      (some (SemiprimeD1StackCalls.configuration (done a M u selected t width))) (polynomial a M u t width):=by
  apply SemiprimeD1StackCalls.evalsCorrect (node (N.affine (SemiprimeD1StackRecoveryAffine.oldAux .originalA))) output (ctl .start) program
  let h:=source_run_bounded a M u selected t width ht
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackRecoveryNodeBounds
