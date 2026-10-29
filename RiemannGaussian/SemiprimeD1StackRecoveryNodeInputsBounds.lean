/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsResource
/-! # SAME140-role whole and actual-cache-ready fixed polynomial clock
The resource pays true grid size and W by VALUE. No native/report clock enters.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsBounds
open SemiprimeD1StackRecoveryNodeInputs SemiprimeD1StackRecoveryNodeInputsEncoding
open SemiprimeD1StackRecoveryNodeInputsExecution SemiprimeD1StackRecoveryNodeInputsResource
/-- Fixed coefficient/degree precede all original phase words and all acquired arrays. -/
def polynomial (a M u : ℕ) (t width : List Bool) : ℕ :=10^150*(R.resource a M u t width)^30
/-- Abstract arithmetic is checked before substituting large acquired-word expressions. -/
theorem inverse_scale (s r : ℕ) (h : s≤10^10*r^3) :10^42*s^10≤10^142*r^30 := by
  have hm:=Nat.mul_le_mul_left (10^42) (Nat.pow_le_pow_left h 10)
  rw [mul_pow,←pow_mul] at hm
  norm_num1 at hm ⊢
  convert hm using 1
  ring
/-- Abstract powers scaling avoids reducing any original Grid report. -/
theorem powers_scale (s r : ℕ) (h : s≤10*r) :10^40*s^10≤10^50*r^10 := by
  have hm:=Nat.mul_le_mul_left (10^40) (Nat.pow_le_pow_left h 10)
  rw [mul_pow] at hm
  norm_num1 at hm ⊢
  convert hm using 1
  ring
/-- The real inverse is charged from actual fitted affine bytes and actually acquired q. -/
theorem inverse_le (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool) :
    SemiprimeD1StackNormalizedInverseBounds.polynomial (E.array a M u selected width) (E.retained a M u selected) width≤
      10^142*(R.resource a M u t width)^30 :=
  inverse_scale _ _ (inverse_size a M u selected t width)
/-- The whole real powers call is charged from actual retained Grid argument/q/W fields. -/
theorem powers_le (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool)
    (ht : SemiprimeBitArithmetic.bitValue t=selected.val) :
    SemiprimeD1StackRecoveryPowersExecution.timeBound (argument a M u selected width) width (E.retained a M u selected)≤
      10^50*(R.resource a M u t width)^10 :=
  (SemiprimeD1StackRecoveryPowersBounds.timeBound_le _ _ _).trans (powers_scale _ _ (powers_size a M u selected t width ht))
/-- The exact three actual calls/returns and final halt fit one fixed polynomial. -/
theorem runBound_le (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool)
    (ht : SemiprimeBitArithmetic.bitValue t=selected.val) :runBound a M u selected t width≤polynomial a M u t width := by
  have ha:=SemiprimeD1StackRecoveryAffineBounds.timeBound_le a M u selected t width ht
  have hi:=inverse_le a M u selected t width
  have hp:=powers_le a M u selected t width ht
  have hr:=R.resource_pos a M u t width
  have h14:(R.resource a M u t width)^14≤(R.resource a M u t width)^30:=Nat.pow_le_pow_right hr (by decide:14≤30)
  have h10:(R.resource a M u t width)^10≤(R.resource a M u t width)^30:=Nat.pow_le_pow_right hr (by decide:10≤30)
  have h0:1≤(R.resource a M u t width)^30:=Nat.one_le_pow _ _ hr
  unfold runBound tailBound polynomial SemiprimeD1StackRecoveryAffineBounds.polynomial at *
  omega
/-- SAME program ready entry omits Grid replay and has its own exact remaining-call sum. -/
theorem readyBound_le (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool) :
    readyBound a M u selected t width≤runBound a M u selected t width := by
  have h:=SemiprimeD1StackRecoveryNodeInputsAffineReady.timeBound_le a M u selected t width
  unfold readyBound runBound
  omega
/-- Whole actual five-word source terminates with both arrays and all old112 fields retained. -/
theorem source_run_bounded (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool)
    (ht : SemiprimeBitArithmetic.bitValue t=selected.val) :
    ∃s≤polynomial a M u t width,SemiprimeD1StackCalls.run program s
      (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)=some (done a M u selected t width) := by
  obtain ⟨s,hs,hr⟩:=source_run a M u selected t width ht
  exact ⟨s,hs.trans (runBound_le a M u selected t width ht),hr⟩
/-- Actual already acquired Grid104 cache enters the SAME source with no affine/q/inverse/power advice. -/
theorem ready_run_bounded (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool)
    (ht : SemiprimeBitArithmetic.bitValue t=selected.val) :
    ∃s≤polynomial a M u t width,SemiprimeD1StackCalls.run program s
      (gridReady a M u selected t width)=some (done a M u selected t width) := by
  obtain ⟨s,hs,hr⟩:=ready_run a M u selected t width ht
  exact ⟨s,hs.trans ((readyBound_le a M u selected t width).trans (runBound_le a M u selected t width ht)),hr⟩
/-- Genuine compiled finite140-role source follows that SAME actual source clock. -/
noncomputable def machineSource (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool)
    (ht : SemiprimeBitArithmetic.bitValue t=selected.val) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width))
      (some (SemiprimeD1StackCalls.configuration (done a M u selected t width))) (polynomial a M u t width) := by
  apply SemiprimeD1StackCalls.evalsCorrect (affine (A.oldAux .originalA)) inverseOutput (ctl .start) program
  let h:=source_run_bounded a M u selected t width ht
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsBounds
