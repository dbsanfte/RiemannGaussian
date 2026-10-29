/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWidthExecution
/-! # Own fixed polynomial in a+M+2^(a+1)+1, paying N and W by VALUE -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWidthBounds
open SemiprimeD1StackRecoveryWidth SemiprimeD1StackRecoveryWidthEncoding
open SemiprimeD1StackRecoveryWidthSetup SemiprimeD1StackRecoveryWidthLoop
open SemiprimeD1StackRecoveryWidthFinish SemiprimeD1StackRecoveryWidthExecution
open SemiprimeD1StackUnaryDivmod (unary)
/-- Every actual intermediate doubling is paid at its literal current grid VALUE, with no supplied N operand. -/
theorem powerTime_le (remaining current cap:Nat) (hp:2^remaining*current≤ cap) :
    powerTime remaining current≤(remaining+1)*(7*cap+7):=by
  induction remaining generalizing current with
  | zero=>simp only [powerTime];omega
  | succ remaining ih=>
    have hchild:2^remaining*(2*current)≤ cap:=by
      convert hp using 1
      rw [pow_succ]
      ring
    have hi:=ih (2*current) hchild
    have hone:1≤2^(remaining+1):=Nat.one_le_pow _ _ (by decide:1≤2)
    have hcurrent:current≤ cap:=by
      have hm:=Nat.mul_le_mul_right current hone
      simp only [Nat.one_mul] at hm
      exact hm.trans hp
    simp only [powerTime]
    nlinarith only [hi,hcurrent]
/-- All original unary metadata and the actual retained N value belong to the resource, which is always positive. -/
theorem envelope_parts (a M:Nat) :1≤ inputEnvelope a M ∧ a+1≤ inputEnvelope a M ∧ M≤ inputEnvelope a M ∧
    gridSize a≤ inputEnvelope a M:=by
  unfold inputEnvelope V.envelope
  omega
/-- Physically copied a markers and every growing N-word doubling have a fixed quadratic VALUE bound. -/
theorem setupTime_le (a M:Nat) :setupTime a≤100*(inputEnvelope a M)^2:=by
  have ⟨hR,ha,_,hN⟩:=envelope_parts a M
  have hp:2^a*2≤ gridSize a:=by rw [gridSize,pow_succ]
  have ht:=powerTime_le a 2 (gridSize a) hp
  have hm:(a+1)*(7*gridSize a+7)≤ inputEnvelope a M*(7*inputEnvelope a M+7):=
    Nat.mul_le_mul ha (by omega)
  unfold setupTime
  nlinarith only [hR,ha,ht,hm]
/-- Exact coefficient and degree are fixed before every acquired metadata pair. -/
def polynomial (a M:Nat) :Nat:=100000000000000000000*(inputEnvelope a M)^12
/-- The SAME complete source pays all64 gate words/copies/products, actual W output cells, all old registers and halt. -/
theorem runBound_le (a M:Nat) :runBound a M≤ polynomial a M:=by
  let R:=inputEnvelope a M
  have hR:1≤ R:=(envelope_parts a M).1
  have hsetup:=setupTime_le a M
  have hW:=SemiprimeD1StackRecoveryWidthPolynomial.value_bound 63 a M (gridSize a)
  have h5:1≤ R^5:=Nat.one_le_pow _ _ hR
  have hH:wordCap a M (gridSize a)+1≤2001*R^5:=by
    change 2000*R^5+1≤2001*R^5
    omega
  have hsquare:=Nat.pow_le_pow_left hH 2
  have he:(2001*R^5)^2=4004001*R^10:=by ring
  rw [he] at hsquare
  have hgate:64*gateCap a M (gridSize a)≤25625606400*R^10:=by
    unfold gateCap
    nlinarith only [hsquare]
  have hfinish:finishBound a M (gridSize a)≤132065*R^5:=by
    change V.value 63 a M (gridSize a)≤2000*R^5 at hW
    unfold finishBound wordCap
    change 2*V.value 63 a M (gridSize a)+1+64*(2000*R^5+1)≤132065*R^5
    omega
  have h2:R^2≤ R^12:=Nat.pow_le_pow_right hR (by decide:2≤12)
  have h512:R^5≤ R^12:=Nat.pow_le_pow_right hR (by decide:5≤12)
  have h10:R^10≤ R^12:=Nat.pow_le_pow_right hR (by decide:10≤12)
  have h12:1≤ R^12:=Nat.one_le_pow _ _ hR
  change runBound a M≤100000000000000000000*R^12
  unfold runBound
  change setupTime a≤100*R^2 at hsetup
  nlinarith only [hsetup,hgate,hfinish,h2,h512,h10,h12]
/-- Exact authoritative FALSE template is acquired from the original two unary words within the own fixed polynomial. -/
theorem source_run_bounded (a M:Nat) :
    ∃q≤ polynomial a M,SemiprimeD1StackCalls.run program q (initial (unary a) (unary M))=some (done a M):=by
  obtain ⟨q,hq,hr⟩:=source_run a M
  exact ⟨q,hq.trans (runBound_le a M),hr⟩
/-- SAME actual fixed finite72-role machine, with paired acquired unary metadata and all internally acquired values paid. -/
noncomputable def machineSource (a M:Nat) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (initial (unary a) (unary M)))
      (some (SemiprimeD1StackCalls.configuration (done a M))) (polynomial a M):=by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .a) (aux .output) .start program
  let h:=source_run_bounded a M
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackRecoveryWidthBounds
