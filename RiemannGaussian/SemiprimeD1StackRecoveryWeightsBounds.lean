/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsOuterBounds
/-! # Whole actual complete weight-array source, one fixed physical-bit polynomial before all inputs -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeightsBounds
open SemiprimeD1StackRecoveryWeights SemiprimeD1StackRecoveryWeightsView
open SemiprimeD1StackRecoveryWeightsExecution SemiprimeD1StackRecoveryWeightsWidths
open SemiprimeRationalBits (RationalWord)
/-- Fixed coefficient/degree precede every array, scalar, count and template. All six input bytes are paid. -/
def polynomial (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width:List Bool):Nat:=
  10^50*(inputSize inverse powers scalar q width)^10
/-- Actual original marker/width lengths pay the complete output, including W0 and empty arrays. -/
theorem output_budget (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width:List Bool):
    1+q*(4*width.length+5) ≤ 14*(inputSize inverse powers scalar q width)^2:=by
  have hs:=input_caps inverse powers scalar q width
  let s:=inputSize inverse powers scalar q width
  have hp:q*width.length ≤ s*s:=Nat.mul_le_mul hs.2.2.2.2.1 hs.2.2.2.2.2
  have h1:1 ≤ s^2:=Nat.one_le_pow _ _ hs.1
  have hs2:s ≤ s^2:=Nat.le_pow (by decide:0<2)
  change _ ≤ 14*s^2
  nlinarith only [hp,h1,hs2,hs.2.2.2.2.1]
/-- Pure polynomial accounting does not reduce any rational payload or substitute an old native clock. -/
private theorem source_arithmetic (s q loop mass:Nat) (hs:1 ≤ s) (hq:q ≤ s)
    (hl:loop ≤ (q+1)*(10^41*s^7)) (hm:mass ≤ 300*s^2):
    5*q+5+loop+53*(mass+1)+1 ≤ 10^50*s^10:=by
  have hs10:s ≤ s^10:=Nat.le_pow (by decide:0<10)
  have hs210:s^2 ≤ s^10:=Nat.pow_le_pow_right hs (by decide:2≤10)
  have hs710:s^7 ≤ s^10:=Nat.pow_le_pow_right hs (by decide:7≤10)
  have hs810:s^8 ≤ s^10:=Nat.pow_le_pow_right hs (by decide:8≤10)
  have h110:1 ≤ s^10:=Nat.one_le_pow _ _ hs
  have hp:(q+1)*s^7 ≤ 2*s^8:=by
    have h:=Nat.mul_le_mul_right (s^7) (show q+1 ≤ 2*s by omega)
    simpa only [pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h
  nlinarith only [hl,hm,hq,hs10,hs210,hs710,hs810,h110,hp]
/-- SAME complete actual entry/halt budget is fixed polynomial in the six ORIGINAL physical inputs. -/
theorem timeBound_le (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width:List Bool):
    timeBound inverse powers scalar q width ≤ polynomial inverse powers scalar q width:=by
  let s:=inputSize inverse powers scalar q width
  have hs:=input_caps inverse powers scalar q width
  have hb:=output_budget inverse powers scalar q width
  change 1+q*(4*width.length+5) ≤ 14*s^2 at hb
  have hl:=SemiprimeD1StackRecoveryWeightsOuterBounds.outer_bound inverse powers scalar q width q [false] s
    hs.1 hs.2.2.2.2.2 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1 le_rfl hb
  have hout:(SemiprimeD1StackNormalizedInverse.tape (Spec.array width q scalar inverse powers)).length ≤ 14*s^2:=by
    have h:=array_tape_bytes width q scalar inverse powers
    omega
  have hbank:=SemiprimeD1StackRecoveryWeightsBankBounds.outer_bound inverse powers scalar q width 0
    (SemiprimeD1StackNormalizedInverse.tape (Spec.array width q scalar inverse powers)) s hs.1 hs.2.2.2.2.2
      hs.2.1 hs.2.2.1 hs.2.2.2.2.1 (by omega) hout
  have hm:=SemiprimeD1StackNormalizedInverseStateBounds.mass_small _ s hs.1 hbank
  exact source_arithmetic s q _ _ hs.1 hs.2.2.2.2.1 hl hm
/-- Whole actual source reaches exact halted full bank within its OWN fixed polynomial clock. -/
theorem source_run_bounded (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width:List Bool):
    ∃time ≤ polynomial inverse powers scalar q width,SemiprimeD1StackCalls.run program time
      (initial (SemiprimeD1StackNormalizedInverse.tape inverse) (SemiprimeD1StackNormalizedInverse.tape powers)
        (SemiprimeD1StackNormalizedInverse.signed scalar) scalar.denominator (SemiprimeD1StackRecoveryWeightsIndices.unary q) width)=
      some (done inverse powers scalar q width):=by
  obtain ⟨time,ht,hr⟩:=source_run inverse powers scalar q width
  exact ⟨time,ht.trans (timeBound_le inverse powers scalar q width),hr⟩
/-- Genuine fixed60-role FinTM2 uses the SAME source and whole own clock, including real calls and returns. -/
noncomputable def machineSource (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width:List Bool):
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial (SemiprimeD1StackNormalizedInverse.tape inverse) (SemiprimeD1StackNormalizedInverse.tape powers)
        (SemiprimeD1StackNormalizedInverse.signed scalar) scalar.denominator (SemiprimeD1StackRecoveryWeightsIndices.unary q) width))
      (some (SemiprimeD1StackCalls.configuration (done inverse powers scalar q width))) (polynomial inverse powers scalar q width):=by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .denominator) (aux .output) (.local .start) program
  let h:=source_run_bounded inverse powers scalar q width
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackRecoveryWeightsBounds
