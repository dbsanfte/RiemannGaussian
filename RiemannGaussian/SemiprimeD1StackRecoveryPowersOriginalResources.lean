/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryPowersStorage
import RiemannGaussian.SemiprimeD1StackRecoveryPowersValues
import RiemannGaussian.SemiprimeD1StackRecoveryWidthOriginal
/-! # Original-family paid-width/retained-q resource bound for the SAME physical source
This bounds the four-word source on actual acquired Grid/affine/width lineage.
It does not assert that this prepared entry has already been joined to N-only
initialization, nor claim any inverse/Hermite/child/counter acquisition.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryPowersOriginalResources
open SemiprimeD1StackRecoveryPowersValues
namespace B
export SemiprimeD1StackRecoveryPowersBounds (polynomial timeBound_le)
end B
namespace E
export SemiprimeD1StackRecoveryPowersEncoding (resource)
end E
namespace W
export SemiprimeD1StackRecoveryWidthPolynomial (value_bound last_original envelope)
export SemiprimeD1StackRecoveryWidthOriginal (originalA originalM sizingCoefficient original_envelope)
end W
/-- Actual binary geometry VALUE is included in the original-family dimension resource. -/
def dimensions (a M:Nat):Nat:=a+M+2^(a+1)+1
/-- The physical original template is the already paid literal width word. -/
def widthWord (a M:Nat):List Bool:=List.replicate (SemiprimeD1RecoveryNodeBits.width a M) false
/-- BOTH argument fields are actually fitted by the SAME Grid source; q is the actual bounded metadata value. -/
theorem resource_le (a M u:Nat) (selected:Fin (2^(a+1))) (t:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val) (hu:u ≤ M):
    E.resource (argument a M u t (widthWord a M)) (retained a M u selected) (widthWord a M) ≤ 10000*(dimensions a M)^5:=by
  have hw:(widthWord a M).length=SemiprimeD1RecoveryNodeBits.width a M:=List.length_replicate
  have ha:=SemiprimeD1StackRecoveryGridValues.argument_value a M u selected t (widthWord a M) ht hu hw.ge
  have hq:=SemiprimeD1WeightPrecision.nodeMultiplicity_le a M u selected.val hu
  have hv:=W.value_bound 63 a M (2^(a+1))
  rw [W.last_original] at hv
  change SemiprimeD1RecoveryNodeBits.width a M ≤ 2000*(dimensions a M)^5 at hv
  have hd:1 ≤ dimensions a M:=by unfold dimensions;omega
  have hm:M ≤ (dimensions a M)^5:=by
    have h:M ≤ dimensions a M:=by unfold dimensions;omega
    exact h.trans (Nat.le_pow (by decide:0<5))
  have hp:1 ≤ (dimensions a M)^5:=one_le_pow₀ hd
  dsimp only [E.resource,SemiprimeD1StackRecoveryPowersEncoding.resource,SemiprimeD1StackRecoveryPowersSpec.signed]
  simp only [List.length_cons]
  change (argument a M u t (widthWord a M)).numerator.magnitude.length+1+
    (argument a M u t (widthWord a M)).denominator.length+retained a M u selected+(widthWord a M).length+1 ≤ _
  dsimp only [argument] at ⊢
  have haw:=ha.2.2
  dsimp only [retained] at ⊢
  unfold SemiprimeRationalBits.Width at haw
  nlinarith only [haw.1,haw.2,hw,hq,hv,hm,hp]
/-- Whole actual cached-power clock is a fixed original-dimension polynomial, independently of every native report clock. -/
theorem original_clock (a M u:Nat) (selected:Fin (2^(a+1))) (t:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val) (hu:u ≤ M):
    SemiprimeD1StackRecoveryPowersExecution.timeBound (argument a M u t (widthWord a M)) (widthWord a M) (retained a M u selected) ≤
      10^100*(dimensions a M)^50:=by
  have h:=B.timeBound_le (argument a M u t (widthWord a M)) (retained a M u selected) (widthWord a M)
  have hp:=Nat.pow_le_pow_left (resource_le a M u selected t ht hu) 10
  have hm:=Nat.mul_le_mul_left (10^40) hp
  unfold B.polynomial at h
  rw [mul_pow,←pow_mul] at hm
  norm_num1 at hm ⊢
  omega
/-- Every actual47-role plus real-return prefix is paid by the original-dimension bound through the SAME source resource. -/
theorem original_space (a M u:Nat) (selected:Fin (2^(a+1))) (t:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val) (hu:u ≤ M):
    SemiprimeD1StackRecoveryPowersStorage.spacePolynomial (argument a M u t (widthWord a M))
      (retained a M u selected) (widthWord a M) ≤ 10^103*(dimensions a M)^50:=by
  have hm:=Nat.mul_le_mul_left (10^43) (Nat.pow_le_pow_left (resource_le a M u selected t ht hu) 10)
  unfold SemiprimeD1StackRecoveryPowersStorage.spacePolynomial
  rw [mul_pow,←pow_mul] at hm
  norm_num1 at hm ⊢
  omega
/-- Fixed coefficient precedes every original N; argument and q acquisition remain explicit caller work. -/
def globalCoefficient:Nat:=10^100*W.sizingCoefficient^50
/-- The actual original root a/M bounds also pay q and physical W by VALUE. -/
theorem root_clock (bits t:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0<SemiprimeBitArithmetic.bitValue bits) (u:Nat) (hu:u ≤ W.originalM bits)
    (selected:Fin (2^(W.originalA bits+1))) (ht:SemiprimeBitArithmetic.bitValue t=selected.val):
    SemiprimeD1StackRecoveryPowersExecution.timeBound
      (argument (W.originalA bits) (W.originalM bits) u t (widthWord (W.originalA bits) (W.originalM bits)))
      (widthWord (W.originalA bits) (W.originalM bits)) (retained (W.originalA bits) (W.originalM bits) u selected) ≤
      globalCoefficient*(bits.length+1)^500:=by
  have h:=original_clock (W.originalA bits) (W.originalM bits) u selected t ht hu
  have hd:=W.original_envelope bits hc hN
  change dimensions (W.originalA bits) (W.originalM bits) ≤ W.sizingCoefficient*(bits.length+1)^10 at hd
  have hm:=Nat.mul_le_mul_left (10^100) (Nat.pow_le_pow_left hd 50)
  rw [mul_pow,←pow_mul] at hm
  unfold globalCoefficient
  simpa only [Nat.mul_assoc,show 10*50=500 by decide] using h.trans hm
end RiemannGaussian.SemiprimeD1StackRecoveryPowersOriginalResources
