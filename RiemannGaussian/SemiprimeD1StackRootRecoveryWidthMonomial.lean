/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootRecoveryWidthBounds
/-! # Fixed original-input scope rate after actual width-template acquisition -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootRecoveryWidthMonomial
open SemiprimeD1StackRootRecoveryWidthBounds
namespace Arity
export SemiprimeD1StackAllDescriptorRecordRootBounds (arityCapacity)
end Arity
/-- Fixed coefficient and degree precede all original inputs; adding actual width acquisition preserves the same scope exponent. -/
theorem runBound_monomial:∃coef degree:Nat,∀bits:List Bool,
    runBound bits ≤ coef*(bits.length+1)^degree*2^(28500*Arity.arityCapacity bits):=by
  obtain ⟨coef,degree,hroot⟩:=SemiprimeD1StackRootPacketPaddingMonomial.runBound_monomial
  refine ⟨coef+clockCoefficient,degree+120,?_⟩
  intro bits
  let H:Nat:=(bits.length+1)^(degree+120)
  let E:Nat:=2^(28500*Arity.arityCapacity bits)
  have hpos:1 ≤ bits.length+1:=by omega
  have he:1 ≤ E:=Nat.pow_pos (by decide)
  have hd:(bits.length+1)^degree ≤ H:=Nat.pow_le_pow_right hpos (by omega)
  have hw:(bits.length+1)^120 ≤ H:=Nat.pow_le_pow_right hpos (by omega)
  have hpay:H ≤ H*E:=by simpa only [Nat.mul_one] using Nat.mul_le_mul_left H he
  have hr:SemiprimeD1StackRootPacketPaddingBounds.runBound bits ≤ coef*H*E:=
    (hroot bits).trans (Nat.mul_le_mul_right E (Nat.mul_le_mul_left coef hd))
  have ha:clockCoefficient*(bits.length+1)^120 ≤ clockCoefficient*H*E:=by
    have h:=Nat.mul_le_mul_left clockCoefficient (hw.trans hpay)
    simpa only [Nat.mul_assoc] using h
  change runBound bits ≤ (coef+clockCoefficient)*H*E
  unfold runBound
  nlinarith only [hr,ha]
end RiemannGaussian.SemiprimeD1StackRootRecoveryWidthMonomial
