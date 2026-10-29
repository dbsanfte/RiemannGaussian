/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPacketInventoryBounds
/-! # Fixed original-input rate for the whole actual shared-root packet-inventory source -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPacketInventoryMonomial
open SemiprimeD1StackRootPacketInventoryBounds SemiprimeD1StackRootPacketInventoryInputBounds
namespace Arity
export SemiprimeD1StackAllDescriptorRecordRootBounds (arityCapacity)
end Arity
/-- A fixed whole-producer envelope retains the original selected-key source's actual scope rate. -/
theorem envelope_monomial :∃coef degree:Nat,∀bits:List Bool,
    envelope bits ≤coef*(bits.length+1)^degree*2^(28500*Arity.arityCapacity bits) :=by
  obtain ⟨coef,degree,hroot⟩:=SemiprimeD1StackRootRecoveryWidthMonomial.runBound_monomial
  refine ⟨coef+1,degree+1,?_⟩
  intro bits
  let H:Nat:=(bits.length+1)^(degree+1)
  let E:Nat:=2^(28500*Arity.arityCapacity bits)
  have hpos:1 ≤bits.length+1:=by omega
  have he:1 ≤E:=Nat.pow_pos (by decide)
  have hself:bits.length+1 ≤H:=by
    simpa only [pow_one] using Nat.pow_le_pow_right hpos (by omega:1 ≤degree+1)
  have hd:(bits.length+1)^degree ≤H:=Nat.pow_le_pow_right hpos (by omega)
  have hpay:H ≤H*E:=by simpa only [Nat.mul_one] using Nat.mul_le_mul_left H he
  have hlin:bits.length+1 ≤H*E:=hself.trans hpay
  have hr:SemiprimeD1StackRootRecoveryWidthBounds.runBound bits ≤coef*H*E:=
    (hroot bits).trans (Nat.mul_le_mul_right E (Nat.mul_le_mul_left coef hd))
  change envelope bits ≤(coef+1)*H*E
  unfold envelope
  nlinarith only [hlin,hr]
/-- SAME actual whole-source cap has fixed coefficients/degrees before every input N. -/
theorem runBound_monomial :∃coef degree:Nat,∀bits:List Bool,
    runBound bits ≤coef*(bits.length+1)^degree*2^(114000*Arity.arityCapacity bits) :=by
  obtain ⟨coef,degree,hbound⟩:=envelope_monomial
  refine ⟨clockCoefficient*coef^4,degree*4,?_⟩
  intro bits
  have h:=Nat.mul_le_mul_left clockCoefficient (Nat.pow_le_pow_left (hbound bits) 4)
  unfold runBound
  calc
    _ ≤clockCoefficient*(coef*(bits.length+1)^degree*2^(28500*Arity.arityCapacity bits))^4:=h
    _=(clockCoefficient*coef^4)*(bits.length+1)^(degree*4)*2^(114000*Arity.arityCapacity bits):=by
      simp only [mul_pow,←pow_mul]
      rw [show 28500*Arity.arityCapacity bits*4=114000*Arity.arityCapacity bits by omega]
      ring
end RiemannGaussian.SemiprimeD1StackRootPacketInventoryMonomial
