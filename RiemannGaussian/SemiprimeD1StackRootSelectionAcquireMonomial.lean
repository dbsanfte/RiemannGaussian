/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootSelectionAcquireBounds
/-! # Fixed original-input rate for the same whole selected-key source
The real row producer has one scope exponential. A fixed polynomial of its
actual resource bound raises only the fixed coefficient in that exponent.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootSelectionAcquireMonomial
open SemiprimeD1StackRootSelectionAcquireBounds SemiprimeD1StackRootSelectionAcquireInputBounds
namespace R
export SemiprimeD1StackRootNetworkRowsBounds
  (runBound runBoundPrefix prefixPolynomial polynomial_monomial)
end R
namespace Arity
export SemiprimeD1StackAllDescriptorRecordRootBounds (arityCapacity)
end Arity
/-- Fixed polynomial witnesses precede every input for the whole actual producer envelope. -/
theorem envelope_monomial :∃coef degree:Nat,∀bits:List Bool,
    envelope bits ≤coef*(bits.length+1)^degree*2^(57*Arity.arityCapacity bits) :=by
  obtain ⟨coef,degree,hpoly⟩:=R.polynomial_monomial
  refine ⟨1+coef+10^51,degree+11,?_⟩
  intro bits
  let H:Nat:=(bits.length+1)^(degree+11)
  let E:Nat:=2^(57*Arity.arityCapacity bits)
  have hpos:1 ≤bits.length+1:=by omega
  have he:1 ≤E:=Nat.pow_pos (by decide)
  have hself:bits.length+1 ≤H:=by
    simpa only [pow_one] using Nat.pow_le_pow_right hpos (by omega:1 ≤degree+11)
  have hd:(bits.length+1)^degree ≤H:=Nat.pow_le_pow_right hpos (by omega)
  have h10:(bits.length+1)^10 ≤H:=Nat.pow_le_pow_right hpos (by omega)
  have hr0:R.runBound bits ≤coef*(bits.length+1)^degree*E:=by
    unfold R.runBound R.runBoundPrefix
    exact Nat.mul_le_mul_right E (hpoly bits.length)
  have hr:R.runBound bits ≤coef*H*E:=
    hr0.trans (Nat.mul_le_mul_right E (Nat.mul_le_mul_left coef hd))
  have hp:parameterBound bits ≤10^51*H:=Nat.mul_le_mul_left (10^51) h10
  have hlin:bits.length+parameterBound bits+1 ≤(1+10^51)*H:=by
    nlinarith only [hself,hp]
  have hpay:bits.length+parameterBound bits+1 ≤(bits.length+parameterBound bits+1)*E:=by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (bits.length+parameterBound bits+1) he
  have hlinE:=hpay.trans (Nat.mul_le_mul_right E hlin)
  change envelope bits ≤(1+coef+10^51)*H*E
  unfold envelope
  nlinarith only [hr,hlinE]
/-- The SAME original-input whole-source bound has fixed coefficients and a fixed scope exponent. -/
theorem runBound_monomial :∃coef degree:Nat,∀bits:List Bool,
    SemiprimeD1StackRootSelectionAcquireBounds.runBound bits ≤
      coef*(bits.length+1)^degree*2^(5700*Arity.arityCapacity bits) :=by
  obtain ⟨coef,degree,hbound⟩:=envelope_monomial
  refine ⟨clockCoefficient*coef^100,degree*100,?_⟩
  intro bits
  have h:=Nat.mul_le_mul_left clockCoefficient (Nat.pow_le_pow_left (hbound bits) 100)
  unfold SemiprimeD1StackRootSelectionAcquireBounds.runBound
  calc
    _ ≤clockCoefficient*(coef*(bits.length+1)^degree*2^(57*Arity.arityCapacity bits))^100:=h
    _=(clockCoefficient*coef^100)*(bits.length+1)^(degree*100)*2^(5700*Arity.arityCapacity bits):=by
      simp only [mul_pow,←pow_mul]
      rw [show 57*Arity.arityCapacity bits*100=5700*Arity.arityCapacity bits by omega]
      ring
end RiemannGaussian.SemiprimeD1StackRootSelectionAcquireMonomial
