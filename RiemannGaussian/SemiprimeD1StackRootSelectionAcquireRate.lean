/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootScheduleOriginal
import RiemannGaussian.SemiprimeD1StackRootPhaseGridBounds
/-! # The genuinely enumerated root alphabet has polynomial original-input size
The exact dyadic schedule, rather than a coarse bound on acquired unary
metadata, pays for every one of the64^a actual alphabet entries.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootSelectionAcquireRate
/-- The fixed epsilon denominator makes every original cumulative exponent at most lambda. -/
theorem schedule_exponent_le (lam depth:Nat) :SemiprimeD1Schedule.exponent lam depth ≤lam :=by
  have h4:4 ≤SemiprimeD1Schedule.epsilonDenominator:=by decide
  have hm:=Nat.mul_le_mul_right (lam/SemiprimeD1Schedule.epsilonDenominator) h4
  have hd:SemiprimeD1Schedule.epsilonDenominator*(lam/SemiprimeD1Schedule.epsilonDenominator) ≤lam:=by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self lam SemiprimeD1Schedule.epsilonDenominator
  exact (SemiprimeD1Schedule.exponent_le lam depth).trans (hm.trans hd)
/-- Exact proof description of the physically acquired root alphabet dimension. -/
def originalDimension (N:Nat) :Nat :=
  SemiprimeD1Schedule.exponent (SemiprimeD1StackRootScheduleOriginal.originalLambda N) 0
/-- Ceiling-log arithmetic pays the binary exponential from the actual original bit length. -/
theorem original_power_le (N:Nat) :
    2^(SemiprimeD1StackRootScheduleOriginal.originalLambda N) ≤
      10^7*(SemiprimeMacroParameters.bitLength N+1) :=by
  let ell:=SemiprimeMacroParameters.bitLength N
  have h:=SemiprimeD1StackRootPhaseGridBounds.pow_clog_le (2^20*ell+2) (by omega)
  change 2^(Nat.clog 2 (2^20*ell+2)) ≤10^7*(ell+1)
  omega
/-- The actual root unary dimension is logarithmic before its genuine materialization. -/
theorem dimension_le (N:Nat) :
    originalDimension N+1 ≤10^7*(SemiprimeMacroParameters.bitLength N+1) :=by
  have ha:=schedule_exponent_le (SemiprimeD1StackRootScheduleOriginal.originalLambda N) 0
  have hl:SemiprimeD1StackRootScheduleOriginal.originalLambda N+1 ≤
      2^(SemiprimeD1StackRootScheduleOriginal.originalLambda N):=by
    exact (SemiprimeD1StackRootScheduleOriginal.originalLambda N).lt_two_pow_self
  have hp:=original_power_le N
  change originalDimension N ≤_ at ha
  omega
/-- All64^a alphabet entries are paid by a fixed degree-six polynomial in the original bit length. -/
theorem alphabet_le (N:Nat) :
    64^(originalDimension N) ≤10^42*(SemiprimeMacroParameters.bitLength N+1)^6 :=by
  have ha:=schedule_exponent_le (SemiprimeD1StackRootScheduleOriginal.originalLambda N) 0
  have hpow:=Nat.pow_le_pow_right (by decide:0 < (2:Nat)) ha
  have hp:2^(originalDimension N) ≤10^7*(SemiprimeMacroParameters.bitLength N+1):=
    hpow.trans (original_power_le N)
  calc
    64^(originalDimension N)=(2^(originalDimension N))^6:=by
      change ((2:Nat)^6)^(originalDimension N)=(2^(originalDimension N))^6
      rw [←pow_mul,←pow_mul,Nat.mul_comm 6]
    _ ≤(10^7*(SemiprimeMacroParameters.bitLength N+1))^6:=Nat.pow_le_pow_left hp 6
    _=10^42*(SemiprimeMacroParameters.bitLength N+1)^6:=by ring
end RiemannGaussian.SemiprimeD1StackRootSelectionAcquireRate
