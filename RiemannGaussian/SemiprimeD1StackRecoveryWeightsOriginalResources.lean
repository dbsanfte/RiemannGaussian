/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsOriginalCaps
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsStorage
import RiemannGaussian.SemiprimeD1StackRecoveryGridOriginalResources
/-! # Original-family weight acquisition clock and every compiled prefix, with actual W/grid VALUES paid
The six acquired words remain an explicit prepared source boundary. The literal
upstream caller join, Hermite coefficients and full counter remain separate.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeightsOriginalResources
open SemiprimeD1StackRecoveryWeights SemiprimeD1StackRecoveryWeightsExecution
open SemiprimeD1StackRecoveryWeightsLegacy SemiprimeD1StackRecoveryWeightsOriginalCaps
open SemiprimeD1StackRecoveryWeightsBounds SemiprimeD1StackRecoveryWeightsStorage
namespace D
export SemiprimeD1StackRecoveryGridOriginalResources (dimensions resource_le root_dimensions)
end D
namespace W
export SemiprimeD1StackRecoveryWidthOriginal (originalA originalM sizingCoefficient)
end W
/-- Pure source-byte scaling precedes substitution of any acquired rational word. -/
theorem byte_scale (s r:Nat) (h:s ≤ 1000*r^2):10^50*s^10 ≤ 10^80*r^20:=by
  have hm:=Nat.mul_le_mul_left (10^50) (Nat.pow_le_pow_left h 10)
  rw [mul_pow,←pow_mul] at hm
  convert hm using 1;ring
/-- SAME actual complete source clock has this fixed Grid/width VALUE bound, with no recursive child clock. -/
theorem grid_clock (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool):
    timeBound (inverse width a M u selected) (powers width a M u selected) (grid width a M u selected).scalar
      (retained a M u selected) width ≤ 10^80*(R.resource a M u t width)^20:=
  (timeBound_le _ _ _ _ _).trans (byte_scale _ _ (inputSize_le a M u selected t width))
/-- Pure original-dimension scaling pays the complete actual materialized W and grid enumeration. -/
theorem dimension_scale (r d:Nat) (h:r ≤ 10000*d^5):10^80*r^20 ≤ 10^160*d^100:=by
  have hm:=Nat.mul_le_mul_left (10^80) (Nat.pow_le_pow_left h 20)
  rw [mul_pow,←pow_mul] at hm
  convert hm using 1;ring
/-- Actual exact paid Node width gives a uniform original-family polynomial before every phase/node. -/
theorem original_clock (a M u:Nat) (selected:Fin (2^(a+1))) (t:List Bool) (hu:u ≤ M):
    timeBound (inverse (List.replicate (SemiprimeD1RecoveryNodeBits.width a M) false) a M u selected)
      (powers (List.replicate (SemiprimeD1RecoveryNodeBits.width a M) false) a M u selected)
      (grid (List.replicate (SemiprimeD1RecoveryNodeBits.width a M) false) a M u selected).scalar
      (retained a M u selected) (List.replicate (SemiprimeD1RecoveryNodeBits.width a M) false) ≤ 10^160*(D.dimensions a M t)^100:=
  (grid_clock a M u selected t _).trans (dimension_scale _ _ (D.resource_le a M u t hu))
/-- SAME complete actual six-input run, exact native weights and no advised coefficient/Fits/clock stream. -/
theorem source_run_original_bounded (a M u:Nat) (selected:Fin (2^(a+1))) (t:List Bool) (hu:u ≤ M):
    ∃time ≤ 10^160*(D.dimensions a M t)^100,SemiprimeD1StackCalls.run program time
      (SemiprimeD1StackRecoveryWeightsOriginal.originalInput (List.replicate (SemiprimeD1RecoveryNodeBits.width a M) false) a M u selected)=some
      (done (inverse (List.replicate (SemiprimeD1RecoveryNodeBits.width a M) false) a M u selected)
        (powers (List.replicate (SemiprimeD1RecoveryNodeBits.width a M) false) a M u selected)
        (grid (List.replicate (SemiprimeD1RecoveryNodeBits.width a M) false) a M u selected).scalar (retained a M u selected)
        (List.replicate (SemiprimeD1RecoveryNodeBits.width a M) false)):=by
  obtain ⟨time,ht,hr⟩:=SemiprimeD1StackRecoveryWeightsOriginal.source_run_original
    (List.replicate (SemiprimeD1RecoveryNodeBits.width a M) false) a M u selected
  exact ⟨time,ht.trans (original_clock a M u selected t hu),hr⟩
/-- Fixed coefficient is chosen before all original binary N and selected phases. -/
def globalCoefficient:Nat:=10^160*(4*W.sizingCoefficient)^100
/-- Actual acquired original a/M and bounded physical binary-index bytes specialize the SAME source clock. -/
theorem root_clock (bits t:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0<SemiprimeBitArithmetic.bitValue bits) (u:Nat) (hu:u ≤ W.originalM bits)
    (selected:Fin (2^(W.originalA bits+1))) (hbytes:t.length ≤ W.originalA bits+2):
    let width:=List.replicate (SemiprimeD1RecoveryNodeBits.width (W.originalA bits) (W.originalM bits)) false
    timeBound (inverse width (W.originalA bits) (W.originalM bits) u selected)
      (powers width (W.originalA bits) (W.originalM bits) u selected)
      (grid width (W.originalA bits) (W.originalM bits) u selected).scalar (retained (W.originalA bits) (W.originalM bits) u selected) width ≤
      globalCoefficient*(bits.length+1)^1000:=by
  have h:=original_clock (W.originalA bits) (W.originalM bits) u selected t hu
  have hm:=Nat.mul_le_mul_left (10^160) (Nat.pow_le_pow_left (D.root_dimensions bits t hc hN hbytes) 100)
  rw [mul_pow,←pow_mul] at hm
  unfold globalCoefficient
  simpa only [Nat.mul_assoc,show 10*100=1000 by decide] using h.trans hm
end RiemannGaussian.SemiprimeD1StackRecoveryWeightsOriginalResources
