/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootSourceExecution
/-! # Literal original root and normalization syntax from original input
All exponent identities are derived from the actual acquired word/cache LENGTHS.
No expected exponent, normalizer value or supplied expression is assumed.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackRootSourceOriginal
open SemiprimeD1StackRootSources SemiprimeD1StackRootSourceExecution
open SemiprimeBitArithmetic SemiprimeMacroParameters SemiprimeMacroEntryBitCheck
/-- Actual completed public cache, obtained by the same N-only call. -/
def actualCache (bits : List Bool) : P.Stack→List Bool := SemiprimeD1BinaryPublicAcquisitionComponents.result bits
/-- The actual modulus has exactly radius+1 physical cells. -/
theorem modulus_length (bits : List Bool) :
    (actualCache bits modulusKey).length=transformLength bits.length+1 := by
  change (SemiprimeD1StackFermatWords.modulusWord (transformLength bits.length)).length=_
  have hp : 0<transformLength bits.length := by unfold transformLength;positivity
  simp only [SemiprimeD1StackFermatWords.modulusWord,List.length_cons,List.length_append,List.length_replicate,List.length_nil]
  omega
/-- Actual acquired exponent-cache length, rather than its numeric word value. -/
theorem exponent_length (bits : List Bool) :
    (actualCache bits exponentKey).length=transformExponent bits.length := by
  change (List.replicate (transformExponent bits.length) true).length=_
  exact List.length_replicate
/-- Both exponents are lengths of marker streams ACTUALLY produced by physical pops. -/
theorem marker_lengths (bits : List Bool) :
    (rootMarkers (actualCache bits)).length=transformLength bits.length-1 ∧
    (normalMarkers (actualCache bits)).length=transformLength bits.length-transformExponent bits.length := by
  simp only [rootMarkers,normalMarkers,List.length_tail,List.length_drop,modulus_length,exponent_length]
  omega
/-- Positive canonical original N identifies physical radius/exponent with the
actual public configuration, including depth+1 rather than an advised exponent. -/
theorem original_parameters (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) :
    let config:=SemiprimePublicFactorCount.publicConfig (bitValue bits) hN
    transformLength bits.length=config.r*config.t ∧ transformExponent bits.length=config.depth+1 := by
  have hw:=SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc
  have hp:=transformExponent_ge_two (bitLength_pos hN)
  dsimp [SemiprimePublicFactorCount.publicConfig]
  rw [hw,axes_product]
  constructor
  · rfl
  · unfold macroDepth;omega
/-- Literal forward root code, acquired only by nine fixed physical pushes. -/
theorem forward_root (bits : List Bool) (hN : 0<bitValue bits) (side : Fin 2) :
    (done bits).data (.inr .forwardRoot)=SemiprimeD1StackExprCodec.encode
      (rootExpr (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN) (.inl side)) [] := rfl
/-- Literal forward normalization code, acquired by five fixed physical pushes. -/
theorem forward_normalization (bits : List Bool) (hN : 0<bitValue bits) (side : Fin 2) :
    (done bits).data (.inr .forwardNormal)=SemiprimeD1StackExprCodec.encode
      (normalizationExpr (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN) (.inl side)) [] := rfl
/-- EXACT old inverse rootExpr bytes. Actual marker acquisition is modulus-WORD
copy/drop, never evaluation or scanning of the numeric modulus VALUE. -/
theorem inverse_root (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) :
    (done bits).data (.inr .root)=SemiprimeD1StackExprCodec.encode
      (rootExpr (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN) (.inr ())) [] := by
  have hm:=(marker_lengths bits).1
  have hp:=(original_parameters bits hc hN).1
  change SemiprimeD1StackExprPowerSpec.result (rootMarkers (actualCache bits)).length
    (SemiprimeD1StackExprCodec.encode fourExpr []) []=_
  rw [SemiprimeD1StackExprPowerSpec.result_original,hm,hp]
  rfl
/-- EXACT old inverse normalizationExpr bytes: actual paired marker pops,
Power(twoExpr), then literal zero/subtraction pushes. No semantic substitution. -/
theorem inverse_normalization (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) :
    (done bits).data (.inr .normal)=SemiprimeD1StackExprCodec.encode
      (normalizationExpr (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN) (.inr ())) [] := by
  have hm:=(marker_lengths bits).2
  have hp:=original_parameters bits hc hN
  change [true,false,false,false,false]++SemiprimeD1StackExprPowerSpec.result
    (normalMarkers (actualCache bits)).length (SemiprimeD1StackExprCodec.encode twoExpr []) []=_
  rw [SemiprimeD1StackExprPowerSpec.result_original,hm,hp.1,hp.2]
  rfl
/-- All original N, digit-bank, modulus, normalizer and geometry caches survive. -/
theorem retained_public (bits : List Bool) (k : P.Stack) :
    (done bits).data (.inl k)=actualCache bits k := rfl
/-- Source construction work/markers/base caches are physically cleared. -/
theorem cleanup (bits : List Bool) (k : Aux)
    (hk : k≠.root ∧ k≠.normal ∧ k≠.forwardRoot ∧ k≠.forwardNormal) :
    (done bits).data (.inr k)=[] := by cases k <;> simp_all [done,result,store,aux]
end RiemannGaussian.SemiprimeD1StackRootSourceOriginal
