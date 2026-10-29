/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRationalNormalize
import RiemannGaussian.SemiprimeD1StackAssignmentOrder
/-! # Exact legacy rational bytes, including raw quotient padding and both zero signs
Only these proof interpretations mention rational values, natural GCD, lengths,
or legacy reports. The finite source uses actual scans and arithmetic calls.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRationalNormalizeSpec
open SemiprimeBitArithmetic (bitValue)
open SemiprimeBitIndexClipping (SignedWord floorSignedBits)
open SemiprimeRationalBits (RationalWord zeroWord reduceBits)
/-- Interpretation of the actually acquired compact GCD word. -/
def gcd (num den:List Bool) :List Bool:=(SemiprimeD1StackEuclidGCDSpec.answer num den).word
/-- Literal restoring-division numerator quotient; its original dividend width is retained. -/
def numerator (num den:List Bool) :List Bool:=(SemiprimeBitDivision.divideLoop num (gcd num den)).quotient
/-- Literal restoring-division denominator quotient; its original dividend width is retained. -/
def denominator (num den:List Bool) :List Bool:=(SemiprimeBitDivision.divideLoop den (gcd num den)).quotient
/-- Exact result interpretation of the actual denominator scan and the two real quotient calls. -/
def word (negative:Bool) (num den:List Bool) :RationalWord:=
  if bitValue den=0 then zeroWord else ⟨⟨negative,numerator num den⟩,denominator num den⟩
/-- Actual compact GCD keeps its exact natural value. -/
theorem gcd_value (num den:List Bool) :bitValue (gcd num den)=(bitValue num).gcd (bitValue den):=
  SemiprimeD1StackEuclidGCDSpec.answer_value num den
/-- An actually positive denominator makes the acquired divisor genuinely positive. -/
theorem gcd_positive (num den:List Bool) (hd:0<bitValue den) :0<bitValue (gcd num den):=by
  rw [gcd_value]
  exact Nat.gcd_pos_of_pos_right _ hd
/-- Quotient bytes depend only on a positive divisor's value and the actual dividend width. -/
theorem quotient_eq (xs a b:List Bool) (ha:0<bitValue a) (hb:0<bitValue b) (hab:bitValue a=bitValue b) :
    (SemiprimeBitDivision.divideLoop xs a).quotient=(SemiprimeBitDivision.divideBits xs b).quotient:=by
  apply SemiprimeD1StackAssignmentOrder.word_value_injective
  · exact (SemiprimeBitDivision.divideLoop_widths xs a).2.1.trans
      (SemiprimeBitDivision.divideBits_widths hb).2.symm
  · rw [(SemiprimeD1StackDividerExecution.output_values xs a ha).1,
      (SemiprimeBitDivision.divideBits_correct xs b).1,hab]
/-- A true GCD divides the original magnitude, so legacy signed-floor correction is actually false.
The legacy sign is retained even when the quotient is zero. -/
theorem floor_gcd_exact (negative:Bool) (num den:List Bool) :
    (floorSignedBits ⟨negative,num⟩ (SemiprimeBitGcd.gcdBits num den).bits).word=
      ⟨negative,(SemiprimeBitDivision.divideBits num (SemiprimeBitGcd.gcdBits num den).bits).quotient⟩:=by
  have hr:bitValue (SemiprimeBitDivision.divideBits num (SemiprimeBitGcd.gcdBits num den).bits).remainder=0:=by
    rw [(SemiprimeBitDivision.divideBits_correct _ _).2,(SemiprimeBitGcd.gcdBits_correct num den).1]
    exact Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_left _ _)
  have hf:(SemiprimeBitDivision.nonzeroBits (SemiprimeBitDivision.divideBits num
      (SemiprimeBitGcd.gcdBits num den).bits).remainder).nonzero=false:=by
    apply Bool.eq_false_of_not_eq_true
    intro h
    have hp:=(SemiprimeBitDivision.nonzeroBits_correct _).mp h
    omega
  simp only [floorSignedBits,hf,Bool.and_false,Bool.false_eq_true,ite_false]
/-- Whole exact legacy byte equality, covering padded-zero denominators and preserving negative zero on positive denominators. -/
theorem word_legacy (negative:Bool) (num den:List Bool) :
    word negative num den=(reduceBits ⟨⟨negative,num⟩,den⟩).word:=by
  by_cases hz:bitValue den=0
  · have hc:¬(SemiprimeBitDivision.nonzeroBits den).nonzero=true:=by
      intro h;have hp:=(SemiprimeBitDivision.nonzeroBits_correct den).mp h;omega
    simp only [word,hz,ite_true,reduceBits,ite_eq_right hc]
  · have hd:0<bitValue den:=by omega
    have hc:=(SemiprimeBitDivision.nonzeroBits_correct den).mpr hd
    have hg:=gcd_positive num den hd
    have hgold:0<bitValue (SemiprimeBitGcd.gcdBits num den).bits:=by
      rw [(SemiprimeBitGcd.gcdBits_correct num den).1]
      exact Nat.gcd_pos_of_pos_right _ hd
    have hv:bitValue (gcd num den)=bitValue (SemiprimeBitGcd.gcdBits num den).bits:=by
      rw [gcd_value,(SemiprimeBitGcd.gcdBits_correct num den).1]
    have hn:=quotient_eq num (gcd num den) (SemiprimeBitGcd.gcdBits num den).bits hg hgold hv
    have hdq:=quotient_eq den (gcd num den) (SemiprimeBitGcd.gcdBits num den).bits hg hgold hv
    simp only [word,ite_eq_right hz,reduceBits,ite_eq_left hc]
    rw [floor_gcd_exact]
    exact congrArg₂ RationalWord.mk (congrArg (SignedWord.mk negative) hn) hdq
/-- Exact canonical integer numerator and positive denominator of the original input rational. -/
theorem word_components (negative:Bool) (num den:List Bool) :
    (word negative num den).numerator.value=(⟨⟨negative,num⟩,den⟩:RationalWord).value.num ∧
      bitValue (word negative num den).denominator=(⟨⟨negative,num⟩,den⟩:RationalWord).value.den:=by
  rw [word_legacy]
  exact SemiprimeRationalBits.reduceBits_components _
/-- Normalization preserves the original rational value, including the physically guarded zero-denominator totalization. -/
theorem word_value (negative:Bool) (num den:List Bool) :
    (word negative num den).value=(⟨⟨negative,num⟩,den⟩:RationalWord).value:=by
  rw [word_legacy]
  exact SemiprimeRationalBits.reduceBits_value _
/-- Every actual normalized result has a positive denominator, including the literal zero-denominator branch. -/
theorem word_valid (negative:Bool) (num den:List Bool) :(word negative num den).Valid:=by
  rw [word_legacy]
  exact SemiprimeRationalBits.reduceBits_valid _
/-- The actual numerator quotient has exactly its original magnitude's physical byte width. -/
theorem numerator_length (num den:List Bool) :(numerator num den).length=num.length:=
  (SemiprimeBitDivision.divideLoop_widths num (gcd num den)).2.1
/-- The actual denominator quotient has exactly its original denominator's physical byte width. -/
theorem denominator_length (num den:List Bool) :(denominator num den).length=den.length:=
  (SemiprimeBitDivision.divideLoop_widths den (gcd num den)).2.1
end RiemannGaussian.SemiprimeD1StackRationalNormalizeSpec
