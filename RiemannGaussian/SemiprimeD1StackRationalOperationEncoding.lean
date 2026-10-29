/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRationalOperation
/-! # Complete36-word physical boundaries of literal rational operations -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRationalOperationEncoding
open SemiprimeD1StackRationalOperation
/-- All36 actual source, shared arithmetic, scratch and result words. -/
structure Words where
  /-- Actual x bytes. -/
  x:List Bool:=[]
  /-- Actual y bytes. -/
  y:List Bool:=[]
  /-- Actual digits bytes. -/
  digits:List Bool:=[]
  /-- Actual left bytes. -/
  left:List Bool:=[]
  /-- Actual right bytes. -/
  right:List Bool:=[]
  /-- Actual scratch bytes. -/
  scratch:List Bool:=[]
  /-- Actual difference bytes. -/
  difference:List Bool:=[]
  /-- Actual remainder bytes. -/
  remainder:List Bool:=[]
  /-- Actual quotient bytes. -/
  quotient:List Bool:=[]
  /-- Actual copyScratch bytes. -/
  copyScratch:List Bool:=[]
  /-- Actual template bytes. -/
  template:List Bool:=[]
  /-- Actual originalLeft bytes. -/
  originalLeft:List Bool:=[]
  /-- Actual originalRight bytes. -/
  originalRight:List Bool:=[]
  /-- Actual fuel bytes. -/
  fuel:List Bool:=[]
  /-- Actual scan bytes. -/
  scan:List Bool:=[]
  /-- Actual next bytes. -/
  next:List Bool:=[]
  /-- Actual trimScratch bytes. -/
  trimScratch:List Bool:=[]
  /-- Actual output bytes. -/
  output:List Bool:=[]
  /-- Actual originalSigned bytes. -/
  originalSigned:List Bool:=[]
  /-- Actual numeratorOutput bytes. -/
  numeratorOutput:List Bool:=[]
  /-- Actual denominatorOutput bytes. -/
  denominatorOutput:List Bool:=[]
  /-- Actual signOutput bytes. -/
  signOutput:List Bool:=[]
  /-- Actual multFactor bytes. -/
  multFactor:List Bool:=[]
  /-- Actual multCopied bytes. -/
  multCopied:List Bool:=[]
  /-- Actual multScratch bytes. -/
  multScratch:List Bool:=[]
  /-- Actual multInput bytes. -/
  multInput:List Bool:=[]
  /-- Actual multDigits bytes. -/
  multDigits:List Bool:=[]
  /-- Actual leftSigned bytes. -/
  leftSigned:List Bool:=[]
  /-- Actual leftDen bytes. -/
  leftDen:List Bool:=[]
  /-- Actual rightSigned bytes. -/
  rightSigned:List Bool:=[]
  /-- Actual rightDen bytes. -/
  rightDen:List Bool:=[]
  /-- Actual templateInput bytes. -/
  templateInput:List Bool:=[]
  /-- Actual leftMagnitude bytes. -/
  leftMagnitude:List Bool:=[]
  /-- Actual rightMagnitude bytes. -/
  rightMagnitude:List Bool:=[]
  /-- Actual finalNumerator bytes. -/
  finalNumerator:List Bool:=[]
  /-- Actual finalDenominator bytes. -/
  finalDenominator:List Bool:=[]
/-- Complete physical store, with shared arithmetic represented exactly once. -/
def bank (w:Words) :Stack→List Bool
  | .inl k=>SemiprimeD1StackRationalNormalizeEncoding.bank {x:=w.x,y:=w.y,digits:=w.digits,left:=w.left,right:=w.right,scratch:=w.scratch,difference:=w.difference,remainder:=w.remainder,quotient:=w.quotient,copyScratch:=w.copyScratch,template:=w.template,originalLeft:=w.originalLeft,originalRight:=w.originalRight,fuel:=w.fuel,scan:=w.scan,next:=w.next,trimScratch:=w.trimScratch,output:=w.output,originalSigned:=w.originalSigned,numeratorOutput:=w.numeratorOutput,denominatorOutput:=w.denominatorOutput,signOutput:=w.signOutput} k
  | .inr (.inl (.inl k))=>if k=0 then w.multFactor else if k=1 then w.multCopied else w.multScratch
  | .inr (.inl (.inr b))=>if b then w.multDigits else w.multInput
  | .inr (.inr k)=>match k with
    | .leftSigned=>w.leftSigned | .leftDen=>w.leftDen | .rightSigned=>w.rightSigned | .rightDen=>w.rightDen
    | .template=>w.templateInput | .leftMagnitude=>w.leftMagnitude | .rightMagnitude=>w.rightMagnitude
    | .numeratorOutput=>w.finalNumerator | .denominatorOutput=>w.finalDenominator
/-- One actual x update changes exactly its physical word. -/
theorem update_x (w:Words) (xs:List Bool) :
    Function.update (bank w) (normalizeStack (SemiprimeD1StackRationalNormalize.x)) xs=bank {w with x:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual y update changes exactly its physical word. -/
theorem update_y (w:Words) (xs:List Bool) :
    Function.update (bank w) (normalizeStack (SemiprimeD1StackRationalNormalize.y)) xs=bank {w with y:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual digits update changes exactly its physical word. -/
theorem update_digits (w:Words) (xs:List Bool) :
    Function.update (bank w) (normalizeStack (SemiprimeD1StackRationalNormalize.dividerStack (.inr .digits))) xs=bank {w with digits:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual left update changes exactly its physical word. -/
theorem update_left (w:Words) (xs:List Bool) :
    Function.update (bank w) (normalizeStack (SemiprimeD1StackRationalNormalize.dividerStack (.inl .left))) xs=bank {w with left:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual right update changes exactly its physical word. -/
theorem update_right (w:Words) (xs:List Bool) :
    Function.update (bank w) (normalizeStack (SemiprimeD1StackRationalNormalize.dividerStack (.inl .right))) xs=bank {w with right:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual scratch update changes exactly its physical word. -/
theorem update_scratch (w:Words) (xs:List Bool) :
    Function.update (bank w) (normalizeStack (SemiprimeD1StackRationalNormalize.dividerStack (.inl .scratch))) xs=bank {w with scratch:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual difference update changes exactly its physical word. -/
theorem update_difference (w:Words) (xs:List Bool) :
    Function.update (bank w) (normalizeStack (SemiprimeD1StackRationalNormalize.dividerStack (.inl .output))) xs=bank {w with difference:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual remainder update changes exactly its physical word. -/
theorem update_remainder (w:Words) (xs:List Bool) :
    Function.update (bank w) (normalizeStack (SemiprimeD1StackRationalNormalize.remainder)) xs=bank {w with remainder:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual quotient update changes exactly its physical word. -/
theorem update_quotient (w:Words) (xs:List Bool) :
    Function.update (bank w) (normalizeStack (SemiprimeD1StackRationalNormalize.quotient)) xs=bank {w with quotient:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual copyScratch update changes exactly its physical word. -/
theorem update_copyScratch (w:Words) (xs:List Bool) :
    Function.update (bank w) (normalizeStack (SemiprimeD1StackRationalNormalize.copyScratch)) xs=bank {w with copyScratch:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual template update changes exactly its physical word. -/
theorem update_template (w:Words) (xs:List Bool) :
    Function.update (bank w) (normalizeStack (SemiprimeD1StackRationalNormalize.dividerStack (.inr .template))) xs=bank {w with template:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual originalLeft update changes exactly its physical word. -/
theorem update_originalLeft (w:Words) (xs:List Bool) :
    Function.update (bank w) (normalizeStack (SemiprimeD1StackRationalNormalize.numerator)) xs=bank {w with originalLeft:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual originalRight update changes exactly its physical word. -/
theorem update_originalRight (w:Words) (xs:List Bool) :
    Function.update (bank w) (normalizeStack (SemiprimeD1StackRationalNormalize.denominator)) xs=bank {w with originalRight:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual fuel update changes exactly its physical word. -/
theorem update_fuel (w:Words) (xs:List Bool) :
    Function.update (bank w) (normalizeStack (SemiprimeD1StackRationalNormalize.gcdStack (SemiprimeD1StackEuclidGCD.aux .fuel))) xs=bank {w with fuel:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual scan update changes exactly its physical word. -/
theorem update_scan (w:Words) (xs:List Bool) :
    Function.update (bank w) (normalizeStack (SemiprimeD1StackRationalNormalize.scan)) xs=bank {w with scan:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual next update changes exactly its physical word. -/
theorem update_next (w:Words) (xs:List Bool) :
    Function.update (bank w) (normalizeStack (SemiprimeD1StackRationalNormalize.gcdStack (SemiprimeD1StackEuclidGCD.aux .next))) xs=bank {w with next:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual trimScratch update changes exactly its physical word. -/
theorem update_trimScratch (w:Words) (xs:List Bool) :
    Function.update (bank w) (normalizeStack (SemiprimeD1StackRationalNormalize.gcdStack (SemiprimeD1StackEuclidGCD.aux .trimScratch))) xs=bank {w with trimScratch:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual output update changes exactly its physical word. -/
theorem update_output (w:Words) (xs:List Bool) :
    Function.update (bank w) (normalizeStack (SemiprimeD1StackRationalNormalize.gcdOutput)) xs=bank {w with output:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual originalSigned update changes exactly its physical word. -/
theorem update_originalSigned (w:Words) (xs:List Bool) :
    Function.update (bank w) (normalizeStack (SemiprimeD1StackRationalNormalize.aux .originalSigned)) xs=bank {w with originalSigned:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual numeratorOutput update changes exactly its physical word. -/
theorem update_numeratorOutput (w:Words) (xs:List Bool) :
    Function.update (bank w) (normalizeStack (SemiprimeD1StackRationalNormalize.aux .numeratorOutput)) xs=bank {w with numeratorOutput:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual denominatorOutput update changes exactly its physical word. -/
theorem update_denominatorOutput (w:Words) (xs:List Bool) :
    Function.update (bank w) (normalizeStack (SemiprimeD1StackRationalNormalize.aux .denominatorOutput)) xs=bank {w with denominatorOutput:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual signOutput update changes exactly its physical word. -/
theorem update_signOutput (w:Words) (xs:List Bool) :
    Function.update (bank w) (normalizeStack (SemiprimeD1StackRationalNormalize.aux .signOutput)) xs=bank {w with signOutput:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual multFactor update changes exactly its physical word. -/
theorem update_multFactor (w:Words) (xs:List Bool) :
    Function.update (bank w) (multiplierStack SemiprimeD1StackMultiplier.factor) xs=bank {w with multFactor:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual multCopied update changes exactly its physical word. -/
theorem update_multCopied (w:Words) (xs:List Bool) :
    Function.update (bank w) (multiplierStack SemiprimeD1StackMultiplier.copied) xs=bank {w with multCopied:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual multScratch update changes exactly its physical word. -/
theorem update_multScratch (w:Words) (xs:List Bool) :
    Function.update (bank w) (multiplierStack SemiprimeD1StackMultiplier.copyScratch) xs=bank {w with multScratch:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual multInput update changes exactly its physical word. -/
theorem update_multInput (w:Words) (xs:List Bool) :
    Function.update (bank w) (multiplierStack SemiprimeD1StackMultiplier.input) xs=bank {w with multInput:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual multDigits update changes exactly its physical word. -/
theorem update_multDigits (w:Words) (xs:List Bool) :
    Function.update (bank w) (multiplierStack SemiprimeD1StackMultiplier.digits) xs=bank {w with multDigits:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual leftSigned update changes exactly its physical word. -/
theorem update_leftSigned (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .leftSigned) xs=bank {w with leftSigned:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual leftDen update changes exactly its physical word. -/
theorem update_leftDen (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .leftDen) xs=bank {w with leftDen:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual rightSigned update changes exactly its physical word. -/
theorem update_rightSigned (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .rightSigned) xs=bank {w with rightSigned:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual rightDen update changes exactly its physical word. -/
theorem update_rightDen (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .rightDen) xs=bank {w with rightDen:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual templateInput update changes exactly its physical word. -/
theorem update_templateInput (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .template) xs=bank {w with templateInput:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual leftMagnitude update changes exactly its physical word. -/
theorem update_leftMagnitude (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .leftMagnitude) xs=bank {w with leftMagnitude:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual rightMagnitude update changes exactly its physical word. -/
theorem update_rightMagnitude (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .rightMagnitude) xs=bank {w with rightMagnitude:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual finalNumerator update changes exactly its physical word. -/
theorem update_finalNumerator (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .numeratorOutput) xs=bank {w with finalNumerator:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- One actual finalDenominator update changes exactly its physical word. -/
theorem update_finalDenominator (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .denominatorOutput) xs=bank {w with finalDenominator:=xs}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- Only the five retained original words are initialized. -/
def originals (ls ld rs rd template:List Bool) :Words:=
  {leftSigned:=ls,leftDen:=ld,rightSigned:=rs,rightDen:=rd,templateInput:=template}
/-- Honest five-word input equals the complete store view with all31 derived words empty. -/
theorem input_bank (ls ld rs rd template:List Bool) :
    input ls ld rs rd template=bank (originals ls ld rs rd template):=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
/-- Interpretation of the actual three stopped result words; never a runtime opcode. -/
def outputWord (data:Stack→List Bool) :SemiprimeRationalBits.RationalWord:=
  ⟨⟨(data signOutput).head?.getD false,data (aux .numeratorOutput)⟩,data (aux .denominatorOutput)⟩
/-- Every original physical byte, including sign heads and the actual VALUE-width template. -/
def inputSize (ls ld rs rd template:List Bool) :Nat:=ls.length+ld.length+rs.length+rd.length+template.length+1
end RiemannGaussian.SemiprimeD1StackRationalOperationEncoding
