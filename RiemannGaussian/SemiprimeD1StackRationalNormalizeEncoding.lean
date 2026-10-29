/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRationalNormalizeSpec
/-! # Complete actual22-word rational normalization boundaries -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRationalNormalizeEncoding
open SemiprimeD1StackRationalNormalize
/-- Every actual source, arithmetic, scratch, sign and output word. -/
structure Words where
  /-- Actual x Boolean word. -/
  x:List Bool:=[]
  /-- Actual y Boolean word. -/
  y:List Bool:=[]
  /-- Actual digits Boolean word. -/
  digits:List Bool:=[]
  /-- Actual left Boolean word. -/
  left:List Bool:=[]
  /-- Actual right Boolean word. -/
  right:List Bool:=[]
  /-- Actual scratch Boolean word. -/
  scratch:List Bool:=[]
  /-- Actual difference Boolean word. -/
  difference:List Bool:=[]
  /-- Actual remainder Boolean word. -/
  remainder:List Bool:=[]
  /-- Actual quotient Boolean word. -/
  quotient:List Bool:=[]
  /-- Actual copyScratch Boolean word. -/
  copyScratch:List Bool:=[]
  /-- Actual template Boolean word. -/
  template:List Bool:=[]
  /-- Actual originalLeft Boolean word. -/
  originalLeft:List Bool:=[]
  /-- Actual originalRight Boolean word. -/
  originalRight:List Bool:=[]
  /-- Actual fuel Boolean word. -/
  fuel:List Bool:=[]
  /-- Actual scan Boolean word. -/
  scan:List Bool:=[]
  /-- Actual next Boolean word. -/
  next:List Bool:=[]
  /-- Actual trimScratch Boolean word. -/
  trimScratch:List Bool:=[]
  /-- Actual output Boolean word. -/
  output:List Bool:=[]
  /-- Actual originalSigned Boolean word. -/
  originalSigned:List Bool:=[]
  /-- Actual numeratorOutput Boolean word. -/
  numeratorOutput:List Bool:=[]
  /-- Actual denominatorOutput Boolean word. -/
  denominatorOutput:List Bool:=[]
  /-- Actual signOutput Boolean word. -/
  signOutput:List Bool:=[]
/-- Complete literal physical store, including every reused GCD/Divider role. -/
def bank (w:Words) :Stack→List Bool
  | .inl (.inl (.inr .input))=>w.x
  | .inl (.inl (.inr .divisor))=>w.y
  | .inl (.inl (.inr .digits))=>w.digits
  | .inl (.inl (.inl .left))=>w.left
  | .inl (.inl (.inl .right))=>w.right
  | .inl (.inl (.inl .scratch))=>w.scratch
  | .inl (.inl (.inl .output))=>w.difference
  | .inl (.inl (.inr .remainder))=>w.remainder
  | .inl (.inl (.inr .quotient))=>w.quotient
  | .inl (.inl (.inr .copyScratch))=>w.copyScratch
  | .inl (.inl (.inr .template))=>w.template
  | .inl (.inr .left)=>w.originalLeft
  | .inl (.inr .right)=>w.originalRight
  | .inl (.inr .fuel)=>w.fuel
  | .inl (.inr .scan)=>w.scan
  | .inl (.inr .next)=>w.next
  | .inl (.inr .trimScratch)=>w.trimScratch
  | .inl (.inr .output)=>w.output
  | .inr .originalSigned=>w.originalSigned
  | .inr .numeratorOutput=>w.numeratorOutput
  | .inr .denominatorOutput=>w.denominatorOutput
  | .inr .signOutput=>w.signOutput
/-- A real x update preserves every other physical word. -/
theorem update_x (w:Words) (xs:List Bool) :
    Function.update (bank w) (dividerStack (.inr .input)) xs=bank {w with x:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A real y update preserves every other physical word. -/
theorem update_y (w:Words) (xs:List Bool) :
    Function.update (bank w) (dividerStack (.inr .divisor)) xs=bank {w with y:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A real digits update preserves every other physical word. -/
theorem update_digits (w:Words) (xs:List Bool) :
    Function.update (bank w) (dividerStack (.inr .digits)) xs=bank {w with digits:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A real left update preserves every other physical word. -/
theorem update_left (w:Words) (xs:List Bool) :
    Function.update (bank w) (dividerStack (.inl .left)) xs=bank {w with left:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A real right update preserves every other physical word. -/
theorem update_right (w:Words) (xs:List Bool) :
    Function.update (bank w) (dividerStack (.inl .right)) xs=bank {w with right:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A real scratch update preserves every other physical word. -/
theorem update_scratch (w:Words) (xs:List Bool) :
    Function.update (bank w) (dividerStack (.inl .scratch)) xs=bank {w with scratch:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A real difference update preserves every other physical word. -/
theorem update_difference (w:Words) (xs:List Bool) :
    Function.update (bank w) (dividerStack (.inl .output)) xs=bank {w with difference:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A real remainder update preserves every other physical word. -/
theorem update_remainder (w:Words) (xs:List Bool) :
    Function.update (bank w) (dividerStack (.inr .remainder)) xs=bank {w with remainder:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A real quotient update preserves every other physical word. -/
theorem update_quotient (w:Words) (xs:List Bool) :
    Function.update (bank w) (dividerStack (.inr .quotient)) xs=bank {w with quotient:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A real copyScratch update preserves every other physical word. -/
theorem update_copyScratch (w:Words) (xs:List Bool) :
    Function.update (bank w) (dividerStack (.inr .copyScratch)) xs=bank {w with copyScratch:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A real template update preserves every other physical word. -/
theorem update_template (w:Words) (xs:List Bool) :
    Function.update (bank w) (dividerStack (.inr .template)) xs=bank {w with template:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A real originalLeft update preserves every other physical word. -/
theorem update_originalLeft (w:Words) (xs:List Bool) :
    Function.update (bank w) (gcdStack (SemiprimeD1StackEuclidGCD.aux .left)) xs=bank {w with originalLeft:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A real originalRight update preserves every other physical word. -/
theorem update_originalRight (w:Words) (xs:List Bool) :
    Function.update (bank w) (gcdStack (SemiprimeD1StackEuclidGCD.aux .right)) xs=bank {w with originalRight:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A real fuel update preserves every other physical word. -/
theorem update_fuel (w:Words) (xs:List Bool) :
    Function.update (bank w) (gcdStack (SemiprimeD1StackEuclidGCD.aux .fuel)) xs=bank {w with fuel:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A real scan update preserves every other physical word. -/
theorem update_scan (w:Words) (xs:List Bool) :
    Function.update (bank w) (gcdStack (SemiprimeD1StackEuclidGCD.aux .scan)) xs=bank {w with scan:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A real next update preserves every other physical word. -/
theorem update_next (w:Words) (xs:List Bool) :
    Function.update (bank w) (gcdStack (SemiprimeD1StackEuclidGCD.aux .next)) xs=bank {w with next:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A real trimScratch update preserves every other physical word. -/
theorem update_trimScratch (w:Words) (xs:List Bool) :
    Function.update (bank w) (gcdStack (SemiprimeD1StackEuclidGCD.aux .trimScratch)) xs=bank {w with trimScratch:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A real output update preserves every other physical word. -/
theorem update_output (w:Words) (xs:List Bool) :
    Function.update (bank w) (gcdStack (SemiprimeD1StackEuclidGCD.aux .output)) xs=bank {w with output:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A real originalSigned update preserves every other physical word. -/
theorem update_originalSigned (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .originalSigned) xs=bank {w with originalSigned:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A real numeratorOutput update preserves every other physical word. -/
theorem update_numeratorOutput (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .numeratorOutput) xs=bank {w with numeratorOutput:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A real denominatorOutput update preserves every other physical word. -/
theorem update_denominatorOutput (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .denominatorOutput) xs=bank {w with denominatorOutput:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A real signOutput update preserves every other physical word. -/
theorem update_signOutput (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .signOutput) xs=bank {w with signOutput:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- Every initialized byte is one of the two retained original words. -/
theorem initial_bank (signed den:List Bool) :
    input signed den=bank {originalSigned:=signed,originalRight:=den}:=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- Acquired magnitude and parsed sign are physical cache words before the denominator guard. -/
def parsed (negative:Bool) (num den:List Bool) :Words:=
  {originalSigned:=negative::num,originalLeft:=num,originalRight:=den,signOutput:=[negative]}
/-- Clean positive arithmetic boundary retains the acquired magnitude, original inputs and parsed sign. -/
def ready (negative:Bool) (num den g n d:List Bool) :Words:=
  {parsed negative num den with output:=g,numeratorOutput:=n,denominatorOutput:=d}
/-- Whole output retains the original signed bytes and original denominator, with all arithmetic words empty. -/
def result (negative:Bool) (num den:List Bool) :Stack→List Bool:=bank { originalSigned:=negative::num,originalRight:=den, signOutput:=[(SemiprimeD1StackRationalNormalizeSpec.word negative num den).numerator.negative], numeratorOutput:=(SemiprimeD1StackRationalNormalizeSpec.word negative num den).numerator.magnitude, denominatorOutput:=(SemiprimeD1StackRationalNormalizeSpec.word negative num den).denominator}
/-- Interpretation reads all THREE actual stopped output words; it is never a runtime getter. -/
def outputWord (data:Stack→List Bool) :SemiprimeRationalBits.RationalWord:=
  ⟨⟨((data (aux .signOutput)).head?).getD false,data (aux .numeratorOutput)⟩,data (aux .denominatorOutput)⟩
/-- Actual final halt with exact full physical bank and cleared flags/returns. -/
def done (negative:Bool) (num den:List Bool) :C.State Stack Label:=⟨none,none,none,result negative num den,[]⟩
/-- Both original binary words, their physical sign head and one positive terminal allowance. -/
def inputSize (num den:List Bool) :Nat:=num.length+den.length+2
end RiemannGaussian.SemiprimeD1StackRationalNormalizeEncoding
