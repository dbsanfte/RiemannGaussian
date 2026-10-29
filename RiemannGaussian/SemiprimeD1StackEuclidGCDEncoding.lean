/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackEuclidGCDSpec
/-! # Complete physical eighteen-word Euclid boundary interpretation -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackEuclidGCDEncoding
open SemiprimeD1StackEuclidGCD
/-- Every physical divider, retained input, fuel, scratch and output word. -/
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
/-- Literal complete store, with no uncounted alias or hidden data word. -/
def bank (w:Words) :Stack→List Bool
  | .inl (.inr .input)=>w.x
  | .inl (.inr .divisor)=>w.y
  | .inl (.inr .digits)=>w.digits
  | .inl (.inl .left)=>w.left
  | .inl (.inl .right)=>w.right
  | .inl (.inl .scratch)=>w.scratch
  | .inl (.inl .output)=>w.difference
  | .inl (.inr .remainder)=>w.remainder
  | .inl (.inr .quotient)=>w.quotient
  | .inl (.inr .copyScratch)=>w.copyScratch
  | .inl (.inr .template)=>w.template
  | .inr .left=>w.originalLeft
  | .inr .right=>w.originalRight
  | .inr .fuel=>w.fuel
  | .inr .scan=>w.scan
  | .inr .next=>w.next
  | .inr .trimScratch=>w.trimScratch
  | .inr .output=>w.output
/-- Actual x update leaves every other physical word unchanged. -/
theorem update_x (w:Words) (xs:List Bool) :
    Function.update (bank w) (dividerStack (.inr .input)) xs=bank {w with x:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- Actual y update leaves every other physical word unchanged. -/
theorem update_y (w:Words) (xs:List Bool) :
    Function.update (bank w) (dividerStack (.inr .divisor)) xs=bank {w with y:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- Actual digits update leaves every other physical word unchanged. -/
theorem update_digits (w:Words) (xs:List Bool) :
    Function.update (bank w) (dividerStack (.inr .digits)) xs=bank {w with digits:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- Actual left update leaves every other physical word unchanged. -/
theorem update_left (w:Words) (xs:List Bool) :
    Function.update (bank w) (dividerStack (.inl .left)) xs=bank {w with left:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- Actual right update leaves every other physical word unchanged. -/
theorem update_right (w:Words) (xs:List Bool) :
    Function.update (bank w) (dividerStack (.inl .right)) xs=bank {w with right:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- Actual scratch update leaves every other physical word unchanged. -/
theorem update_scratch (w:Words) (xs:List Bool) :
    Function.update (bank w) (dividerStack (.inl .scratch)) xs=bank {w with scratch:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- Actual difference update leaves every other physical word unchanged. -/
theorem update_difference (w:Words) (xs:List Bool) :
    Function.update (bank w) (dividerStack (.inl .output)) xs=bank {w with difference:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- Actual remainder update leaves every other physical word unchanged. -/
theorem update_remainder (w:Words) (xs:List Bool) :
    Function.update (bank w) (dividerStack (.inr .remainder)) xs=bank {w with remainder:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- Actual quotient update leaves every other physical word unchanged. -/
theorem update_quotient (w:Words) (xs:List Bool) :
    Function.update (bank w) (dividerStack (.inr .quotient)) xs=bank {w with quotient:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- Actual copyScratch update leaves every other physical word unchanged. -/
theorem update_copyScratch (w:Words) (xs:List Bool) :
    Function.update (bank w) (dividerStack (.inr .copyScratch)) xs=bank {w with copyScratch:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- Actual template update leaves every other physical word unchanged. -/
theorem update_template (w:Words) (xs:List Bool) :
    Function.update (bank w) (dividerStack (.inr .template)) xs=bank {w with template:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- Actual originalLeft update leaves every other physical word unchanged. -/
theorem update_originalLeft (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .left) xs=bank {w with originalLeft:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- Actual originalRight update leaves every other physical word unchanged. -/
theorem update_originalRight (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .right) xs=bank {w with originalRight:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- Actual fuel update leaves every other physical word unchanged. -/
theorem update_fuel (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .fuel) xs=bank {w with fuel:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- Actual scan update leaves every other physical word unchanged. -/
theorem update_scan (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .scan) xs=bank {w with scan:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- Actual next update leaves every other physical word unchanged. -/
theorem update_next (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .next) xs=bank {w with next:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- Actual trimScratch update leaves every other physical word unchanged. -/
theorem update_trimScratch (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .trimScratch) xs=bank {w with trimScratch:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- Actual output update leaves every other physical word unchanged. -/
theorem update_output (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .output) xs=bank {w with output:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- Clean literal loop boundary after actual fuel acquisition or one complete Euclid step. -/
def loopWords (left right fuel x y:List Bool) :Words:=
  {originalLeft:=left,originalRight:=right,fuel:=fuel,x:=x,y:=y}
/-- Both original inputs are retained literally; all fifteen other non-output roles are cleared. -/
def result (left right:List Bool) :Stack→List Bool:=
  bank {originalLeft:=left,originalRight:=right,output:=(SemiprimeD1StackEuclidGCDSpec.answer left right).word}
/-- Actual halt boundary clears flags and real return frames. -/
def done (left right:List Bool) :C.State Stack Label:=⟨none,none,none,result left right,[]⟩
/-- Physical original input size includes every padded byte and a positive terminal allowance. -/
def inputSize (left right:List Bool) :Nat:=left.length+right.length+1
/-- The complete clean bank is exactly the actual two-word front door. -/
theorem initial_bank (left right:List Bool) :
    input left right=bank {originalLeft:=left,originalRight:=right}:=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackEuclidGCDEncoding
