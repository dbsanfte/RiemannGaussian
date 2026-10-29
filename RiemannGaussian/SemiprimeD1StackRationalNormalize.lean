/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackEuclidGCDStorage
import RiemannGaussian.SemiprimeRationalBits
/-! # Literal canonical rational normalization from actual signed binary inputs
The original signed numerator is one actual sign-prefixed binary word. A copied denominator is physically
OR-scanned; zero takes the exact legacy zero branch. The positive branch calls
actual GCD18, then twice reuses its cleared Divider11 bank, preserving original
input bytes and legacy quotient padding. No GCD, quotient, width or result operand
is supplied to this fixed finite program.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRationalNormalize
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace G
export SemiprimeD1StackEuclidGCD (Stack Label program)
end G
namespace D
export SemiprimeD1StackDivider (Stack Label code)
end D
/-- Retained actual signed word and three literal normalized-output words; the entire arithmetic bank is reused. -/
inductive Aux where | originalSigned | numeratorOutput | denominatorOutput | signOutput deriving DecidableEq,Repr
/-- Literal complete four-word caller inventory. -/
instance :Fintype Aux:=Fintype.ofList [.originalSigned,.numeratorOutput,.denominatorOutput,.signOutput] (by intro k;cases k <;> simp)
/-- All18 GCD words plus four actual sign/output words; no displaced or uncounted divider shadow. -/
abbrev Stack:=G.Stack⊕Aux
/-- Actual complete GCD inclusion. -/
def gcdStack :G.Stack→Stack:=Sum.inl
/-- Actual caller signed-word/output addresses. -/
def aux :Aux→Stack:=Sum.inr
/-- Both post-GCD positive divisions reuse the same physically cleared eleven-word bank. -/
def dividerStack (k:D.Stack) :Stack:=gcdStack (SemiprimeD1StackEuclidGCD.dividerStack k)
/-- Literal retained original numerator magnitude. -/
def numerator :Stack:=gcdStack (SemiprimeD1StackEuclidGCD.aux .left)
/-- Literal retained original unsigned denominator. -/
def denominator :Stack:=gcdStack (SemiprimeD1StackEuclidGCD.aux .right)
/-- Actual acquired compact GCD, physically erased before return. -/
def gcdOutput :Stack:=gcdStack (SemiprimeD1StackEuclidGCD.aux .output)
/-- Shared actual scan input, empty again before the actual GCD call. -/
def scan :Stack:=gcdStack (SemiprimeD1StackEuclidGCD.aux .scan)
/-- Literal actual divider first operand. -/
def x :Stack:=dividerStack (.inr .input)
/-- Literal actual divider positive divisor. -/
def y :Stack:=dividerStack (.inr .divisor)
/-- Actual quotient bytes retain the original dividend width. -/
def quotient :Stack:=dividerStack (.inr .quotient)
/-- Every returned remainder byte is physically discarded. -/
def remainder :Stack:=dividerStack (.inr .remainder)
/-- Every preserving copy uses the same cleared physical scratch. -/
def copyScratch :Stack:=dividerStack (.inr .copyScratch)
/-- Seven literal data routes, fixed before the original sign and both original magnitudes. -/
inductive Copy where | signedInput | guard | numeratorInput | denominatorInput | gcdInput | numeratorOutput | denominatorOutput
  deriving DecidableEq,Repr
/-- Complete finite enumeration of actual copy routes. -/
instance :Fintype Copy:=Fintype.ofList [.signedInput,.guard,.numeratorInput,.denominatorInput,.gcdInput,.numeratorOutput,.denominatorOutput]
  (by intro k;cases k <;> simp)
/-- Three distinct physical operands per paid copy. -/
def copyStack (what:Copy) (k:Fin 3) :Stack:=
  if k=0 then match what with
    | .signedInput=>aux .originalSigned
    | .guard|.denominatorInput=>denominator | .numeratorInput=>numerator | .gcdInput=>gcdOutput
    | .numeratorOutput|.denominatorOutput=>quotient
  else if k=1 then match what with
    | .signedInput=>numerator | .guard=>scan | .numeratorInput|.denominatorInput=>x | .gcdInput=>y
    | .numeratorOutput=>aux .numeratorOutput | .denominatorOutput=>aux .denominatorOutput
  else copyScratch
/-- Finite actual-bit scan, positive arithmetic and exact sign/zero-output control. -/
inductive Label where
  | start | parseSign | initializeSign (negative:Bool) | guardDen | scan (seen:Bool) | gcdCall | copyInput (den:Bool) | copyGcd (den:Bool) | divide (den:Bool)
  | save (den:Bool) | clearQuotient (den:Bool) | clearRemainder (den:Bool) | clearGcd | clearMagnitude | zeroClearSign
  | zeroSign | zeroDen | done | abort
  | gcd (pc:G.Label) | divider (pc:D.Label) | copier (what:Copy) (pc:Fin 9)
  deriving Fintype
/-- One actual fixed source handles zero denominator and positive GCD reduction with real arithmetic calls. -/
def program :Label→C.Instruction Stack Label
  | .start=>.call (.copier .signedInput 0) .parseSign
  | .parseSign=>.base (.pop numerator .abort (.initializeSign false) (.initializeSign true))
  | .initializeSign negative=>.base (.push (aux .signOutput) negative .guardDen)
  | .guardDen=>.call (.copier .guard 0) (.scan false)
  | .scan seen=>.base (.pop scan (if seen then .gcdCall else .zeroClearSign) (.scan seen) (.scan true))
  | .gcdCall=>.call (.gcd .start) (.copyInput false)
  | .copyInput den=>.call (.copier (if den then .denominatorInput else .numeratorInput) 0) (.copyGcd den)
  | .copyGcd den=>.call (.copier .gcdInput 0) (.divide den)
  | .divide den=>.call (.divider (.control .start)) (.save den)
  | .save den=>.call (.copier (if den then .denominatorOutput else .numeratorOutput) 0) (.clearQuotient den)
  | .clearQuotient den=>.base (.pop quotient (.clearRemainder den) (.clearQuotient den) (.clearQuotient den))
  | .clearRemainder den=>.base (.pop remainder (if den then .clearGcd else .copyInput true)
      (.clearRemainder den) (.clearRemainder den))
  | .clearGcd=>.base (.pop gcdOutput .clearMagnitude .clearGcd .clearGcd)
  | .clearMagnitude=>.base (.pop numerator .done .clearMagnitude .clearMagnitude)
  | .zeroClearSign=>.base (.pop (aux .signOutput) .zeroSign .zeroClearSign .zeroClearSign)
  | .zeroSign=>.base (.push (aux .signOutput) false .zeroDen)
  | .zeroDen=>.base (.push (aux .denominatorOutput) true .clearMagnitude)
  | .done|.abort=>.base .halt
  | .gcd pc=>SemiprimeD1StackValidationLink.instruction gcdStack Label.gcd (G.program pc)
  | .divider pc=>SemiprimeD1StackValidationLink.instruction dividerStack Label.divider (D.code pc)
  | .copier what pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack what) (Label.copier what)
      (SemiprimeD1StackCopy.code pc)
/-- Only the original sign-prefixed numerator word and original unsigned denominator are initialized. -/
def input (signed den:List Bool) :Stack→List Bool:=
  Sum.elim (SemiprimeD1StackEuclidGCD.input [] den) (fun k=>if k=.originalSigned then signed else [])
/-- Honest two-word front door; no separately supplied sign, magnitude, GCD, quotient, width or result. -/
def initial (signed den:List Bool) :C.State Stack Label:=⟨some .start,none,none,input signed den,[]⟩
/-- Fixed actual finite22-role machine; output numerator/sign/denominator are retained as three physical words. -/
def machine :Turing.FinTM2:=SemiprimeD1StackCalls.machine (aux .originalSigned) (aux .numeratorOutput) .start program
/-- All eighteen GCD and four sign/output roles are counted. -/
theorem stack_card :Fintype.card Stack=22:=by decide
/-- Every whole GCD call preserves every caller sign/output role. -/
theorem gcd_injective :Function.Injective gcdStack:=Sum.inl_injective
/-- The reused physical divider inclusion is injective, with no hidden alias collision. -/
theorem divider_injective :Function.Injective dividerStack:=gcd_injective.comp SemiprimeD1StackEuclidGCD.divider_injective
/-- Every actual copy uses three distinct physical stack addresses. -/
theorem copy_injective (what:Copy) :Function.Injective (copyStack what):=by cases what <;> decide
/-- The source control type is finite before all original words. -/
theorem control_finite :Finite machine.σ:=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- All actual Boolean data and real finite-label return alphabets are finite. -/
theorem alphabets_finite :∀k,Finite (machine.Γ k):=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackRationalNormalize
