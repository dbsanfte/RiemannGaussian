/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackDividerExecution
import RiemannGaussian.SemiprimeD1StackAdderExecution
import RiemannGaussian.SemiprimeD1StackWordFitExecution
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
/-! # Physical original cancelled kernel factor
The four source words are unary a and binary t,x,y. A real binary displacement
and two real fits precede signed subtraction, stripping and restoring division.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackKernelLinear
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace D
export SemiprimeD1StackDivider (Stack Label code)
end D
namespace A
export SemiprimeD1StackAdder (Stack Label code)
end A
namespace S
export SemiprimeD1StackSubtractor (Label code)
end S
namespace F
export SemiprimeD1StackWordFit (Label program)
end F
/-- All original, acquired and transient roles outside the real divider bank. -/
inductive Aux where
  | a | t | x | y | k | center | j | displacement | alpha | content | constant
  | sign | slope | remaining | scan | scratch | buffer | valid
  deriving DecidableEq,Repr
/-- Explicit complete eighteen-role inventory. -/
instance auxFintype : Fintype Aux := Fintype.ofList
  [.a,.t,.x,.y,.k,.center,.j,.displacement,.alpha,.content,.constant,.sign,.slope,
    .remaining,.scan,.scratch,.buffer,.valid] (by intro r; cases r <;> simp)
/-- Eleven actual division fields plus eighteen source/cache/work words. -/
abbrev Stack := D.Stack ⊕ Aux
/-- Whole real divider inclusion. -/
def divider : D.Stack → Stack := Sum.inl
/-- Original/cache/private address. -/
def aux : Aux → Stack := Sum.inr
/-- Four shared real ripple fields, empty between arithmetic calls. -/
def arithmetic (r : A.Stack) : Stack := divider (.inl r)
/-- Two actual fitted destinations; the physical width is the acquired k word. -/
def fitStack (second : Bool) (r : Fin 5) : Stack :=
  if r=0 then arithmetic .output else if r=1 then aux .k else if r=2 then aux .remaining
  else if r=3 then arithmetic .scratch else aux (if second then .j else .displacement)
/-- Fixed preserving-copy call sites, independent of all source values. -/
inductive Copy where
  | aCounter | aK | centerAdd | yAdd | sum | bufferSub | xSub | tFit | centerAlpha
  | jLeft | dRight | dLeft | jRight | deltaScan | constant | alphaDividend
  | contentDivisor | quotient | alphaContent
  deriving DecidableEq
/-- Complete static copy-site inventory. -/
instance copyFintype : Fintype Copy := Fintype.ofList
  [.aCounter,.aK,.centerAdd,.yAdd,.sum,.bufferSub,.xSub,.tFit,.centerAlpha,
    .jLeft,.dRight,.dLeft,.jRight,.deltaScan,.constant,.alphaDividend,.contentDivisor,
    .quotient,.alphaContent] (by intro r; cases r <;> simp)
/-- Every copy source is a literal address. -/
def copySource : Copy → Stack
  | .aCounter | .aK => aux .a
  | .centerAdd | .centerAlpha => aux .center
  | .yAdd => aux .y
  | .sum | .deltaScan => arithmetic .output
  | .bufferSub => aux .buffer
  | .xSub => aux .x
  | .tFit => aux .t
  | .jLeft | .jRight => aux .j
  | .dRight | .dLeft => aux .displacement
  | .constant => aux .scan
  | .alphaDividend | .alphaContent => aux .alpha
  | .contentDivisor => aux .content
  | .quotient => divider (.inr .quotient)
/-- Every copy destination is a literal address. -/
def copyTarget : Copy → Stack
  | .aCounter => aux .remaining
  | .aK => aux .k
  | .centerAdd | .bufferSub | .jLeft | .dLeft => arithmetic .left
  | .yAdd | .xSub | .dRight | .jRight => arithmetic .right
  | .sum => aux .buffer
  | .tFit => arithmetic .output
  | .centerAlpha => aux .alpha
  | .deltaScan => aux .scan
  | .constant => aux .constant
  | .alphaDividend => divider (.inr .input)
  | .contentDivisor => divider (.inr .divisor)
  | .quotient => aux .slope
  | .alphaContent => aux .content
/-- Scratch is physically disjoint from every source and destination. -/
def copyStack (site : Copy) (r : Fin 3) : Stack :=
  if r=0 then copySource site else if r=1 then copyTarget site else aux .scratch
/-- Fixed finite source labels, with only actual bits entering branch control. -/
inductive Control where
  | start | seed | power | shift | copyK | addK | centerAdd | yAdd | add | sum
  | clearSum | bufferSub | xSub | displacementSub | displacementBorrow | displacementFit
  | tCopy | tFit | alphaCopy | alphaShift | normalize | dRight | firstSub | firstBorrow
  | sign (negative : Bool) | clearWrapped | dLeft | jRight | secondSub | secondBorrow
  | deltaCopy | seedContent | strip | shiftContent | restoreOne | constantCopy | clearScan | clearMagnitude
  | dividend | divisor | divide | quotient | zeroContent | zeroCopy | zeroSlope
  | clearDelta | clearBuffer | clearQuotient | clearRemainder | accept | done | abort | returning
  deriving DecidableEq,Fintype
/-- Included controls are finite before a,t,x,y and contain no arithmetic answer. -/
inductive Label where
  | local (pc : Control) | copy (site : Copy) (pc : Fin 9)
  | add (pc : A.Label) | subtract (pc : S.Label) | divide (pc : D.Label)
  | fit (second : Bool) (pc : F.Label) | drain (role : Stack)
  deriving DecidableEq,Fintype
local notation "ctl" => Label.local
/-- One literal source; all arithmetic and fitting use actual included programs. -/
def program : Label → C.Instruction Stack Label
  | .local .start => .call (.copy .aCounter 0) (ctl .seed)
  | .local .seed => .base (.push (aux .center) true (ctl .power))
  | .local .power => .base (.pop (aux .remaining) (ctl .copyK) (ctl .shift) (ctl .shift))
  | .local .shift => .base (.push (aux .center) false (ctl .power))
  | .local .copyK => .call (.copy .aK 0) (ctl .addK)
  | .local .addK => .base (.push (aux .k) true (ctl .centerAdd))
  | .local .centerAdd => .call (.copy .centerAdd 0) (ctl .yAdd)
  | .local .yAdd => .call (.copy .yAdd 0) (ctl .add)
  | .local .add => .call (.add (.start false)) (ctl .sum)
  | .local .sum => .call (.copy .sum 0) (ctl .clearSum)
  | .local .clearSum => .call (.drain (arithmetic .output)) (ctl .bufferSub)
  | .local .bufferSub => .call (.copy .bufferSub 0) (ctl .xSub)
  | .local .xSub => .call (.copy .xSub 0) (ctl .displacementSub)
  | .local .displacementSub => .call (.subtract (.start false)) (ctl .displacementBorrow)
  | .local .displacementBorrow => .base (.pop (arithmetic .output) (ctl .abort) (ctl .displacementFit) (ctl .abort))
  | .local .displacementFit => .call (.fit false .start) (ctl .tCopy)
  | .local .tCopy => .call (.copy .tFit 0) (ctl .tFit)
  | .local .tFit => .call (.fit true .start) (ctl .alphaCopy)
  | .local .alphaCopy => .call (.copy .centerAlpha 0) (ctl .alphaShift)
  | .local .alphaShift => .base (.push (aux .alpha) false (ctl .normalize))
  | .local .normalize => .call (.copy .jLeft 0) (ctl .dRight)
  | .local .dRight => .call (.copy .dRight 0) (ctl .firstSub)
  | .local .firstSub => .call (.subtract (.start false)) (ctl .firstBorrow)
  | .local .firstBorrow => .base (.pop (arithmetic .output) (ctl .abort) (ctl (.sign false)) (ctl (.sign true)))
  | .local (.sign negative) => .base (.push (aux .sign) negative (ctl (if negative then .clearWrapped else .deltaCopy)))
  | .local .clearWrapped => .call (.drain (arithmetic .output)) (ctl .dLeft)
  | .local .dLeft => .call (.copy .dLeft 0) (ctl .jRight)
  | .local .jRight => .call (.copy .jRight 0) (ctl .secondSub)
  | .local .secondSub => .call (.subtract (.start false)) (ctl .secondBorrow)
  | .local .secondBorrow => .base (.pop (arithmetic .output) (ctl .abort) (ctl .deltaCopy) (ctl .abort))
  | .local .deltaCopy => .call (.copy .deltaScan 0) (ctl .seedContent)
  | .local .seedContent => .base (.push (aux .content) true (ctl .strip))
  | .local .strip => .base (.pop (aux .scan) (ctl .zeroContent) (ctl .shiftContent) (ctl .restoreOne))
  | .local .shiftContent => .base (.push (aux .content) false (ctl .strip))
  | .local .restoreOne => .base (.push (aux .scan) true (ctl .constantCopy))
  | .local .constantCopy => .call (.copy .constant 0) (ctl .clearScan)
  | .local .clearScan => .call (.drain (aux .scan)) (ctl .clearMagnitude)
  | .local .clearMagnitude => .call (.drain (arithmetic .output)) (ctl .dividend)
  | .local .dividend => .call (.copy .alphaDividend 0) (ctl .divisor)
  | .local .divisor => .call (.copy .contentDivisor 0) (ctl .divide)
  | .local .divide => .call (.divide (.control .start)) (ctl .quotient)
  | .local .quotient => .call (.copy .quotient 0) (ctl .clearDelta)
  | .local .zeroContent => .call (.drain (aux .content)) (ctl .zeroCopy)
  | .local .zeroCopy => .call (.copy .alphaContent 0) (ctl .zeroSlope)
  | .local .zeroSlope => .base (.push (aux .slope) true (ctl .clearDelta))
  | .local .clearDelta => .call (.drain (arithmetic .output)) (ctl .clearBuffer)
  | .local .clearBuffer => .call (.drain (aux .buffer)) (ctl .clearQuotient)
  | .local .clearQuotient => .call (.drain (divider (.inr .quotient))) (ctl .clearRemainder)
  | .local .clearRemainder => .call (.drain (divider (.inr .remainder))) (ctl .accept)
  | .local .accept => .base (.push (aux .valid) true (ctl .done))
  | .local .done | .local .abort => .base .halt
  | .local .returning => .ret
  | .drain role => .base (.pop role (ctl .returning) (.drain role) (.drain role))
  | .copy site pc => SemiprimeD1StackMultiplierLink.instruction (copyStack site) (Label.copy site)
      (SemiprimeD1StackCopy.code pc)
  | .add pc => SemiprimeD1StackMultiplierLink.instruction arithmetic Label.add (A.code pc)
  | .subtract pc => SemiprimeD1StackMultiplierLink.instruction arithmetic Label.subtract (S.code pc)
  | .divide pc => SemiprimeD1StackValidationLink.instruction divider Label.divide (D.code pc)
  | .fit second pc => SemiprimeD1StackValidationLink.instruction (fitStack second) (Label.fit second) (F.program pc)
/-- Only the four original physical words are initially populated. -/
def input (a t x y : List Bool) : Stack → List Bool := fun r =>
  if r=aux .a then a else if r=aux .t then t else if r=aux .x then x else if r=aux .y then y else []
/-- Honest prepared four-word source, with flags and real return frames empty. -/
def initial (a t x y : List Bool) : C.State Stack Label :=
  ⟨some (ctl .start),none,none,input a t x y,[]⟩
/-- One fixed finite machine, with binary arithmetic words never expanded to unary. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine (aux .a) (aux .slope) (ctl .start) program
/-- Every actual role, including all shared divider fields, is counted. -/
theorem stack_card : Fintype.card Stack=29 := by decide
/-- All arithmetic operands occupy distinct real fields. -/
theorem arithmetic_injective : Function.Injective arithmetic := fun _ _ h => Sum.inl_injective (Sum.inl_injective h)
/-- Each real preserving copy has distinct physical operands. -/
theorem copy_injective (site : Copy) : Function.Injective (copyStack site) := by cases site <;> decide
/-- Both real fitting maps have five distinct physical fields. -/
theorem fit_injective (second : Bool) : Function.Injective (fitStack second) := by cases second <;> decide
/-- Runtime control is fixed finite before the four original operands. -/
theorem control_finite : Finite machine.σ := SemiprimeD1StackCalls.control_finite _ _ _ _
/-- Every data alphabet and the actual return alphabet is fixed finite. -/
theorem alphabets_finite (r : machine.K) : Finite (machine.Γ r) :=
  SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _ r
end RiemannGaussian.SemiprimeD1StackKernelLinear
