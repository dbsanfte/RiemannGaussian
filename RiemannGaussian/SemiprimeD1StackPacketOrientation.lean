/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWordLessExecution
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
import RiemannGaussian.SemiprimeD1StackFrame
import RiemannGaussian.SemiprimeD1StackReverseWord
import RiemannGaussian.SemiprimeD1TensorTapeFieldBytecode
/-! # Actual packet orientation from two acquired colour vectors and binary index
The same fixed source executes numeric comparisons, consumes a real index bit
only on equality, and physically frames unordered coordinate fields. Its packet
key has the remaining binary index as its raw tail, without a vector terminator.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketOrientation
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace Less
export SemiprimeD1StackWordLess (Stack Label program store)
end Less
namespace F
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end F
/-- Fourteen retained inputs, physical cursors, colour words, histories and outputs. -/
inductive Aux where
  | leftInput | rightInput | indexInput | leftReader | rightReader | indexCursor
  | leftColour | rightColour | copyScratch | keyHistory | slotHistory | keyOutput | slotOutput | highOutput
  deriving DecidableEq,Repr
/-- Complete physical inventory fixed before all colour rows and indices. -/
instance :Fintype Aux:=Fintype.ofList
  [.leftInput,.rightInput,.indexInput,.leftReader,.rightReader,.indexCursor,.leftColour,.rightColour,
    .copyScratch,.keyHistory,.slotHistory,.keyOutput,.slotOutput,.highOutput] (by intro k;cases k <;> simp)
/-- All five real comparison words and fourteen physical source/logger words, without shadows. -/
abbrev Stack:=Less.Stack⊕Aux
/-- Direct distinct real comparison-bank injection. -/
def lessStack:Less.Stack→Stack:=Sum.inl
/-- Actual private physical stack. -/
def aux:Aux→Stack:=Sum.inr
/-- Real comparator input, reused only after its actual consuming return. -/
def operand (right:Bool):Stack:=lessStack (.inl (if right then .right else .left))
/-- Real difference output becomes the outer-coordinate frame buffer between comparisons. -/
def buffer:Stack:=lessStack (.inl .output)
/-- Real subtractor scratch becomes actual Field/Frame scratch between comparisons. -/
def scratch:Stack:=lessStack (.inl .scratch)
/-- Actual comparison answer, parser validity and final success word, used at disjoint stages. -/
def answer:Stack:=lessStack (.inr ())
/-- Actual private colour reader. -/
def reader (right:Bool):Stack:=aux (if right then .rightReader else .leftReader)
/-- Actual preserved parsed colour payload. -/
def colour (right:Bool):Stack:=aux (if right then .rightColour else .leftColour)
/-- Every preserving copy is a fixed finite site, not a supplied source or value. -/
inductive Copy where
  | input (part:Fin 3) | operand (backward right:Bool) | high (ordered:Bool) | highOutput | keyTail
  deriving DecidableEq,Fintype
/-- Literal preserving-copy operands; restoration scratch is a real separate physical word. -/
def copyStack (part:Copy) (k:Fin 3):Stack:=
  if k=0 then match part with
    | .input p=>if p=0 then aux .leftInput else if p=1 then aux .rightInput else aux .indexInput
    | .operand back right=>colour (if back then !right else right)
    | .high ordered=>colour ordered
    | .highOutput | .keyTail=>aux .indexCursor
  else if k=1 then match part with
    | .input p=>if p=0 then aux .leftReader else if p=1 then aux .rightReader else aux .indexCursor
    | .operand _ right=>operand right
    | .high _=>operand true
    | .highOutput=>aux .highOutput | .keyTail=>aux .keyOutput
  else aux .copyScratch
/-- Literal Field wiring consumes one actual colour frame after its real vector tag. -/
def fieldStack (right:Bool):F.Stack→Stack
  | .inl .input=>reader right | .inl .scratch=>scratch | .inl .output=>colour right | .inr _=>answer
/-- The inner frame has the chosen larger colour as its raw tail. -/
inductive Frame where | inner (ordered:Bool) | outer
  deriving DecidableEq,Fintype
/-- Actual coordinate/pair framing uses distinct physical words at every fixed site. -/
def frameStack (part:Frame) (k:Fin 3):Stack:=
  if k=0 then match part with | .inner ordered=>colour (!ordered) | .outer=>operand true
  else if k=1 then match part with | .inner _=>operand true | .outer=>buffer
  else scratch
/-- One row-fragment reverse and two actual final chronological reverses. -/
inductive Reverse where | chunk | key | slots
  deriving DecidableEq
/-- Literal complete reversal-site inventory. -/
instance :Fintype Reverse:=Fintype.ofList [.chunk,.key,.slots] (by intro k;cases k <;> simp)
/-- Literal consuming-reverse operand pairs. -/
def reverseStack (part:Reverse) (k:Fin 2):Stack:=
  if k=0 then match part with | .chunk=>buffer | .key=>aux .keyHistory | .slots=>aux .slotHistory
  else match part with | .chunk=>aux .keyHistory | .key=>aux .keyOutput | .slots=>aux .slotOutput
/-- Every actual noninput role, including all five reused comparator words, has a real rejection drain. -/
inductive Work where
  | leftOperand | rightOperand | scratch | buffer | answer | leftReader | rightReader | indexCursor
  | leftColour | rightColour | copyScratch | keyHistory | slotHistory | keyOutput | slotOutput | highOutput
  deriving DecidableEq
/-- Literal complete rejection-role inventory. -/
instance :Fintype Work:=Fintype.ofList [.leftOperand,.rightOperand,.scratch,.buffer,.answer,.leftReader,.rightReader,
  .indexCursor,.leftColour,.rightColour,.copyScratch,.keyHistory,.slotHistory,.keyOutput,.slotOutput,.highOutput]
  (by intro k;cases k <;> simp)
/-- Literal complete rejection sweep. -/
def work:Work→Stack
  | .leftOperand=>operand false | .rightOperand=>operand true | .scratch=>scratch | .buffer=>buffer | .answer=>answer
  | .leftReader=>aux .leftReader | .rightReader=>aux .rightReader | .indexCursor=>aux .indexCursor
  | .leftColour=>aux .leftColour | .rightColour=>aux .rightColour | .copyScratch=>aux .copyScratch
  | .keyHistory=>aux .keyHistory | .slotHistory=>aux .slotHistory | .keyOutput=>aux .keyOutput
  | .slotOutput=>aux .slotOutput | .highOutput=>aux .highOutput
/-- Fixed successor through all sixteen actual rejection words. -/
def nextWork:Work→Option Work
  | .leftOperand=>some .rightOperand | .rightOperand=>some .scratch | .scratch=>some .buffer
  | .buffer=>some .answer | .answer=>some .leftReader | .leftReader=>some .rightReader
  | .rightReader=>some .indexCursor | .indexCursor=>some .leftColour | .leftColour=>some .rightColour
  | .rightColour=>some .copyScratch | .copyScratch=>some .keyHistory | .keyHistory=>some .slotHistory
  | .slotHistory=>some .keyOutput | .keyOutput=>some .slotOutput | .slotOutput=>some .highOutput | .highOutput=>none
/-- All choices are fixed finite labels; no decoded colours, index, coordinate count or packet enters control. -/
inductive Control where
  | start | copyRight | copyIndex | leftTag | rightTag | rightEnd | leftEOF | rightEOF
  | parse (right:Bool) | valid (right:Bool) | copyOperand (backward right:Bool) | compare (backward:Bool)
  | compared (backward:Bool) | padding | slot (ordered bit:Bool) | copyHigh (ordered:Bool)
  | inner (ordered:Bool) | outer | reverseChunk | clearPair | clearColour (right:Bool)
  | copyHighOutput | copyKeyTail | reverseKey | reverseSlots | clearCursor | accept | reject | clear (part:Work) | rejected | done
  deriving DecidableEq,Fintype
/-- Literal fixed call-return labels for every actual helper instruction. -/
inductive Label where
  | local (pc:Control) | less (pc:Less.Label) | copier (part:Copy) (pc:Fin 9)
  | field (right:Bool) (pc:F.Label) | frame (part:Frame) (pc:Fin 11) | reverse (part:Reverse) (pc:Fin 4)
  deriving Fintype
local notation "ctl"=>Label.local
/-- One parameterless finite Boolean-stack program for the entire actual packet orientation. -/
def program:Label→C.Instruction Stack Label
  | .local .start=>.call (.copier (.input 0) 0) (ctl .copyRight)
  | .local .copyRight=>.call (.copier (.input 1) 0) (ctl .copyIndex)
  | .local .copyIndex=>.call (.copier (.input 2) 0) (ctl .leftTag)
  | .local .leftTag=>.base (.pop (reader false) (ctl .reject) (ctl .rightEnd) (ctl .rightTag))
  | .local .rightTag=>.base (.pop (reader true) (ctl .reject) (ctl .reject) (ctl (.parse false)))
  | .local .rightEnd=>.base (.pop (reader true) (ctl .reject) (ctl .leftEOF) (ctl .reject))
  | .local .leftEOF=>.base (.peek (reader false) (ctl .rightEOF) (ctl .reject) (ctl .reject))
  | .local .rightEOF=>.base (.peek (reader true) (ctl .copyHighOutput) (ctl .reject) (ctl .reject))
  | .local (.parse right)=>.call (.field right (F.active .tagPop (none,false))) (ctl (.valid right))
  | .local (.valid right)=>.base (.pop answer (ctl .reject) (ctl .reject)
      (ctl (if right then .copyOperand false false else .parse true)))
  | .local (.copyOperand backward right)=>.call (.copier (.operand backward right) 0)
      (ctl (if right then .compare backward else .copyOperand backward true))
  | .local (.compare backward)=>.call (.less .start) (ctl (.compared backward))
  | .local (.compared false)=>.base (.pop answer (ctl .reject) (ctl (.copyOperand true false)) (ctl (.slot true false)))
  | .local (.compared true)=>.base (.pop answer (ctl .reject) (ctl .padding) (ctl (.slot false true)))
  | .local .padding=>.base (.pop (aux .indexCursor) (ctl (.slot true false)) (ctl (.slot true false)) (ctl (.slot true true)))
  | .local (.slot ordered bit)=>.base (.push (aux .slotHistory) bit (ctl (.copyHigh ordered)))
  | .local (.copyHigh ordered)=>.call (.copier (.high ordered) 0) (ctl (.inner ordered))
  | .local (.inner ordered)=>.call (.frame (.inner ordered) 0) (ctl .outer)
  | .local .outer=>.call (.frame .outer 0) (ctl .reverseChunk)
  | .local .reverseChunk=>.call (.reverse .chunk 0) (ctl .clearPair)
  | .local .clearPair=>.base (.pop (operand true) (ctl (.clearColour false)) (ctl .clearPair) (ctl .clearPair))
  | .local (.clearColour right)=>.base (.pop (colour right) (ctl (if right then .leftTag else .clearColour true))
      (ctl (.clearColour right)) (ctl (.clearColour right)))
  | .local .copyHighOutput=>.call (.copier .highOutput 0) (ctl .copyKeyTail)
  | .local .copyKeyTail=>.call (.copier .keyTail 0) (ctl .reverseKey)
  | .local .reverseKey=>.call (.reverse .key 0) (ctl .reverseSlots)
  | .local .reverseSlots=>.call (.reverse .slots 0) (ctl .clearCursor)
  | .local .clearCursor=>.base (.pop (aux .indexCursor) (ctl .accept) (ctl .clearCursor) (ctl .clearCursor))
  | .local .accept=>.base (.push answer true (ctl .done))
  | .local .reject=>.base (.jump (ctl (.clear .leftOperand)))
  | .local (.clear part)=>.base (.pop (work part) (ctl (match nextWork part with | some k=>.clear k | none=>.rejected))
      (ctl (.clear part)) (ctl (.clear part)))
  | .local .rejected=>.base (.push answer false (ctl .done))
  | .local .done=>.base .halt
  | .less pc=>SemiprimeD1StackValidationLink.instruction lessStack Label.less (Less.program pc)
  | .copier part pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack part) (Label.copier part) (SemiprimeD1StackCopy.code pc)
  | .field right pc=>SemiprimeD1StackMultiplierLink.instruction (fieldStack right) (Label.field right) (F.code pc)
  | .frame part pc=>SemiprimeD1StackMultiplierLink.instruction (frameStack part) (Label.frame part) (SemiprimeD1StackFrame.code pc)
  | .reverse part pc=>SemiprimeD1StackMultiplierLink.instruction (reverseStack part) (Label.reverse part) (SemiprimeD1StackReverseWord.code pc)
/-- Only three actual physical acquired words are loaded at the source boundary. -/
def input (left right index:List Bool):Stack→List Bool:=
  Sum.elim (fun _=>[]) (fun k=>match k with | .leftInput=>left | .rightInput=>right | .indexInput=>index | _=>[])
/-- Prepared three-input actual source; no supplied colour/order/equality/index-tail/packet answer. -/
def initial (left right index:List Bool):C.State Stack Label:=⟨some (ctl .start),none,none,input left right index,[]⟩
/-- One fixed finite machine before all rows and binary index words. -/
def machine:Turing.FinTM2:=SemiprimeD1StackCalls.machine (aux .leftInput) (aux .keyOutput) (ctl .start) program
/-- All nineteen real Boolean roles, with no unused aliases. -/
theorem stack_card:Fintype.card Stack=19:=by rw [Fintype.card_sum];decide
/-- Every fixed preserving copy has distinct physical operands. -/
theorem copy_injective (part:Copy):Function.Injective (copyStack part):=by
  cases part with
  | input p=>fin_cases p <;> decide
  | operand back right=>cases back <;> cases right <;> decide
  | high ordered=>cases ordered <;> decide
  | highOutput=>decide
  | keyTail=>decide
/-- Actual parsers never alias input/output/scratch/valid words. -/
theorem field_injective (right:Bool):Function.Injective (fieldStack right):=by cases right <;> decide
/-- Both actual inner/outer frames use separate source/destination/restoration words. -/
theorem frame_injective (part:Frame):Function.Injective (frameStack part):=by cases part <;> first | cases ‹Bool› <;> decide | decide
/-- Every actual reversal consumes a separate source word. -/
theorem reverse_injective (part:Reverse):Function.Injective (reverseStack part):=by cases part <;> decide
/-- Every physical symbol alphabet, including all genuine return labels, is fixed finite. -/
theorem alphabets_finite:∀k,Finite (machine.Γ k):=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
/-- Runtime sigma contains finite control only, not a row/index/count/function operand. -/
theorem control_finite:Finite machine.σ:=SemiprimeD1StackCalls.control_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackPacketOrientation
