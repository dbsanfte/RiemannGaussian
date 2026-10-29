/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexPrimitives
import RiemannGaussian.SemiprimeD1StackNetworkRowsEncoding
import RiemannGaussian.SemiprimeD1StackReduceExecution
/-! # Literal original owner/factor namespace keys from actual acquired rows
Only the actual nested binary-owner row tape and actual unary n enter.
A real preliminary row scan counts every factor and allocates one counter
bit per factor, including empty factors. Actual n markers allocate the
remaining counter bits and drive n real increments. A second real scan
normalizes actual owner words, copies/normalizes the current n+f counter,
and logs one pair per occurrence in original factor/local-slot order.
All keys are binary; only bounded dimensions and F/M tallies are unary.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceOccurrences
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace Field
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end Field
namespace Inc
export SemiprimeD1StackIncrementBytecode (Label code entry)
end Inc
namespace Reduce
export SemiprimeD1StackReduce (Label code)
export SemiprimeD1StackAdder (Stack)
end Reduce
/-- Every actual retained input, parser/counter/normalizer/logger word and physical tally. -/
inductive Stack where
  | rows | number | reader | row | word | todo | counter | next | incrementScratch
  | ownerKey | factorKey | fieldScratch | valid | copyScratch | normScratch
  | frameBuffer | frameScratch | history | output | factors | occurrences
  deriving DecidableEq,Repr
instance :Fintype Stack :=Fintype.ofList
  [.rows,.number,.reader,.row,.word,.todo,.counter,.next,.incrementScratch,.ownerKey,.factorKey,
    .fieldScratch,.valid,.copyScratch,.normScratch,.frameBuffer,.frameScratch,.history,.output,.factors,.occurrences]
  (by intro k;cases k <;> simp)
/-- The three actual preserving-copy operand choices. -/
inductive Copy where | number | rows | factor deriving DecidableEq
instance :Fintype Copy :=Fintype.ofList [.number,.rows,.factor] (by intro k;cases k <;> simp)
/-- Every source/destination/scratch is a real separate Boolean word. -/
def copyStack (part:Copy) (k:Fin 3) :Stack :=
  if k=0 then match part with | .number=>.number | .rows=>.rows | .factor=>.counter
  else if k=1 then match part with | .number=>.todo | .rows=>.reader | .factor=>.word
  else .copyScratch
/-- Outer row fields and inner binary-owner fields are physically parsed separately. -/
inductive Part where | row | owner deriving DecidableEq
instance :Fintype Part :=Fintype.ofList [.row,.owner] (by intro k;cases k <;> simp)
/-- Actual parser operands; the same real scratch and validity word are clear between fields. -/
def fieldStack (part:Part) :Field.Stack→Stack
  | .inl .input=>match part with | .row=>.reader | .owner=>.row
  | .inl .scratch=>.fieldScratch
  | .inl .output=>match part with | .row=>.row | .owner=>.word
  | .inr _=>.valid
/-- Two actual binary namespace-key normalization destinations. -/
inductive Trim where | factor | owner deriving DecidableEq
instance :Fintype Trim :=Fintype.ofList [.factor,.owner] (by intro k;cases k <;> simp)
/-- All four reducer operands exist; the actual trim entry starts with its unused left/right operands empty. -/
def trimStack (part:Trim) :Reduce.Stack→Stack
  | .left=>.fieldScratch | .right=>.copyScratch | .scratch=>.normScratch
  | .output=>match part with | .factor=>.factorKey | .owner=>.ownerKey
/-- Literal actual counter initialization and per-factor successors. -/
inductive Counter where | initialize | factor deriving DecidableEq
instance :Fintype Counter :=Fintype.ofList [.initialize,.factor] (by intro k;cases k <;> simp)
/-- Every real increment consumes the actual padded binary counter, with separate carry/scratch words. -/
def incrementStack :SemiprimeD1TensorTapeFieldMachine.Stack→Stack
  | .input=>.counter | .scratch=>.incrementScratch | .output=>.next
/-- Actual normalization, counter transfer, pair and final reversals. -/
inductive Reverse where | normalize | counterFirst | counterSecond | pair | output deriving DecidableEq
instance :Fintype Reverse :=Fintype.ofList [.normalize,.counterFirst,.counterSecond,.pair,.output] (by intro k;cases k <;> simp)
/-- Every actual reversal reads/writes distinct real words. -/
def reverseStack (part:Reverse) (k:Fin 2) :Stack :=
  if k=0 then match part with
    | .normalize=>.word | .counterFirst=>.next | .counterSecond=>.incrementScratch | .pair=>.frameBuffer | .output=>.history
  else match part with
    | .normalize=>.normScratch | .counterFirst=>.incrementScratch | .counterSecond=>.counter | .pair=>.history | .output=>.output
/-- Real preserving frames for both binary namespace keys. -/
inductive Frame where | factor | owner deriving DecidableEq
instance :Fintype Frame :=Fintype.ofList [.factor,.owner] (by intro k;cases k <;> simp)
/-- The acquired factor key is framed first, then the actual owner key prepends its field. -/
def frameStack (part:Frame) (k:Fin 3) :Stack :=
  if k=0 then match part with | .factor=>.factorKey | .owner=>.ownerKey
  else if k=1 then .frameBuffer else .frameScratch
/-- Every source/scan/counter/normalizer/logging decision is a fixed finite phase. -/
inductive Control where
  | start | seedZero | widthLoop | widthPush | preCopy | preTag | preField | preValid | preDrain | prePushBit | preCount
  | copyInit | initLoop | increment (part:Counter) | carry (part:Counter)
  | counterFirst (part:Counter) | counterSecond (part:Counter) | afterIncrement (part:Counter)
  | mainCopy | factorTag | rowField | rowValid | copyFactor | normalizeReverse (part:Trim) | normalize (part:Trim)
  | ownerTag | ownerField | ownerValid | frameFactor | frameOwner | pairTag | pairReverse | clearOwner | countOccurrence
  | clearFactor | finishSeed | outputReverse | clearCounter | done | abort
  deriving DecidableEq,Fintype
/-- All actual return labels are fixed finite before n, F, M and every acquired row. -/
inductive Label where
  | local (pc:Control) | copy (part:Copy) (pc:Fin 9) | field (part:Part) (pc:Field.Label)
  | trim (part:Trim) (pc:Reduce.Label) | increment (pc:Inc.Label)
  | reverse (part:Reverse) (pc:Fin 4) | frame (part:Frame) (pc:Fin 11)
  deriving Fintype
local notation "ctl" => Label.local
/-- One fixed actual source program with no numeric/key/row/arity/owner/count/clock callback operand. -/
def program :Label→C.Instruction Stack Label
  | .local .start=>.call (.copy .number 0) (ctl .seedZero)
  | .local .seedZero=>.base (.push .counter false (ctl .widthLoop))
  | .local .widthLoop=>.base (.pop .todo (ctl .preCopy) (ctl .abort) (ctl .widthPush))
  | .local .widthPush=>.base (.push .counter false (ctl .widthLoop))
  | .local .preCopy=>.call (.copy .rows 0) (ctl .preTag)
  | .local .preTag=>.base (.pop .reader (ctl .abort) (ctl .copyInit) (ctl .preField))
  | .local .preField=>.call (.field .row (Field.active .tagPop (none,false))) (ctl .preValid)
  | .local .preValid=>.base (.pop .valid (ctl .abort) (ctl .abort) (ctl .preDrain))
  | .local .preDrain=>.base (.pop .row (ctl .prePushBit) (ctl .preDrain) (ctl .preDrain))
  | .local .prePushBit=>.base (.push .counter false (ctl .preCount))
  | .local .preCount=>.base (.push .factors true (ctl .preTag))
  | .local .copyInit=>.call (.copy .number 0) (ctl .initLoop)
  | .local .initLoop=>.base (.pop .todo (ctl .mainCopy) (ctl .abort) (ctl (.increment .initialize)))
  | .local (.increment part)=>.call (.increment Inc.entry) (ctl (.carry part))
  | .local (.carry part)=>.base (.pop .next (ctl .abort) (ctl (.counterFirst part)) (ctl .abort))
  | .local (.counterFirst part)=>.call (.reverse .counterFirst 0) (ctl (.counterSecond part))
  | .local (.counterSecond part)=>.call (.reverse .counterSecond 0) (ctl (.afterIncrement part))
  | .local (.afterIncrement .initialize)=>.base (.jump (ctl .initLoop))
  | .local (.afterIncrement .factor)=>.base (.jump (ctl .factorTag))
  | .local .mainCopy=>.call (.copy .rows 0) (ctl .factorTag)
  | .local .factorTag=>.base (.pop .reader (ctl .abort) (ctl .finishSeed) (ctl .rowField))
  | .local .rowField=>.call (.field .row (Field.active .tagPop (none,false))) (ctl .rowValid)
  | .local .rowValid=>.base (.pop .valid (ctl .abort) (ctl .abort) (ctl .copyFactor))
  | .local .copyFactor=>.call (.copy .factor 0) (ctl (.normalizeReverse .factor))
  | .local (.normalizeReverse part)=>.call (.reverse .normalize 0) (ctl (.normalize part))
  | .local (.normalize part)=>.call (.trim part .trim) (match part with | .factor=>ctl .ownerTag | .owner=>ctl .frameFactor)
  | .local .ownerTag=>.base (.pop .row (ctl .abort) (ctl .clearFactor) (ctl .ownerField))
  | .local .ownerField=>.call (.field .owner (Field.active .tagPop (none,false))) (ctl .ownerValid)
  | .local .ownerValid=>.base (.pop .valid (ctl .abort) (ctl .abort) (ctl (.normalizeReverse .owner)))
  | .local .frameFactor=>.call (.frame .factor 0) (ctl .frameOwner)
  | .local .frameOwner=>.call (.frame .owner 0) (ctl .pairTag)
  | .local .pairTag=>.base (.push .frameBuffer true (ctl .pairReverse))
  | .local .pairReverse=>.call (.reverse .pair 0) (ctl .clearOwner)
  | .local .clearOwner=>.base (.pop .ownerKey (ctl .countOccurrence) (ctl .clearOwner) (ctl .clearOwner))
  | .local .countOccurrence=>.base (.push .occurrences true (ctl .ownerTag))
  | .local .clearFactor=>.base (.pop .factorKey (ctl (.increment .factor)) (ctl .clearFactor) (ctl .clearFactor))
  | .local .finishSeed=>.base (.push .output false (ctl .outputReverse))
  | .local .outputReverse=>.call (.reverse .output 0) (ctl .clearCounter)
  | .local .clearCounter=>.base (.pop .counter (ctl .done) (ctl .clearCounter) (ctl .clearCounter))
  | .local .done|.local .abort=>.base .halt
  | .copy part pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack part) (Label.copy part) (SemiprimeD1StackCopy.code pc)
  | .field part pc=>SemiprimeD1StackMultiplierLink.instruction (fieldStack part) (Label.field part) (Field.code pc)
  | .trim part pc=>SemiprimeD1StackMultiplierLink.instruction (trimStack part) (Label.trim part) (Reduce.code pc)
  | .increment pc=>SemiprimeD1StackMultiplierLink.instruction incrementStack Label.increment (Inc.code pc)
  | .reverse part pc=>SemiprimeD1StackMultiplierLink.instruction (reverseStack part) (Label.reverse part) (SemiprimeD1StackReverseWord.code pc)
  | .frame part pc=>SemiprimeD1StackMultiplierLink.instruction (frameStack part) (Label.frame part) (SemiprimeD1StackFrame.code pc)
/-- Exactly two actual physical operands; every derived key/count/work word is initially empty. -/
def input (rows number:List Bool) :Stack→List Bool :=fun k=>if k=.rows then rows else if k=.number then number else []
/-- Whole actual prepared row/count source, before any count/width/key acquisition. -/
def initial (rows number:List Bool) :C.State Stack Label :=⟨some (ctl .start),none,none,input rows number,[]⟩
/-- One fixed finite machine; original-N composition must supply the second actually acquired operand. -/
def machine :Turing.FinTM2 :=SemiprimeD1StackCalls.machine Stack.rows Stack.output (ctl .start) program
/-- All preserving-copy operands are distinct. -/
theorem copy_injective (part:Copy) :Function.Injective (copyStack part) :=by cases part <;> decide
/-- Every actual field input/output/scratch/valid role is distinct. -/
theorem field_injective (part:Part) :Function.Injective (fieldStack part) :=by cases part <;> decide
/-- Every real four-role trim map is injective, including its empty unused operands. -/
theorem trim_injective (part:Trim) :Function.Injective (trimStack part) :=by cases part <;> decide
/-- The actual increment has separate input/scratch/output words. -/
theorem increment_injective :Function.Injective incrementStack :=by decide
/-- Every actual two-word reversal has distinct operands. -/
theorem reverse_injective (part:Reverse) :Function.Injective (reverseStack part) :=by cases part <;> decide
/-- Both actual binary frames have distinct source/output/restoration scratch. -/
theorem frame_injective (part:Frame) :Function.Injective (frameStack part) :=by cases part <;> decide
/-- Every one of the21actual physical words is included, with all source/parser/counter/cache/helper roles. -/
theorem stack_card :Fintype.card Stack=21 :=by decide
/-- Runtime control contains no Nat/List/arity/row/owner/evaluator or advised key/count/clock. -/
theorem control_finite :Finite machine.σ :=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- All21data and real return alphabets are fixed finite before the input family. -/
theorem alphabets_finite :∀k,Finite (machine.Γ k) :=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackSourceOccurrences
