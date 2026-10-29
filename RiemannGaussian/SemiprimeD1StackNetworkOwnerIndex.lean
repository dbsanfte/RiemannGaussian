/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexProduct
import RiemannGaussian.SemiprimeD1StackIncrementBytecode
import RiemannGaussian.SemiprimeD1StackFrame
import RiemannGaussian.SemiprimeD1StackReverseWord

/-! # Physical network-record acquisition of the occurrence-to-owner index
Only literal vertex-record bytes and an actually acquired bounded unary left
count enter. The first leftCount records are parsed physically, including their
tables; each unary occurrence port is paired with a physically incremented
binary owner ordinal. Every table parse/drain, pair frame and reversal is paid.
The original record tape and left count are retained; the factor-record suffix
remains on the reader for the subsequent actual factor-row acquisition.
This is a generic physical source stage, not an original-N factoring theorem.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNetworkOwnerIndex
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace Field
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end Field
namespace Inc
export SemiprimeD1StackIncrementBytecode (Label code entry)
end Inc
/-- All seventeen physical words, with numeric owner ordinals stored in binary. -/
inductive Stack where
  | vertices | leftCount | reader | todo | ports | table | valid | key | owner | ownerNext
  | incrementScratch | scratch | fieldScratch | frameBuffer | frameScratch | history | output
  deriving DecidableEq,Repr
instance :Fintype Stack :=Fintype.ofList
  [.vertices,.leftCount,.reader,.todo,.ports,.table,.valid,.key,.owner,.ownerNext,
    .incrementScratch,.scratch,.fieldScratch,.frameBuffer,.frameScratch,.history,.output]
  (by intro k;cases k <;> simp)
/-- The two actual preserving-copy operand maps. -/
inductive Copy where | vertices | count deriving DecidableEq
instance :Fintype Copy :=Fintype.ofList [.vertices,.count] (by intro k;cases k <;> simp)
/-- Every copied source, target and scratch word is physically distinct. -/
def copyStack (what:Copy) (k:Fin 3) :Stack :=
  if k=0 then (if what=.vertices then .vertices else .leftCount)
  else if k=1 then (if what=.vertices then .reader else .todo) else .scratch
/-- The three actual framed fields: ports, table and one current occurrence key. -/
inductive Part where | ports | table | key deriving DecidableEq
instance :Fintype Part :=Fintype.ofList [.ports,.table,.key] (by intro k;cases k <;> simp)
/-- Port/table parsing consumes actual record bytes; port keys come from the actual port vector. -/
def fieldStack (part:Part) :Field.Stack→Stack
  | .inl .input=>if part=.key then .ports else .reader
  | .inl .scratch=>.fieldScratch
  | .inl .output=>match part with | .ports=>.ports | .table=>.table | .key=>.key
  | .inr _=>.valid
/-- Both components of the actual key/owner pair use preserving field framing. -/
inductive Frame where | value | key deriving DecidableEq
instance :Fintype Frame :=Fintype.ofList [.value,.key] (by intro k;cases k <;> simp)
/-- Owner values are binary; bounded unary port keys retain the original record ABI. -/
def frameStack (what:Frame) (k:Fin 3) :Stack :=
  if k=0 then (if what=.value then .owner else .key)
  else if k=1 then .frameBuffer else .frameScratch
/-- Actual reversals for pair history, binary-counter transfer and whole output. -/
inductive Reverse where | pair | ownerFirst | ownerSecond | finish deriving DecidableEq
instance :Fintype Reverse :=Fintype.ofList [.pair,.ownerFirst,.ownerSecond,.finish] (by intro k;cases k <;> simp)
/-- Two physical counter reversals transfer its little-endian bits without reversing their order. -/
def reverseStack (what:Reverse) (k:Fin 2) :Stack :=
  if k=0 then match what with
    | .pair=>.frameBuffer | .ownerFirst=>.ownerNext | .ownerSecond=>.incrementScratch | .finish=>.history
  else match what with
    | .pair=>.history | .ownerFirst=>.incrementScratch | .ownerSecond=>.owner | .finish=>.output
/-- Actual three-role fixed-width binary incrementer inclusion. -/
def incrementStack :SemiprimeD1TensorTapeFieldMachine.Stack→Stack
  | .input=>.owner | .scratch=>.incrementScratch | .output=>.ownerNext
/-- Literal source/count initialization, record/port loops, counter update and final return. -/
inductive Control where
  | start | zeroCount | zeroSeed | zeroLoop | zeroPush | copyCount | owners | vertexTag
  | parsePorts | portsValid | parseTable | tableValid | clearTable | portLoop | parseKey | keyValid
  | valueFrame | keyFrame | pairTag | reversePair | clearKey | increment | carry
  | ownerFirst | ownerSecond | finish | reverseOutput | done | abort
  deriving DecidableEq
instance :Fintype Control :=Fintype.ofList
  [.start,.zeroCount,.zeroSeed,.zeroLoop,.zeroPush,.copyCount,.owners,.vertexTag,
    .parsePorts,.portsValid,.parseTable,.tableValid,.clearTable,.portLoop,.parseKey,.keyValid,
    .valueFrame,.keyFrame,.pairTag,.reversePair,.clearKey,.increment,.carry,
    .ownerFirst,.ownerSecond,.finish,.reverseOutput,.done,.abort]
  (by intro k;cases k <;> simp)
/-- All actual code and return locations are fixed finite before every network. -/
inductive Label where
  | local (pc:Control) | copy (what:Copy) (pc:Fin 9) | field (part:Part) (pc:Field.Label)
  | frame (what:Frame) (pc:Fin 11) | reverse (what:Reverse) (pc:Fin 4) | increment (pc:Inc.Label)
  deriving Fintype
/-- One concrete program extracts the owner index from physical vertex bytes. -/
def program :Label→C.Instruction Stack Label
  | .local .start=>.call (.copy .vertices 0) (.local .zeroCount)
  | .local .zeroCount=>.call (.copy .count 0) (.local .zeroSeed)
  | .local .zeroSeed=>.base (.push .owner false (.local .zeroLoop))
  | .local .zeroLoop=>.base (.pop .todo (.local .copyCount) (.local .abort) (.local .zeroPush))
  | .local .zeroPush=>.base (.push .owner false (.local .zeroLoop))
  | .local .copyCount=>.call (.copy .count 0) (.local .owners)
  | .local .owners=>.base (.pop .todo (.local .finish) (.local .abort) (.local .vertexTag))
  | .local .vertexTag=>.base (.pop .reader (.local .abort) (.local .abort) (.local .parsePorts))
  | .local .parsePorts=>.call (.field .ports (Field.active .tagPop (none,false))) (.local .portsValid)
  | .local .portsValid=>.base (.pop .valid (.local .abort) (.local .abort) (.local .parseTable))
  | .local .parseTable=>.call (.field .table (Field.active .tagPop (none,false))) (.local .tableValid)
  | .local .tableValid=>.base (.pop .valid (.local .abort) (.local .abort) (.local .clearTable))
  | .local .clearTable=>.base (.pop .table (.local .portLoop) (.local .clearTable) (.local .clearTable))
  | .local .portLoop=>.base (.pop .ports (.local .abort) (.local .increment) (.local .parseKey))
  | .local .parseKey=>.call (.field .key (Field.active .tagPop (none,false))) (.local .keyValid)
  | .local .keyValid=>.base (.pop .valid (.local .abort) (.local .abort) (.local .valueFrame))
  | .local .valueFrame=>.call (.frame .value 0) (.local .keyFrame)
  | .local .keyFrame=>.call (.frame .key 0) (.local .pairTag)
  | .local .pairTag=>.base (.push .frameBuffer true (.local .reversePair))
  | .local .reversePair=>.call (.reverse .pair 0) (.local .clearKey)
  | .local .clearKey=>.base (.pop .key (.local .portLoop) (.local .clearKey) (.local .clearKey))
  | .local .increment=>.call (.increment Inc.entry) (.local .carry)
  | .local .carry=>.base (.pop .ownerNext (.local .abort) (.local .ownerFirst) (.local .abort))
  | .local .ownerFirst=>.call (.reverse .ownerFirst 0) (.local .ownerSecond)
  | .local .ownerSecond=>.call (.reverse .ownerSecond 0) (.local .owners)
  | .local .finish=>.base (.push .history false (.local .reverseOutput))
  | .local .reverseOutput=>.call (.reverse .finish 0) (.local .done)
  | .local .done|.local .abort=>.base .halt
  | .copy what pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack what) (Label.copy what)
      (SemiprimeD1StackCopy.code pc)
  | .field part pc=>SemiprimeD1StackMultiplierLink.instruction (fieldStack part) (Label.field part) (Field.code pc)
  | .frame what pc=>SemiprimeD1StackMultiplierLink.instruction (frameStack what) (Label.frame what)
      (SemiprimeD1StackFrame.code pc)
  | .reverse what pc=>SemiprimeD1StackMultiplierLink.instruction (reverseStack what) (Label.reverse what)
      (SemiprimeD1StackReverseWord.code pc)
  | .increment pc=>SemiprimeD1StackMultiplierLink.instruction incrementStack Label.increment (Inc.code pc)
/-- Actual source input has the complete record tape and acquired unary left count only. -/
def input (vertices count:List Bool) :Stack→List Bool
  | .vertices=>vertices | .leftCount=>count | _=>[]
/-- Literal source start with every dictionary, counter and work word initially empty. -/
def initial (vertices count:List Bool) :C.State Stack Label :=
  ⟨some (.local .start),none,none,input vertices count,[]⟩
/-- Fixed finite physical owner-index source; factor rows are still present on the reader at return. -/
def machine :Turing.FinTM2 :=SemiprimeD1StackCalls.machine Stack.vertices Stack.output (.local .start) program
/-- Both actual preserving-copy instances have three distinct operands. -/
theorem copy_injective (what:Copy) :Function.Injective (copyStack what) :=by cases what <;> decide
/-- Every actual field parser has four distinct physical operands. -/
theorem field_injective (part:Part) :Function.Injective (fieldStack part) :=by cases part <;> decide
/-- Both preserving pair frames have three distinct physical operands. -/
theorem frame_injective (what:Frame) :Function.Injective (frameStack what) :=by cases what <;> decide
/-- Each actual reversal has distinct source and target words. -/
theorem reverse_injective (what:Reverse) :Function.Injective (reverseStack what) :=by cases what <;> decide
/-- Actual binary increment input/scratch/output roles cannot alias. -/
theorem increment_injective :Function.Injective incrementStack :=by decide
/-- All seventeen data roles, including parsed table bytes and real binary-counter work, are counted. -/
theorem stack_card :Fintype.card Stack=17 :=by decide
/-- Only finite read flags and actual fixed real-return labels inhabit runtime control. -/
theorem control_finite :Finite machine.σ :=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- Every data/return alphabet is fixed finite before the source inputs. -/
theorem alphabets_finite :∀k,Finite (machine.Γ k) :=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackNetworkOwnerIndex
