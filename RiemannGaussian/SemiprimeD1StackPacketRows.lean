/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerLookupBounds
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
import RiemannGaussian.SemiprimeD1StackFrame
import RiemannGaussian.SemiprimeD1StackReverseWord
/-! # Actual two-ID packet colour-row reader with paired physical EOF
Only the physical joint key and acquired alphabet catalogue enter. One real
Field reads the owner ID; its actual remaining raw tail is the factor ID. Two
real preserving catalogue copies and OwnerLookup calls acquire the colour rows.
A nonempty unread catalogue suffix physically distinguishes a found empty row
from a missing ID. Paired physical EOF, never a supplied coordinate count, ends
the colour loop. Empty colour fields begin with false and remain real fields.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketRows
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace L
export SemiprimeD1StackOwnerLookup (Stack Label program)
end L
namespace F
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end F
/-- Eight actual source, payload, logger-history and chronological-output words. -/
inductive Aux where
  | key | catalogue | keyReader | leftBytes | leftHistory | rightHistory | leftOutput | rightOutput
  deriving DecidableEq,Repr
/-- Literal complete physical inventory, fixed before all keys and alphabets. -/
instance :Fintype Aux :=Fintype.ofList
  [.key,.catalogue,.keyReader,.leftBytes,.leftHistory,.rightHistory,.leftOutput,.rightOutput]
  (by intro k;cases k <;> simp)
/-- All eleven actual lookup words and eight actual reader/logger words, with no shadows. -/
abbrev Stack :=L.Stack⊕Aux
/-- Complete real lookup bank; its scratch words are reused only between actual calls. -/
def lookupStack :L.Stack→Stack :=Sum.inl
/-- Private actual physical field. -/
def aux :Aux→Stack :=Sum.inr
/-- The actual parsed owner/factor query word. -/
def query :Stack :=lookupStack (.inr .query)
/-- Actual unread lookup catalogue suffix; physical EOF detects a missing key. -/
def lookupReader :Stack :=lookupStack (.inr .reader)
/-- The second actual payload directly supplies the right raw colour-row stream. -/
def rightBytes :Stack :=lookupStack (.inr .output)
/-- Lookup comparison inputs become actual colour words only after both lookups finish. -/
def colourWord (right:Bool) :Stack :=lookupStack (if right then .inl .right else .inl .left)
/-- The old comparison output becomes the public computed success flag after all comparison calls finish. -/
def success :Stack :=lookupStack (.inl .output)
/-- Actual field/copy work is directly shared with the included lookup component. -/
def parserScratch :Stack :=lookupStack (.inr .fieldScratch)
/-- Every actual parser valid byte is physically popped. -/
def parserValid :Stack :=lookupStack (.inr .valid)
/-- Actual preserving-copy scratch. -/
def copyScratch :Stack :=lookupStack (.inr .copyScratch)
/-- The lookup discard word is an actual field-frame buffer only after lookup cleanup. -/
def frameBuffer :Stack :=lookupStack (.inr .discard)
/-- Source row bytes consumed by the paired physical field loop. -/
def rowBytes (right:Bool) :Stack :=if right then rightBytes else aux .leftBytes
/-- Real reverse-row logger histories. -/
def history (right:Bool) :Stack :=if right then aux .rightHistory else aux .leftHistory
/-- Chronological literal colour vectors. -/
def output (right:Bool) :Stack :=if right then aux .rightOutput else aux .leftOutput
/-- Four fixed preserving-copy sites, independent of every ID and row value. -/
inductive Copy where | key | catalogue | leftPayload | factor
  deriving DecidableEq
/-- Complete fixed preserving-copy site inventory. -/
instance :Fintype Copy :=Fintype.ofList [.key,.catalogue,.leftPayload,.factor] (by intro k;cases k <;> simp)
/-- Actual copy source, destination and restoration scratch. -/
def copyStack (part:Copy) (k:Fin 3) :Stack :=
  if k=0 then match part with
    | .key=>aux .key | .catalogue=>aux .catalogue | .leftPayload=>rightBytes | .factor=>aux .keyReader
  else if k=1 then match part with
    | .key=>aux .keyReader | .catalogue=>lookupReader | .leftPayload=>aux .leftBytes | .factor=>query
  else copyScratch
/-- A single actual owner-ID field and two actual colour-field parser choices. -/
inductive Field where | owner | colour (right:Bool)
  deriving DecidableEq,Fintype
/-- Exact physical Field wiring; the factor ID is already the owner's unconsumed raw tail. -/
def fieldStack (part:Field) :F.Stack→Stack
  | .inl .input=>match part with | .owner=>aux .keyReader | .colour right=>rowBytes right
  | .inl .scratch=>parserScratch
  | .inl .output=>match part with | .owner=>query | .colour right=>colourWord right
  | .inr _=>parserValid
/-- Actual preserving Frame on one raw colour word, shared empty buffer and parser scratch. -/
def frameStack (right:Bool) (k:Fin 3) :Stack :=
  if k=0 then colourWord right else if k=1 then frameBuffer else parserScratch
/-- Two row-logger reversals and two final whole-history reversals use only actual word stacks. -/
inductive Reverse where | colour (right:Bool) | finish (right:Bool)
  deriving DecidableEq,Fintype
/-- Actual reverse source and destination; no native row-order reversal is an opcode. -/
def reverseStack (part:Reverse) (k:Fin 2) :Stack :=
  if k=0 then match part with | .colour _=>frameBuffer | .finish right=>history right
  else match part with | .colour right=>history right | .finish right=>output right
/-- Every non-input physical role is visited by the literal rejection cleanup. -/
inductive Work where
  | leftWord | rightWord | unused | success | query | reader | parserScratch | valid | copyScratch | frame
  | rightBytes | keyReader | leftBytes | leftHistory | rightHistory | leftOutput | rightOutput
  deriving DecidableEq
/-- Complete static cleanup inventory, independent of all input lengths and values. -/
instance :Fintype Work :=Fintype.ofList
  [.leftWord,.rightWord,.unused,.success,.query,.reader,.parserScratch,.valid,.copyScratch,.frame,
    .rightBytes,.keyReader,.leftBytes,.leftHistory,.rightHistory,.leftOutput,.rightOutput]
  (by intro k;cases k <;> simp)
/-- Literal physical cleanup destination. -/
def workStack :Work→Stack
  | .leftWord=>colourWord false | .rightWord=>colourWord true | .unused=>lookupStack (.inl .scratch)
  | .success=>success | .query=>query | .reader=>lookupReader | .parserScratch=>parserScratch
  | .valid=>parserValid | .copyScratch=>copyScratch | .frame=>frameBuffer | .rightBytes=>rightBytes
  | .keyReader=>aux .keyReader | .leftBytes=>aux .leftBytes | .leftHistory=>aux .leftHistory
  | .rightHistory=>aux .rightHistory | .leftOutput=>aux .leftOutput | .rightOutput=>aux .rightOutput
/-- Fixed literal cleanup succession; no decoded input counter chooses a role. -/
def nextWork :Work→Option Work
  | .leftWord=>some .rightWord | .rightWord=>some .unused | .unused=>some .success | .success=>some .query
  | .query=>some .reader | .reader=>some .parserScratch | .parserScratch=>some .valid | .valid=>some .copyScratch
  | .copyScratch=>some .frame | .frame=>some .rightBytes | .rightBytes=>some .keyReader | .keyReader=>some .leftBytes
  | .leftBytes=>some .leftHistory | .leftHistory=>some .rightHistory | .rightHistory=>some .leftOutput
  | .leftOutput=>some .rightOutput | .rightOutput=>none
/-- Only fixed stages, side bits and actual parser/lookup/EOF choices occur in runtime control. -/
inductive Control where
  | start | seedRight | copyKey | parseKey | keyValid | copyMenu (right:Bool) | lookup (right:Bool)
  | lookupFound (right:Bool) | clearLookupReader (right:Bool) | copyLeft | clearLeftResult | clearQuery (right:Bool)
  | copyFactor | clearKeyReader | leftEOF | rightEOF | rightNonempty | parseColour (right:Bool)
  | colourValid (right:Bool) | tagHistory (right:Bool) | frameColour (right:Bool) | reverseColour (right:Bool)
  | clearColour (right:Bool) | reverseLeft | reverseRight | accept | reject | clear (work:Work) | rejected | done
  deriving DecidableEq,Fintype
/-- Every real lookup/parser/copy/frame/reversal return label is fixed finite before all operands. -/
inductive Label where
  | local (pc:Control) | lookupCode (pc:L.Label) | copier (part:Copy) (pc:Fin 9)
  | field (part:Field) (pc:F.Label) | frame (right:Bool) (pc:Fin 11) | reverse (part:Reverse) (pc:Fin 4)
  deriving Fintype
local notation "ctl" => Label.local
/-- One fixed literal two-input program, with no supplied row, coordinate count or presence/shape verdict. -/
def program :Label→C.Instruction Stack Label
  | .local .start=>.base (.push (output false) false (ctl .seedRight))
  | .local .seedRight=>.base (.push (output true) false (ctl .copyKey))
  | .local .copyKey=>.call (.copier .key 0) (ctl .parseKey)
  | .local .parseKey=>.call (.field .owner (F.active .tagPop (none,false))) (ctl .keyValid)
  | .local .keyValid=>.base (.pop parserValid (ctl .reject) (ctl .reject) (ctl (.copyMenu false)))
  | .local (.copyMenu right)=>.call (.copier .catalogue 0) (ctl (.lookup right))
  | .local (.lookup right)=>.call (.lookupCode .loop) (ctl (.lookupFound right))
  | .local (.lookupFound right)=>.base (.peek lookupReader (ctl .reject) (ctl (.clearLookupReader right)) (ctl (.clearLookupReader right)))
  | .local (.clearLookupReader right)=>.base (.pop lookupReader (ctl (if right then .clearQuery true else .copyLeft))
      (ctl (.clearLookupReader right)) (ctl (.clearLookupReader right)))
  | .local .copyLeft=>.call (.copier .leftPayload 0) (ctl .clearLeftResult)
  | .local .clearLeftResult=>.base (.pop rightBytes (ctl (.clearQuery false)) (ctl .clearLeftResult) (ctl .clearLeftResult))
  | .local (.clearQuery right)=>.base (.pop query (ctl (if right then .clearKeyReader else .copyFactor))
      (ctl (.clearQuery right)) (ctl (.clearQuery right)))
  | .local .copyFactor=>.call (.copier .factor 0) (ctl (.copyMenu true))
  | .local .clearKeyReader=>.base (.pop (aux .keyReader) (ctl .leftEOF) (ctl .clearKeyReader) (ctl .clearKeyReader))
  | .local .leftEOF=>.base (.peek (rowBytes false) (ctl .rightEOF) (ctl .rightNonempty) (ctl .rightNonempty))
  | .local .rightEOF=>.base (.peek (rowBytes true) (ctl .reverseLeft) (ctl .reject) (ctl .reject))
  | .local .rightNonempty=>.base (.peek (rowBytes true) (ctl .reject) (ctl (.parseColour false)) (ctl (.parseColour false)))
  | .local (.parseColour right)=>.call (.field (.colour right) (F.active .tagPop (none,false))) (ctl (.colourValid right))
  | .local (.colourValid right)=>.base (.pop parserValid (ctl .reject) (ctl .reject) (ctl (.tagHistory right)))
  | .local (.tagHistory right)=>.base (.push (history right) true (ctl (.frameColour right)))
  | .local (.frameColour right)=>.call (.frame right 0) (ctl (.reverseColour right))
  | .local (.reverseColour right)=>.call (.reverse (.colour right) 0) (ctl (.clearColour right))
  | .local (.clearColour right)=>.base (.pop (colourWord right) (ctl (if right then .leftEOF else .parseColour true))
      (ctl (.clearColour right)) (ctl (.clearColour right)))
  | .local .reverseLeft=>.call (.reverse (.finish false) 0) (ctl .reverseRight)
  | .local .reverseRight=>.call (.reverse (.finish true) 0) (ctl .accept)
  | .local .accept=>.base (.push success true (ctl .done))
  | .local .reject=>.base (.jump (ctl (.clear .leftWord)))
  | .local (.clear work)=>.base (.pop (workStack work)
      (match nextWork work with | some work=>ctl (.clear work) | none=>ctl .rejected)
      (ctl (.clear work)) (ctl (.clear work)))
  | .local .rejected=>.base (.push success false (ctl .done))
  | .local .done=>.base .halt
  | .lookupCode pc=>SemiprimeD1StackValidationLink.instruction lookupStack Label.lookupCode (L.program pc)
  | .copier part pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack part) (Label.copier part) (SemiprimeD1StackCopy.code pc)
  | .field part pc=>SemiprimeD1StackMultiplierLink.instruction (fieldStack part) (Label.field part) (F.code pc)
  | .frame right pc=>SemiprimeD1StackMultiplierLink.instruction (frameStack right) (Label.frame right) (SemiprimeD1StackFrame.code pc)
  | .reverse part pc=>SemiprimeD1StackMultiplierLink.instruction (reverseStack part) (Label.reverse part) (SemiprimeD1StackReverseWord.code pc)
/-- Exactly two acquired physical words are initialized, with every helper/result word empty. -/
def input (key catalogue:List Bool) :Stack→List Bool :=
  Sum.elim (fun _=>[]) (fun k=>match k with | .key=>key | .catalogue=>catalogue | _=>[])
/-- Actual prepared front door, without given IDs, rows, a, count, colour fields or validity answer. -/
def initial (key catalogue:List Bool) :C.State Stack Label :=⟨some (ctl .start),none,none,input key catalogue,[]⟩
/-- Fixed finite nineteen-role machine; the actual caller acquires both source words. -/
def machine :Turing.FinTM2 :=SemiprimeD1StackCalls.machine (aux .key) (output false) (ctl .start) program
/-- Every actual data role and reused helper word is counted. -/
theorem stack_card :Fintype.card Stack=19 :=by rw [Fintype.card_sum,SemiprimeD1StackOwnerLookup.stack_card];decide
/-- Every actual preserving copy uses distinct words. -/
theorem copy_injective (part:Copy) :Function.Injective (copyStack part) :=by cases part <;> decide
/-- Every actual parser source/output/scratch/valid role is distinct. -/
theorem field_injective (part:Field) :Function.Injective (fieldStack part) :=by cases part with | owner=>decide | colour b=>cases b <;> decide
/-- Every actual colour frame has separate source/buffer/scratch words. -/
theorem frame_injective (right:Bool) :Function.Injective (frameStack right) :=by cases right <;> decide
/-- Every actual logger/final reversal has separate physical source and destination. -/
theorem reverse_injective (part:Reverse) :Function.Injective (reverseStack part) :=by cases part <;> cases ‹Bool› <;> decide
/-- All alphabets, including every genuine return address, are fixed finite before the input. -/
theorem alphabets_finite :∀k,Finite (machine.Γ k) :=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
/-- Runtime control has no coordinate count, decoded ID, native row, score or getter. -/
theorem control_finite :Finite machine.σ :=SemiprimeD1StackCalls.control_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackPacketRows
