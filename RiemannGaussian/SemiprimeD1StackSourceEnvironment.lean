/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerLookupBounds
import RiemannGaussian.SemiprimeD1StackValidationLink
import RiemannGaussian.SemiprimeD1StackIncrementBytecode
import RiemannGaussian.SemiprimeD1StackReduceExecution
import RiemannGaussian.SemiprimeD1StackFrame
import RiemannGaussian.SemiprimeD1StackReverseWord
/-! # Actual prefix dictionary, compact successor and preserving marked-ID lookup
The one finite source accepts actual Boolean words only. Its whole-prefix entry
retains the newest-first prefix, physically reverses the field order, and extends
its actual compact key once per parsed oldest-first ID. Stored true markers
separate a fixed zero ID from a missing key. Missing denotes free only under the
original valid-key/remaining-prefix invariant, never for arbitrary key words.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceEnvironment
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace L
export SemiprimeD1StackOwnerLookup (Stack Label program data records)
end L
namespace R
export SemiprimeD1StackReduce (Label code)
export SemiprimeD1StackAdder (Stack)
end R
namespace I
export SemiprimeD1StackIncrementBytecode (Label code entry)
export SemiprimeD1TensorTapeFieldMachine (Stack)
end I
namespace Field
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end Field
/-- Retained prefix environment and all private physical acquisition words. -/
inductive Aux where
  | dictionary | nextKey | chosenID | markedValue | copyWork | copyScratch | trimScratch
  | frameScratch | incNext | incScratch | found | prefix | reader | reversedPrefix
  deriving DecidableEq,Repr
instance :Fintype Aux :=Fintype.ofList
  [.dictionary,.nextKey,.chosenID,.markedValue,.copyWork,.copyScratch,.trimScratch,
    .frameScratch,.incNext,.incScratch,.found,.prefix,.reader,.reversedPrefix]
  (by intro k;cases k <;> simp)
/-- All eleven actual lookup roles and fourteen caller words, with no unused alias shadow. -/
abbrev Stack :=L.Stack⊕Aux
/-- Real lookup bank; query and returned candidate ID are directly its existing physical operands. -/
def lookupStack :L.Stack→Stack :=Sum.inl
/-- Every private prefix/key/normalization/flag word has a fixed physical address. -/
def aux :Aux→Stack :=Sum.inr
/-- Retained actual binary variable query, allowing high-zero padding. -/
def query :Stack :=lookupStack (.inr .query)
/-- Actual returned compact candidate ID; fixed zero and missing both have empty ID but different found flags. -/
def output :Stack :=lookupStack (.inr .output)
/-- Three literal preserving-copy sites. -/
inductive Copy where | prefix | chosen | dictionary deriving DecidableEq
instance :Fintype Copy :=Fintype.ofList [.prefix,.chosen,.dictionary] (by intro k;cases k <;> simp)
/-- Actual copy source/destination/scratch addresses, independent of every word value. -/
def copyStack (part:Copy) (k:Fin 3) :Stack :=
  if k=0 then match part with | .prefix=>aux .prefix | .chosen=>aux .chosenID | .dictionary=>aux .dictionary
  else if k=1 then match part with | .prefix=>aux .reader | .chosen=>aux .copyWork | .dictionary=>lookupStack (.inr .reader)
  else aux .copyScratch
/-- Both stored fields and the actual prefix-field reversal use real preserving Frame. -/
inductive Frame where | value | key | prefix deriving DecidableEq
instance :Fintype Frame :=Fintype.ofList [.value,.key,.prefix] (by intro k;cases k <;> simp)
/-- Frame appends the existing physical dictionary/vector tail instead of copying an encoded answer. -/
def frameStack (part:Frame) (k:Fin 3) :Stack :=
  if k=0 then match part with | .value=>aux .markedValue | .key=>aux .nextKey | .prefix=>aux .chosenID
  else if k=1 then if part=.prefix then aux .reversedPrefix else aux .dictionary
  else aux .frameScratch
/-- Four actual word-transfer/reversal sites; two transfers reverse the outer prefix order physically. -/
inductive Reverse where | chosen | counter | streamFirst | streamSecond deriving DecidableEq
instance :Fintype Reverse :=Fintype.ofList [.chosen,.counter,.streamFirst,.streamSecond] (by intro k;cases k <;> simp)
/-- Static source/destination pair for each literal reversal. -/
def reverseStack (part:Reverse) (k:Fin 2) :Stack :=
  if k=0 then match part with
    | .chosen|.streamSecond=>aux .copyWork | .counter=>aux .incNext | .streamFirst=>aux .reversedPrefix
  else match part with
    | .chosen|.counter=>aux .trimScratch | .streamFirst=>aux .copyWork | .streamSecond=>aux .reader
/-- The selected ID and physically incremented key each execute actual high-zero normalization. -/
inductive Trim where | chosen | counter deriving DecidableEq
instance :Fintype Trim :=Fintype.ofList [.chosen,.counter] (by intro k;cases k <;> simp)
/-- Reducer left/right words are already physically clear at every actual trim call. -/
def trimStack (part:Trim) :R.Stack→Stack
  | .left=>aux .copyWork | .right=>aux .frameScratch | .scratch=>aux .trimScratch
  | .output=>if part=.chosen then aux .markedValue else aux .nextKey
/-- The real incrementer consumes the actual current key and exposes its physical overflow prefix. -/
def incrementStack :I.Stack→Stack
  | .input=>aux .nextKey | .scratch=>aux .incScratch | .output=>aux .incNext
/-- Prefix ID parsing consumes actual fields and actual validity flags. -/
def fieldStack :Field.Stack→Stack
  | .inl .input=>aux .reader | .inl .scratch=>lookupStack (.inr .fieldScratch)
  | .inl .output=>aux .chosenID | .inr _=>lookupStack (.inr .valid)
/-- Only literal entry modes, finite carry bits and real return labels occur in source control. -/
inductive Control where
  | acquire | initialize | extend | lookup | done | abort | resume
  | copyPrefix | seedReverse | readNew | parseNew | newParsed | framePrefix | newTag | clearNew | newEOF
  | streamFirst | streamSecond | readOld | parseOld | oldParsed | extendPrefix | clearOld | oldEOF
  | reverseChosen | trimChosen | tagMarked | frameValue | frameKey | rowTag | increment | popOverflow
  | reverseCounter (carry:Bool) | counterCarry (carry:Bool) | trimCounter | clearMarked
  | lookupCall | readResult | missing | present | clearReader
  deriving DecidableEq
instance :Fintype Control :=Fintype.ofList
  [.acquire,.initialize,.extend,.lookup,.done,.abort,.resume,.copyPrefix,.seedReverse,.readNew,.parseNew,.newParsed,
    .framePrefix,.newTag,.clearNew,.newEOF,.streamFirst,.streamSecond,.readOld,.parseOld,.oldParsed,
    .extendPrefix,.clearOld,.oldEOF,.reverseChosen,.trimChosen,.tagMarked,.frameValue,.frameKey,.rowTag,
    .increment,.popOverflow,.reverseCounter false,.reverseCounter true,.counterCarry false,.counterCarry true,
    .trimCounter,.clearMarked,.lookupCall,.readResult,.missing,.present,.clearReader]
  (by intro k;cases k <;> simp)
/-- All included fixed finite source labels are chosen before any prefix, key, candidate ID or N. -/
inductive Label where
  | local (pc:Control) | lookupCode (pc:L.Label) | copier (part:Copy) (pc:Fin 9)
  | framer (part:Frame) (pc:Fin 11) | reversal (part:Reverse) (pc:Fin 4)
  | reducer (part:Trim) (pc:R.Label) | incrementCode (pc:I.Label) | parser (pc:Field.Label)
  deriving Fintype
local notation "ctl" => Label.local
/-- One parameterless finite source; all arithmetic, parsing, normalization and dictionary bytes are physically executed. -/
def program :Label→C.Instruction Stack Label
  | .local .acquire=>.call (ctl .initialize) (ctl .copyPrefix)
  | .local .initialize=>.base (.push (aux .dictionary) false (ctl .resume))
  | .local .copyPrefix=>.call (.copier .prefix 0) (ctl .seedReverse)
  | .local .seedReverse=>.base (.push (aux .reversedPrefix) false (ctl .readNew))
  | .local .readNew=>.base (.pop (aux .reader) (ctl .abort) (ctl .newEOF) (ctl .parseNew))
  | .local .parseNew=>.call (.parser (Field.active .tagPop (none,false))) (ctl .newParsed)
  | .local .newParsed=>.base (.pop (lookupStack (.inr .valid)) (ctl .abort) (ctl .abort) (ctl .framePrefix))
  | .local .framePrefix=>.call (.framer .prefix 0) (ctl .newTag)
  | .local .newTag=>.base (.push (aux .reversedPrefix) true (ctl .clearNew))
  | .local .clearNew=>.base (.pop (aux .chosenID) (ctl .readNew) (ctl .clearNew) (ctl .clearNew))
  | .local .newEOF=>.base (.peek (aux .reader) (ctl .streamFirst) (ctl .abort) (ctl .abort))
  | .local .streamFirst=>.call (.reversal .streamFirst 0) (ctl .streamSecond)
  | .local .streamSecond=>.call (.reversal .streamSecond 0) (ctl .readOld)
  | .local .readOld=>.base (.pop (aux .reader) (ctl .abort) (ctl .oldEOF) (ctl .parseOld))
  | .local .parseOld=>.call (.parser (Field.active .tagPop (none,false))) (ctl .oldParsed)
  | .local .oldParsed=>.base (.pop (lookupStack (.inr .valid)) (ctl .abort) (ctl .abort) (ctl .extendPrefix))
  | .local .extendPrefix=>.call (ctl .extend) (ctl .clearOld)
  | .local .clearOld=>.base (.pop (aux .chosenID) (ctl .readOld) (ctl .clearOld) (ctl .clearOld))
  | .local .oldEOF=>.base (.peek (aux .reader) (ctl .done) (ctl .abort) (ctl .abort))
  | .local .extend=>.call (.copier .chosen 0) (ctl .reverseChosen)
  | .local .reverseChosen=>.call (.reversal .chosen 0) (ctl .trimChosen)
  | .local .trimChosen=>.call (.reducer .chosen .trim) (ctl .tagMarked)
  | .local .tagMarked=>.base (.push (aux .markedValue) true (ctl .frameValue))
  | .local .frameValue=>.call (.framer .value 0) (ctl .frameKey)
  | .local .frameKey=>.call (.framer .key 0) (ctl .rowTag)
  | .local .rowTag=>.base (.push (aux .dictionary) true (ctl .increment))
  | .local .increment=>.call (.incrementCode I.entry) (ctl .popOverflow)
  | .local .popOverflow=>.base (.pop (aux .incNext) (ctl .abort) (ctl (.reverseCounter false)) (ctl (.reverseCounter true)))
  | .local (.reverseCounter carry)=>.call (.reversal .counter 0) (ctl (.counterCarry carry))
  | .local (.counterCarry carry)=>if carry then .base (.push (aux .trimScratch) true (ctl .trimCounter))
      else .base (.jump (ctl .trimCounter))
  | .local .trimCounter=>.call (.reducer .counter .trim) (ctl .clearMarked)
  | .local .clearMarked=>.base (.pop (aux .markedValue) (ctl .resume) (ctl .clearMarked) (ctl .clearMarked))
  | .local .lookup=>.call (.copier .dictionary 0) (ctl .lookupCall)
  | .local .lookupCall=>.call (.lookupCode .loop) (ctl .readResult)
  | .local .readResult=>.base (.pop output (ctl .missing) (ctl .abort) (ctl .present))
  | .local .missing=>.base (.push (aux .found) false (ctl .clearReader))
  | .local .present=>.base (.push (aux .found) true (ctl .clearReader))
  | .local .clearReader=>.base (.pop (lookupStack (.inr .reader)) (ctl .done) (ctl .clearReader) (ctl .clearReader))
  | .local .resume=>.ret
  | .local .done | .local .abort=>.base .halt
  | .lookupCode pc=>SemiprimeD1StackValidationLink.instruction lookupStack Label.lookupCode (L.program pc)
  | .copier part pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack part) (Label.copier part) (SemiprimeD1StackCopy.code pc)
  | .framer part pc=>SemiprimeD1StackMultiplierLink.instruction (frameStack part) (Label.framer part) (SemiprimeD1StackFrame.code pc)
  | .reversal part pc=>SemiprimeD1StackMultiplierLink.instruction (reverseStack part) (Label.reversal part) (SemiprimeD1StackReverseWord.code pc)
  | .reducer part pc=>SemiprimeD1StackMultiplierLink.instruction (trimStack part) (Label.reducer part) (R.code pc)
  | .incrementCode pc=>SemiprimeD1StackMultiplierLink.instruction incrementStack Label.incrementCode (I.code pc)
  | .parser pc=>SemiprimeD1StackMultiplierLink.instruction fieldStack Label.parser (Field.code pc)
/-- Literal whole-prefix input initializes just its actual encoded newest-first ID vector. -/
def input (prefixBits:List Bool) :Stack→List Bool :=Function.update (fun _=>[]) (aux .prefix) prefixBits
/-- Genuine one-word prefix entry; no key/count/dictionary/environment/clock is supplied. -/
def initial (prefixBits:List Bool) :C.State Stack Label :=⟨some (ctl .acquire),none,none,input prefixBits,[]⟩
/-- One fixed finite twenty-five-word machine. Other finite entries support retained-cache operations. -/
def machine :Turing.FinTM2 :=SemiprimeD1StackCalls.machine (aux .prefix) (aux .dictionary) (ctl .acquire) program
/-- Every physical word is included and no query/output alias shadow is allocated. -/
theorem stack_card :Fintype.card Stack=25 :=by
  rw [Fintype.card_sum,SemiprimeD1StackOwnerLookup.stack_card]
  decide
/-- All copy operands are physically distinct. -/
theorem copy_injective (part:Copy) :Function.Injective (copyStack part) :=by cases part <;> decide
/-- All preserving-frame operands are physically distinct. -/
theorem frame_injective (part:Frame) :Function.Injective (frameStack part) :=by cases part <;> decide
/-- All actual reversal source/destination pairs are physically distinct. -/
theorem reverse_injective (part:Reverse) :Function.Injective (reverseStack part) :=by cases part <;> decide
/-- All normalization input/scratch/output roles are physically distinct. -/
theorem trim_injective (part:Trim) :Function.Injective (trimStack part) :=by cases part <;> decide
/-- The actual key/carry-output/scratch roles are physically distinct. -/
theorem increment_injective :Function.Injective incrementStack :=by decide
/-- Every parser role is physically distinct. -/
theorem field_injective :Function.Injective fieldStack :=by decide
/-- Runtime control contains no natural/list/function/dictionary/score payload. -/
theorem control_finite :Finite machine.σ :=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- All twenty-five data and real-return alphabets are fixed finite before the input. -/
theorem alphabets_finite :∀k,Finite (machine.Γ k) :=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackSourceEnvironment
