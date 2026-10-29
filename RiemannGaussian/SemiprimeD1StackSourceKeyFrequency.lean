/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerEqualityKeyBounds
import RiemannGaussian.SemiprimeD1StackOwnerLookupBounds
import RiemannGaussian.SemiprimeD1StackWordLessExecution
import RiemannGaussian.SemiprimeD1StackSourceEnvironmentEncoding
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
/-! # Actual raw-key frequencies and maximum from one physically acquired vector
Raw keys may end false or be empty. A real sentinel-copy procedure first writes
rawKey++[true], so the real numeric first-match lookup tests EXACTraw-byte
identity. New counter records override older records at the physical dictionary
head. Every counter increment, maximum comparison, copy/frame and byte drain
executes here. There is no trie/graph/count/max/report/clock input or opcode.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceKeyFrequency
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace L
export SemiprimeD1StackOwnerLookup (Stack Label program data)
end L
namespace K
export SemiprimeD1StackOwnerEqualityKey (Label program)
end K
namespace Less
export SemiprimeD1StackWordLess (Stack Label program)
end Less
namespace I
export SemiprimeD1StackIncrementBytecode (Label code entry)
export SemiprimeD1TensorTapeFieldMachine (Stack)
end I
namespace R
export SemiprimeD1StackReduce (Label code)
export SemiprimeD1StackAdder (Stack)
end R
namespace Field
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end Field
/-- The only ten additional physical source/dictionary/counter/max/restore words; all are Boolean. -/
inductive Aux where
  | source | reader | raw | dictionary | count | maximum | incScratch | incNext | trimScratch | frameScratch
  deriving DecidableEq,Repr
instance :Fintype Aux :=Fintype.ofList
  [.source,.reader,.raw,.dictionary,.count,.maximum,.incScratch,.incNext,.trimScratch,.frameScratch]
  (by intro k;cases k <;> simp)
/-- All11actual first-match roles plus ten actual source roles, without alias shadows. -/
abbrev Stack :=L.Stack⊕Aux
/-- All lookup operands/work words are physically retained as fixed addresses. -/
def lookupStack :L.Stack→Stack :=Sum.inl
/-- All source/count/max/dictionary roles have literal fixed physical addresses. -/
def aux :Aux→Stack :=Sum.inr
/-- Actual encoded sentinel key used for every real dictionary read/write. -/
def query :Stack :=lookupStack (.inr .query)
/-- Actual frequency read, empty only for zero/absence, becomes the real incrementer input. -/
def oldCount :Stack :=lookupStack (.inr .output)
/-- Real copy/sentinel/lookup restoration scratch is shared only sequentially and cleared after each call. -/
def copyScratch :Stack :=lookupStack (.inr .copyScratch)
/-- The literal three-role sentinel procedure preserves the raw key while writing its new compact comparison key. -/
def sentinelStack (k:Fin 3) :Stack :=if k=0 then aux .raw else if k=1 then query else copyScratch
/-- Six actual preserving-copy sites before dictionary reads and actual maximum decisions. -/
inductive Copy where | stream | dictionary | maxLeft | countRight | newMaximum deriving DecidableEq,Repr
instance :Fintype Copy :=Fintype.ofList [.stream,.dictionary,.maxLeft,.countRight,.newMaximum] (by intro k;cases k <;> simp)
/-- Only real source/cache/counter words are copied, with distinct source/destination/scratch at every call. -/
def copyStack (part:Copy) (k:Fin 3) :Stack :=
  if k=0 then match part with
    | .stream=>aux .source | .dictionary=>aux .dictionary | .maxLeft=>aux .maximum
    | .countRight|.newMaximum=>aux .count
  else if k=1 then match part with
    | .stream=>aux .reader | .dictionary=>lookupStack (.inr .reader)
    | .maxLeft=>lookupStack (.inl .left) | .countRight=>lookupStack (.inl .right) | .newMaximum=>aux .maximum
  else copyScratch
/-- The raw key vector field is physically read using existing cleared lookup scratch/valid words. -/
def fieldStack :Field.Stack→Stack
  | .inl .input=>aux .reader | .inl .scratch=>lookupStack (.inr .fieldScratch)
  | .inl .output=>aux .raw | .inr _=>lookupStack (.inr .valid)
/-- The actual incrementer consumes the actual previous count word and emits real overflow/wrapped bytes. -/
def incrementStack :I.Stack→Stack
  | .input=>oldCount | .scratch=>aux .incScratch | .output=>aux .incNext
/-- Real wrapped-bit reversal obtains actual trim input rather than re-encoding a numeric counter. -/
def reverseStack (k:Fin 2) :Stack :=if k=0 then aux .incNext else aux .trimScratch
/-- Real high-zero trim writes the new compact counter; both other physical operands are reused cleared lookup operands. -/
def trimStack :R.Stack→Stack
  | .left=>lookupStack (.inl .left) | .right=>lookupStack (.inl .right)
  | .scratch=>aux .trimScratch | .output=>aux .count
/-- All five real less-than roles reuse distinct cleared lookup operands, including its discard field for the actual Bool result. -/
def lessStack :Less.Stack→Stack
  | .inl k=>lookupStack (.inl k) | .inr _=>lookupStack (.inr .discard)
/-- Both actual count and encoded key are framed onto the existing immutable old dictionary tail. -/
inductive Frame where | count | key deriving DecidableEq,Repr
instance :Fintype Frame :=Fintype.ofList [.count,.key] (by intro k;cases k <;> simp)
/-- Count then key framing physically prepends one newest-first override record per actual occurrence. -/
def frameStack (part:Frame) (k:Fin 3) :Stack :=
  if k=0 then if part=.count then aux .count else query
  else if k=1 then aux .dictionary else aux .frameScratch
/-- Fixed whole source and reusable REALret counter entry, with only actual overflow/read bits as control flags. -/
inductive Label where
  | start | copyStream | header | parse | valid | encode | copyDictionary | lookup | clearReader
  | successor | copyMaximum | copyCount | compare | readMaximum | clearMaximum | saveMaximum
  | frameCount | frameKey | tag | clearRaw | clearQuery | clearCount | eof | done | abort
  | increment | popOverflow | reverseCounter (carry:Bool) | carry (carry:Bool) | trimCounter | counterReturn
  | lookupCode (pc:L.Label) | sentinel (pc:K.Label) | copier (part:Copy) (pc:Fin 9)
  | parser (pc:Field.Label) | incrementCode (pc:I.Label) | reversal (pc:Fin 4)
  | reducer (pc:R.Label) | less (pc:Less.Label) | framer (part:Frame) (pc:Fin 11)
  deriving Fintype
/-- SAME parameterless21-role source, with no supplied frequency, maximum, raw-key equality or semantic body callback. -/
def program :Label→C.Instruction Stack Label
  | .start=>.base (.push (aux .dictionary) false .copyStream)
  | .copyStream=>.call (.copier .stream 0) .header
  | .header=>.base (.pop (aux .reader) .abort .eof .parse)
  | .parse=>.call (.parser (Field.active .tagPop (none,false))) .valid
  | .valid=>.base (.pop (lookupStack (.inr .valid)) .abort .abort .encode)
  | .encode=>.call (.sentinel (.inl 0)) .copyDictionary
  | .copyDictionary=>.call (.copier .dictionary 0) .lookup
  | .lookup=>.call (.lookupCode .loop) .clearReader
  | .clearReader=>.base (.pop (lookupStack (.inr .reader)) .successor .clearReader .clearReader)
  | .successor=>.call .increment .copyMaximum
  | .copyMaximum=>.call (.copier .maxLeft 0) .copyCount
  | .copyCount=>.call (.copier .countRight 0) .compare
  | .compare=>.call (.less .start) .readMaximum
  | .readMaximum=>.base (.pop (lookupStack (.inr .discard)) .abort .frameCount .clearMaximum)
  | .clearMaximum=>.base (.pop (aux .maximum) .saveMaximum .clearMaximum .clearMaximum)
  | .saveMaximum=>.call (.copier .newMaximum 0) .frameCount
  | .frameCount=>.call (.framer .count 0) .frameKey
  | .frameKey=>.call (.framer .key 0) .tag
  | .tag=>.base (.push (aux .dictionary) true .clearRaw)
  | .clearRaw=>.base (.pop (aux .raw) .clearQuery .clearRaw .clearRaw)
  | .clearQuery=>.base (.pop query .clearCount .clearQuery .clearQuery)
  | .clearCount=>.base (.pop (aux .count) .header .clearCount .clearCount)
  | .eof=>.base (.peek (aux .reader) .done .abort .abort)
  | .done|.abort=>.base .halt
  | .increment=>.call (.incrementCode I.entry) .popOverflow
  | .popOverflow=>.base (.pop (aux .incNext) .abort (.reverseCounter false) (.reverseCounter true))
  | .reverseCounter carry=>.call (.reversal 0) (.carry carry)
  | .carry carry=>if carry then .base (.push (aux .trimScratch) true .trimCounter) else .base (.jump .trimCounter)
  | .trimCounter=>.call (.reducer .trim) .counterReturn
  | .counterReturn=>.ret
  | .lookupCode pc=>SemiprimeD1StackValidationLink.instruction lookupStack Label.lookupCode (L.program pc)
  | .sentinel pc=>SemiprimeD1StackValidationLink.instruction sentinelStack Label.sentinel (K.program pc)
  | .copier part pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack part) (Label.copier part) (SemiprimeD1StackCopy.code pc)
  | .parser pc=>SemiprimeD1StackMultiplierLink.instruction fieldStack Label.parser (Field.code pc)
  | .incrementCode pc=>SemiprimeD1StackMultiplierLink.instruction incrementStack Label.incrementCode (I.code pc)
  | .reversal pc=>SemiprimeD1StackMultiplierLink.instruction reverseStack Label.reversal (SemiprimeD1StackReverseWord.code pc)
  | .reducer pc=>SemiprimeD1StackMultiplierLink.instruction trimStack Label.reducer (R.code pc)
  | .less pc=>SemiprimeD1StackValidationLink.instruction lessStack Label.less (Less.program pc)
  | .framer part pc=>SemiprimeD1StackMultiplierLink.instruction (frameStack part) (Label.framer part) (SemiprimeD1StackFrame.code pc)
/-- Key vector only, allother20physical words initially empty. -/
def input (bits:List Bool) :Stack→List Bool :=Function.update (fun _=>[]) (aux .source) bits
/-- Complete actual one-word front door, with no keylist/count/max/dictionary prepared as advice. -/
def initial (bits:List Bool) :C.State Stack Label :=⟨some .start,none,none,input bits,[]⟩
/-- Fixed finite machine acquires its frequency dictionary and actual maximum from raw encoded key vector only. -/
def machine :Turing.FinTM2 :=SemiprimeD1StackCalls.machine (aux .source) (aux .maximum) .start program
/-- All11shared lookup and10client words are physically counted. -/
theorem stack_card :Fintype.card Stack=21 :=by
  rw [Fintype.card_sum,SemiprimeD1StackOwnerLookup.stack_card]
  decide
/-- All actual lookup fields have an injective physical inclusion. -/
theorem lookup_injective :Function.Injective lookupStack :=Sum.inl_injective
/-- Sentinel raw/source/output/scratch roles are distinct, with no unused shadow. -/
theorem sentinel_injective :Function.Injective sentinelStack :=by decide
/-- Every preserving copy has three distinct actual operands. -/
theorem copy_injective (part:Copy) :Function.Injective (copyStack part) :=by cases part <;> decide
/-- Actual raw-field parser operands are physically distinct. -/
theorem field_injective :Function.Injective fieldStack :=by decide
/-- Actual increment input/wrapped output/scratch are physically distinct. -/
theorem increment_injective :Function.Injective incrementStack :=by decide
/-- Actual reversed-bit destination does not alias its source. -/
theorem reverse_injective :Function.Injective reverseStack :=by decide
/-- All four actual trim operands are distinct, including the two reused cleared inputs. -/
theorem trim_injective :Function.Injective trimStack :=by decide
/-- All five real numeric-maximum comparison operands are physically distinct. -/
theorem less_injective :Function.Injective lessStack :=by decide
/-- The actual stored key/value/buffer/scratch framing operands are distinct. -/
theorem frame_injective (part:Frame) :Function.Injective (frameStack part) :=by cases part <;> decide
/-- Runtime flags/labels are finite before every input key or frequency. -/
theorem control_finite :Finite machine.σ :=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- Every21-data/real-return alphabet is fixed finite. -/
theorem alphabets_finite :∀k,Finite (machine.Γ k) :=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackSourceKeyFrequency
