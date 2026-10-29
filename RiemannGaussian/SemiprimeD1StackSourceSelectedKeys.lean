/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceEnvironmentOriginal
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
/-! # Actual selected incidence keys from acquired occurrence tape and complete prefix cache
The joint key is frame ownerID factorID, with the factor ID as RAWsecond tail.
Both IDs are read by actual preserving environment lookups and TRUEfound tests.
One forward-order vector entry is emitted for every actual original occurrence.
Selection, cache acquisition and frequencies are not rerun. This is a prepared
physical source; an N-only selector/packet front door remains a caller join.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceSelectedKeys
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace E
export SemiprimeD1StackSourceEnvironment (Stack Label program query output aux)
end E
namespace Field
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end Field
/-- Every actual retained-source/parser/ID/framing/logger/query-save role is Boolean and physically counted. -/
inductive Aux where
  | source | reader | ownerKey | factorKey | ownerID | key | copyScratch | fieldScratch | valid
  | savedQuery | frameBuffer | frameScratch | history | output
  deriving DecidableEq,Repr
instance :Fintype Aux :=Fintype.ofList
  [.source,.reader,.ownerKey,.factorKey,.ownerID,.key,.copyScratch,.fieldScratch,.valid,
   .savedQuery,.frameBuffer,.frameScratch,.history,.output] (by intro k;cases k <;> simp)
/-- All25 retained environment roles plus all14 actual source roles; there are no unused alias shadows. -/
abbrev Stack :=E.Stack⊕Aux
/-- The entire acquired dictionary/cache has an injective physical inclusion. -/
def environmentStack :E.Stack→Stack :=Sum.inl
/-- Fourteen fixed physical source addresses. -/
def aux :Aux→Stack :=Sum.inr
/-- The caller's arbitrary actual query is physically saved/restored around the source. -/
def query :Stack :=environmentStack E.query
/-- Actual normalized ID output of a real dictionary read. -/
def idOutput :Stack :=environmentStack E.output
/-- Actual found singleton, distinguishing selected zero[] from a missing/free endpoint. -/
def found :Stack :=environmentStack (E.aux .found)
/-- Owner/factor selection is a fixed two-element parser/control choice before all inputs. -/
inductive Part where | owner | factor deriving DecidableEq,Repr
instance :Fintype Part :=Fintype.ofList [.owner,.factor] (by intro k;cases k <;> simp)
/-- Actual retained parsed variable key. -/
def variableKey :Part→Stack | .owner=>aux .ownerKey | .factor=>aux .factorKey
/-- All actual preserving-copy sites, never a supplied key/label/decoded value. -/
inductive Copy where | saveQuery | restoreQuery | stream | query (part:Part) | id (part:Part)
  deriving DecidableEq,Fintype
/-- Every source/destination/scratch triple is physically distinct. -/
def copyStack (part:Copy) (k:Fin 3) :Stack :=
  if k=0 then match part with
    | .saveQuery=>query | .restoreQuery=>aux .savedQuery | .stream=>aux .source
    | .query part=>variableKey part | .id _=>idOutput
  else if k=1 then match part with
    | .saveQuery=>aux .savedQuery | .restoreQuery=>query | .stream=>aux .reader
    | .query _=>query | .id .owner=>aux .ownerID | .id .factor=>aux .key
  else aux .copyScratch
/-- Actual occurrence-field parser; both fields are physically consumed before either lookup. -/
def fieldStack (part:Part) :Field.Stack→Stack
  | .inl .input=>aux .reader | .inl .scratch=>aux .fieldScratch
  | .inl .output=>variableKey part | .inr _=>aux .valid
/-- The joint-key frame and its enclosing vector field are separate real Frame calls. -/
inductive Frame where | joint | vector deriving DecidableEq,Repr
instance :Fintype Frame :=Fintype.ofList [.joint,.vector] (by intro k;cases k <;> simp)
/-- Joint framing preserves the actual raw factor-ID tail; vector framing is external to that complete joint key. -/
def frameStack (part:Frame) (k:Fin 3) :Stack :=
  if k=0 then if part=.joint then aux .ownerID else aux .key
  else if k=1 then if part=.joint then aux .key else aux .frameBuffer
  else aux .frameScratch
/-- Only a row-log reversal and one final chronological reversal occur. -/
inductive Reverse where | row | finish deriving DecidableEq,Repr
instance :Fintype Reverse :=Fintype.ofList [.row,.finish] (by intro k;cases k <;> simp)
/-- Both actual reverse source/destination pairs are distinct. -/
def reverseStack (part:Reverse) (k:Fin 2) :Stack :=
  if k=0 then if part=.row then aux .frameBuffer else aux .history
  else if part=.row then aux .history else aux .output
/-- One finite source, actual read flags and true-fixed-ID branches; no count/graph/list/getter/clock is control data. -/
inductive Label where
  | start | clearOriginalQuery | copyStream | header | eof | parse (part:Part) | valid (part:Part)
  | copyQuery (part:Part) | lookup (part:Part) | readFound (part:Part) | copyID (part:Part)
  | clearID (part:Part) | clearQuery (part:Part) | frameJoint | frameVector | tag | reverseRow
  | clearOwnerID | clearKey | clearOwnerKey | clearFactorKey | seed | reverseFinish
  | restoreQuery | clearSavedQuery | done | abort
  | environment (pc:E.Label) | copier (part:Copy) (pc:Fin 9) | parser (part:Part) (pc:Field.Label)
  | framer (part:Frame) (pc:Fin 11) | reversal (part:Reverse) (pc:Fin 4)
  deriving Fintype
/-- Actual finite continuation after a physically parsed owner/factor field. -/
def afterField :Part→Label | .owner=>.parse .factor | .factor=>.copyQuery .owner
/-- Physical continuation after both a returned ID and its actual query have been drained. -/
def afterLookup :Part→Label | .owner=>.copyQuery .factor | .factor=>.frameJoint
/-- Same fixed39-role real program: consume occurrence bytes, look up two fixed IDs, frame EXACToldkey and log once. -/
def program :Label→C.Instruction Stack Label
  | .start=>.call (.copier .saveQuery 0) .clearOriginalQuery
  | .clearOriginalQuery=>.base (.pop query .copyStream .clearOriginalQuery .clearOriginalQuery)
  | .copyStream=>.call (.copier .stream 0) .header
  | .header=>.base (.pop (aux .reader) .abort .eof (.parse .owner))
  | .eof=>.base (.peek (aux .reader) .seed .abort .abort)
  | .parse part=>.call (.parser part (Field.active .tagPop (none,false))) (.valid part)
  | .valid part=>.base (.pop (aux .valid) .abort .abort (afterField part))
  | .copyQuery part=>.call (.copier (.query part) 0) (.lookup part)
  | .lookup part=>.call (.environment (.local .lookup)) (.readFound part)
  | .readFound part=>.base (.pop found .abort .abort (.copyID part))
  | .copyID part=>.call (.copier (.id part) 0) (.clearID part)
  | .clearID part=>.base (.pop idOutput (.clearQuery part) (.clearID part) (.clearID part))
  | .clearQuery part=>.base (.pop query (afterLookup part) (.clearQuery part) (.clearQuery part))
  | .frameJoint=>.call (.framer .joint 0) .frameVector
  | .frameVector=>.call (.framer .vector 0) .tag
  | .tag=>.base (.push (aux .frameBuffer) true .reverseRow)
  | .reverseRow=>.call (.reversal .row 0) .clearOwnerID
  | .clearOwnerID=>.base (.pop (aux .ownerID) .clearKey .clearOwnerID .clearOwnerID)
  | .clearKey=>.base (.pop (aux .key) .clearOwnerKey .clearKey .clearKey)
  | .clearOwnerKey=>.base (.pop (aux .ownerKey) .clearFactorKey .clearOwnerKey .clearOwnerKey)
  | .clearFactorKey=>.base (.pop (aux .factorKey) .header .clearFactorKey .clearFactorKey)
  | .seed=>.base (.push (aux .output) false .reverseFinish)
  | .reverseFinish=>.call (.reversal .finish 0) .restoreQuery
  | .restoreQuery=>.call (.copier .restoreQuery 0) .clearSavedQuery
  | .clearSavedQuery=>.base (.pop (aux .savedQuery) .done .clearSavedQuery .clearSavedQuery)
  | .done|.abort=>.base .halt
  | .environment pc=>SemiprimeD1StackValidationLink.instruction environmentStack Label.environment (E.program pc)
  | .copier part pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack part) (Label.copier part) (SemiprimeD1StackCopy.code pc)
  | .parser part pc=>SemiprimeD1StackMultiplierLink.instruction (fieldStack part) (Label.parser part) (Field.code pc)
  | .framer part pc=>SemiprimeD1StackMultiplierLink.instruction (frameStack part) (Label.framer part) (SemiprimeD1StackFrame.code pc)
  | .reversal part pc=>SemiprimeD1StackMultiplierLink.instruction (reverseStack part) (Label.reversal part) (SemiprimeD1StackReverseWord.code pc)
/-- Actual complete acquired environment and original occurrence source, with all14 new words fresh except source. -/
def data (environment:E.Stack→List Bool) (stream:List Bool) :Stack→List Bool :=
  Sum.elim environment (fun k=>if k=.source then stream else [])
/-- Prepared physical entry, with complete-cache lineage explicit to the actual selector caller. -/
def initial (environment:E.Stack→List Bool) (stream:List Bool) :C.State Stack Label :=
  ⟨some .start,none,none,data environment stream,[]⟩
/-- Same finite compiled39-role source before every N/selected prefix/occurrence. -/
def machine :Turing.FinTM2 :=SemiprimeD1StackCalls.machine (aux .source) (aux .output) .start program
/-- Exact physical inventory includes all25 cache and14 source roles. -/
theorem stack_card :Fintype.card Stack=39 :=by
  rw [Fintype.card_sum,SemiprimeD1StackSourceEnvironment.stack_card]
  decide
/-- Every real copy has three distinct actual operands. -/
theorem copy_injective (part:Copy) :Function.Injective (copyStack part) :=by
  cases part with
  | query part|id part=>cases part <;> decide
  | _=>decide
/-- No unused shadow is introduced for the acquired environment. -/
theorem environment_injective :Function.Injective environmentStack :=Sum.inl_injective
/-- Actual field-parser input/scratch/output/valid roles are distinct. -/
theorem field_injective (part:Part) :Function.Injective (fieldStack part) :=by cases part <;> decide
/-- Each actual preserving Frame has distinct input/buffer/scratch. -/
theorem frame_injective (part:Frame) :Function.Injective (frameStack part) :=by cases part <;> decide
/-- Actual logger reversals do not alias their source/destination. -/
theorem reverse_injective (part:Reverse) :Function.Injective (reverseStack part) :=by cases part <;> decide
/-- Flags and all labels are finite, independent of every input word and selected ID. -/
theorem control_finite :Finite machine.σ :=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- Every actual39-data/real-return alphabet is fixed finite. -/
theorem alphabets_finite :∀k,Finite (machine.Γ k) :=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackSourceSelectedKeys
