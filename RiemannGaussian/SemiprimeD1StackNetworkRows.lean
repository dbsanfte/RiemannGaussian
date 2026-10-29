/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexOriginal
import RiemannGaussian.SemiprimeD1StackOwnerFibreBounds
import RiemannGaussian.SemiprimeD1StackAssignmentBody
/-! # Actual original-record→owner-index→ordered binary-owner rows source
Only the old complete physical vertex-record tape and acquired unary left count
enter. The actual index is acquired once and retained; each factor port copies
and scans that real catalogue. The physical singleton result is validated and
framed. Empty-port factors still emit one empty row and one factor marker.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNetworkRows
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace I
export SemiprimeD1StackNetworkOwnerIndex (Stack Label program input)
end I
namespace F
export SemiprimeD1StackOwnerFibre (Stack Label program)
end F
namespace Field
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end Field
namespace Body
export SemiprimeD1StackAssignmentBody (Stack Label code entry)
end Body
/-- All actual factor/parser/singleton/frame/row/output/tally words. -/
inductive Aux where
  | reader | ports | table | key | owner | valid | fieldScratch | copyScratch
  | frameBuffer | frameScratch | rowHistory | row | logScratch | history | output | factors | occurrences
  deriving DecidableEq,Repr
instance :Fintype Aux :=Fintype.ofList
  [.reader,.ports,.table,.key,.owner,.valid,.fieldScratch,.copyScratch,.frameBuffer,.frameScratch,
    .rowHistory,.row,.logScratch,.history,.output,.factors,.occurrences]
  (by intro k;cases k <;> simp)
/-- All17retained index roles,14allocated fibre roles and17literal new roles. -/
abbrev Stack :=I.Stack⊕(F.Stack⊕Aux)
/-- Whole original index source/cache inclusion, retained literally after acquisition. -/
def indexStack :I.Stack→Stack :=Sum.inl
/-- Private physical factor/row/count roles. -/
def aux (k:Aux) :Stack :=.inr (.inr k)
/-- Fibre query DIRECTLYaliases the actual parsed unary port; its allocated query shadow staysEMPTY. -/
def fibreStack :F.Stack→Stack
  | .inr .query=>aux .key
  | k=>.inr (.inl k)
/-- Static inverse for actual mapped fibre roles; all other physical roles are irrelevant. -/
def fibreInverse :Stack→F.Stack
  | .inr (.inr .key)=>.inr .query
  | .inr (.inl k)=>k
  | _=>.inr .reader
/-- Only two real preserving-copy call sites are needed. -/
inductive Copy where | factors | dictionary deriving DecidableEq
instance :Fintype Copy :=Fintype.ofList [.factors,.dictionary] (by intro k;cases k <;> simp)
/-- Factor suffix is copied ONCE; acquired index output is copied physically before EACHquery. -/
def copyStack (what:Copy) (k:Fin 3) :Stack :=
  if k=0 then (if what=.factors then indexStack .reader else indexStack .output)
  else if k=1 then (if what=.factors then aux .reader else fibreStack (.inr .reader)) else aux .copyScratch
/-- Actual record/port/singleton parser phases, independent of every data list or numeric index. -/
inductive Part where | ports | table | key | owner deriving DecidableEq
instance :Fintype Part :=Fintype.ofList [.ports,.table,.key,.owner] (by intro k;cases k <;> simp)
/-- All parser reads consume actual physical fields and share only their clear private scratch/flag. -/
def fieldStack (part:Part) :Field.Stack→Stack
  | .inl .input=>match part with
    | .ports|.table=>aux .reader | .key=>aux .ports | .owner=>fibreStack (.inr .output)
  | .inl .scratch=>aux .fieldScratch
  | .inl .output=>match part with
    | .ports=>aux .ports | .table=>aux .table | .key=>aux .key | .owner=>aux .owner
  | .inr _=>aux .valid
/-- Real preserving Frame writes one actually returned BINARYowner word. -/
def frameStack (k:Fin 3) :Stack :=if k=0 then aux .owner else if k=1 then aux .frameBuffer else aux .frameScratch
/-- Actual owner-chunk, completed-row and sole final outer-history reversals. -/
inductive Reverse where | owner | row | output deriving DecidableEq
instance :Fintype Reverse :=Fintype.ofList [.owner,.row,.output] (by intro k;cases k <;> simp)
/-- Physical inner/outer reversal addresses preserve all original index tapes. -/
def reverseStack (what:Reverse) (k:Fin 2) :Stack :=
  if k=0 then match what with | .owner=>aux .frameBuffer | .row=>aux .rowHistory | .output=>aux .history
  else match what with | .owner=>aux .rowHistory | .row=>aux .row | .output=>aux .output
/-- The actual row logger frames the physically acquired row and restores its input before cleanup. -/
def bodyStack :Body.Stack→Stack
  | .word=>aux .row | .scratch=>aux .logScratch | .history=>aux .history
/-- Literal physical acquisition/validation/emission phases. -/
inductive Control where
  | start | copyFactors | factorLoop | portsField | portsValid | tableField | tableValid | clearTable
  | portLoop | keyField | keyValid | copyDictionary | lookup | singletonTag | ownerField | ownerValid
  | singletonEnd | singletonEOF | ownerFrame | ownerTag | ownerReverse | clearOwner | clearKey | countOccurrence
  | rowSeed | rowReverse | logRow | clearRow | countFactor | finish | outputReverse | done | abort
  deriving DecidableEq
instance :Fintype Control :=Fintype.ofList
  [.start,.copyFactors,.factorLoop,.portsField,.portsValid,.tableField,.tableValid,.clearTable,
    .portLoop,.keyField,.keyValid,.copyDictionary,.lookup,.singletonTag,.ownerField,.ownerValid,
    .singletonEnd,.singletonEOF,.ownerFrame,.ownerTag,.ownerReverse,.clearOwner,.clearKey,.countOccurrence,
    .rowSeed,.rowReverse,.logRow,.clearRow,.countFactor,.finish,.outputReverse,.done,.abort]
  (by intro k;cases k <;> simp)
/-- Every actual called source/field/frame/reversal/logger label is fixed finite before all inputs. -/
inductive Label where
  | local (pc:Control) | index (pc:I.Label) | fibre (pc:F.Label) | copy (what:Copy) (pc:Fin 9)
  | field (part:Part) (pc:Field.Label) | frame (pc:Fin 11) | reverse (what:Reverse) (pc:Fin 4) | body (pc:Body.Label)
  deriving Fintype
local notation "ctl" => Label.local
/-- One real fixed source, with no dictionary/lookup/arity/rows/clock supplier operand. -/
def program :Label→C.Instruction Stack Label
  | .local .start=>.call (.index (.local .start)) (ctl .copyFactors)
  | .local .copyFactors=>.call (.copy .factors 0) (ctl .factorLoop)
  | .local .factorLoop=>.base (.pop (aux .reader) (ctl .abort) (ctl .finish) (ctl .portsField))
  | .local .portsField=>.call (.field .ports (Field.active .tagPop (none,false))) (ctl .portsValid)
  | .local .portsValid=>.base (.pop (aux .valid) (ctl .abort) (ctl .abort) (ctl .tableField))
  | .local .tableField=>.call (.field .table (Field.active .tagPop (none,false))) (ctl .tableValid)
  | .local .tableValid=>.base (.pop (aux .valid) (ctl .abort) (ctl .abort) (ctl .clearTable))
  | .local .clearTable=>.base (.pop (aux .table) (ctl .portLoop) (ctl .clearTable) (ctl .clearTable))
  | .local .portLoop=>.base (.pop (aux .ports) (ctl .abort) (ctl .rowSeed) (ctl .keyField))
  | .local .keyField=>.call (.field .key (Field.active .tagPop (none,false))) (ctl .keyValid)
  | .local .keyValid=>.base (.pop (aux .valid) (ctl .abort) (ctl .abort) (ctl .copyDictionary))
  | .local .copyDictionary=>.call (.copy .dictionary 0) (ctl .lookup)
  | .local .lookup=>.call (.fibre .loop) (ctl .singletonTag)
  | .local .singletonTag=>.base (.pop (fibreStack (.inr .output)) (ctl .abort) (ctl .abort) (ctl .ownerField))
  | .local .ownerField=>.call (.field .owner (Field.active .tagPop (none,false))) (ctl .ownerValid)
  | .local .ownerValid=>.base (.pop (aux .valid) (ctl .abort) (ctl .abort) (ctl .singletonEnd))
  | .local .singletonEnd=>.base (.pop (fibreStack (.inr .output)) (ctl .abort) (ctl .singletonEOF) (ctl .abort))
  | .local .singletonEOF=>.base (.peek (fibreStack (.inr .output)) (ctl .ownerFrame) (ctl .abort) (ctl .abort))
  | .local .ownerFrame=>.call (.frame 0) (ctl .ownerTag)
  | .local .ownerTag=>.base (.push (aux .frameBuffer) true (ctl .ownerReverse))
  | .local .ownerReverse=>.call (.reverse .owner 0) (ctl .clearOwner)
  | .local .clearOwner=>.base (.pop (aux .owner) (ctl .clearKey) (ctl .clearOwner) (ctl .clearOwner))
  | .local .clearKey=>.base (.pop (aux .key) (ctl .countOccurrence) (ctl .clearKey) (ctl .clearKey))
  | .local .countOccurrence=>.base (.push (aux .occurrences) true (ctl .portLoop))
  | .local .rowSeed=>.base (.push (aux .row) false (ctl .rowReverse))
  | .local .rowReverse=>.call (.reverse .row 0) (ctl .logRow)
  | .local .logRow=>.call (.body Body.entry) (ctl .clearRow)
  | .local .clearRow=>.base (.pop (aux .row) (ctl .countFactor) (ctl .clearRow) (ctl .clearRow))
  | .local .countFactor=>.base (.push (aux .factors) true (ctl .factorLoop))
  | .local .finish=>.base (.push (aux .output) false (ctl .outputReverse))
  | .local .outputReverse=>.call (.reverse .output 0) (ctl .done)
  | .local .done|.local .abort=>.base .halt
  | .index pc=>SemiprimeD1StackValidationLink.instruction indexStack Label.index (I.program pc)
  | .fibre pc=>SemiprimeD1StackValidationLink.instruction fibreStack Label.fibre (F.program pc)
  | .copy what pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack what) (Label.copy what) (SemiprimeD1StackCopy.code pc)
  | .field part pc=>SemiprimeD1StackMultiplierLink.instruction (fieldStack part) (Label.field part) (Field.code pc)
  | .frame pc=>SemiprimeD1StackMultiplierLink.instruction frameStack Label.frame (SemiprimeD1StackFrame.code pc)
  | .reverse what pc=>SemiprimeD1StackMultiplierLink.instruction (reverseStack what) (Label.reverse what) (SemiprimeD1StackReverseWord.code pc)
  | .body pc=>SemiprimeD1StackMultiplierLink.instruction bodyStack Label.body (Body.code pc)
/-- Literal two-input physical data bank: no acquired index, rows, tally, owner, verdict or answer yet. -/
def input (vertices count:List Bool) :Stack→List Bool :=Sum.elim (I.input vertices count) (fun _=>[])
/-- Actual whole entry precedes the actual owner-index acquisition. -/
def initial (vertices count:List Bool) :C.State Stack Label :=⟨some (ctl .start),none,none,input vertices count,[]⟩
/-- One fixed finite48-role program from actual old record/count words. -/
def machine :Turing.FinTM2 :=SemiprimeD1StackCalls.machine (indexStack .vertices) (aux .output) (ctl .start) program
/-- Actual query alias has an exact static inverse on every called fibre register. -/
theorem fibre_inverse (k:F.Stack) :fibreInverse (fibreStack k)=k :=by
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- All actual fibre source/destination/scratch fields are distinct despite the intended query alias. -/
theorem fibre_injective :Function.Injective fibreStack :=by
  intro a b h
  have he:=congrArg fibreInverse h
  simpa only [fibre_inverse] using he
/-- Every called original index role remains physically distinct. -/
theorem index_injective :Function.Injective indexStack :=Sum.inl_injective
/-- Both actual preserving-copy operand maps are injective. -/
theorem copy_injective (what:Copy) :Function.Injective (copyStack what) :=by cases what <;> decide
/-- All four actual parser operand maps are injective. -/
theorem field_injective (part:Part) :Function.Injective (fieldStack part) :=by cases part <;> decide
/-- The real binary-owner frame has separate source, output and scratch words. -/
theorem frame_injective :Function.Injective frameStack :=by decide
/-- All three inner/outer actual reversals have distinct source and target words. -/
theorem reverse_injective (what:Reverse) :Function.Injective (reverseStack what) :=by cases what <;> decide
/-- The actual row logger preserves its source using separate restoration scratch. -/
theorem body_injective :Function.Injective bodyStack :=by decide
/-- Complete allocation includes the entire index, entire fibre bank and its ONEunused query shadow. -/
theorem stack_card :Fintype.card Stack=48 :=by
  rw [Fintype.card_sum,SemiprimeD1StackNetworkOwnerIndex.stack_card,Fintype.card_sum,SemiprimeD1StackOwnerFibre.stack_card]
  decide
/-- Runtime control contains no original N/graph/lookup/list/count/arity/native evaluator object. -/
theorem control_finite :Finite machine.σ :=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- Every actual48role and real-return alphabet is fixed finite before every input. -/
theorem alphabets_finite :∀k,Finite (machine.Γ k) :=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackNetworkRows
