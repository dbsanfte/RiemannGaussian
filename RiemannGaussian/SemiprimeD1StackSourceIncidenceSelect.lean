/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidence
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectSpec
import RiemannGaussian.SemiprimeD1StackFrame
/-! # Actual prepared incidence-only candidate and variable controller
Seven acquired physical words enter: occurrence stream, alphabet catalogue,
three binary powers and unary owner/factor counts. Every temporary candidate is
installed by the real environment source and scored by the real incidence
source. Real field reads remove only the newly prepended dictionary row, leaving
its identical old tail. The actual key snapshot is copied back physically.
Strict physical WordLess replaces the incumbent only on an improvement.
The query engine is imported as a frozen actual source dependency.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace Q
export SemiprimeD1StackSourceIncidence (Stack Label program environmentStack aux data)
end Q
namespace E
export SemiprimeD1StackSourceEnvironment (Stack Label aux query output)
end E
namespace Less
export SemiprimeD1StackWordLess (Stack Label program)
end Less
namespace Field
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end Field
/-- All sixteen physical input, marker, snapshot, catalogue, parser and incumbent/comparison words. -/
inductive Aux where
  | catalogue | owners | factors | todo | reader | discard | parserScratch | valid
  | copyScratch | savedKey | bestID | bestScore | compareLeft | compareRight | compareScratch | compareOutput
  deriving DecidableEq,Repr
/-- Literal complete physical inventory, fixed before every acquired source. -/
instance :Fintype Aux :=Fintype.ofList
  [.catalogue,.owners,.factors,.todo,.reader,.discard,.parserScratch,.valid,.copyScratch,.savedKey,
    .bestID,.bestScore,.compareLeft,.compareRight,.compareScratch,.compareOutput]
  (by intro k;cases k <;> simp)
/-- The full real query bank plus every caller word; no physical alias shadow is allocated. -/
abbrev Stack :=Q.Stack⊕Aux
/-- All47real query/cache roles are included literally. -/
def queryStack :Q.Stack→Stack :=Sum.inl
/-- Private physical selector roles. -/
def aux :Aux→Stack :=Sum.inr
/-- Every25-role environment field is shared directly with the actual query engine. -/
def environmentStack (k:E.Stack) :Stack :=queryStack (Q.environmentStack k)
/-- The actually generated dictionary; temporary rollback removes only its real newest row. -/
def dictionary :Stack :=environmentStack (E.aux .dictionary)
/-- Actual compact next variable key; its snapshot is acquired by a paid preserving copy. -/
def nextKey :Stack :=environmentStack (E.aux .nextKey)
/-- The actual parsed candidate directly occupies the environment's preserved chosen-ID word. -/
def candidate :Stack :=environmentStack (E.aux .chosenID)
/-- The actual newest-first selected ID vector directly occupies the preserved environment prefix word. -/
def selected :Stack :=environmentStack (E.aux .prefix)
/-- Actual physically accumulated binary query result, cleared after every candidate. -/
def score :Stack :=queryStack (Q.aux .total)
/-- Ten literal preserving-copy choices, independent of every count, candidate and score. -/
inductive Copy where | owners | factors | saveKey | catalogue | bestID | bestScore | scoreOperand | bestOperand | restoreKey | winner
  deriving DecidableEq
/-- Literal preserving-copy control inventory, independent of all word values. -/
instance :Fintype Copy :=Fintype.ofList
  [.owners,.factors,.saveKey,.catalogue,.bestID,.bestScore,.scoreOperand,.bestOperand,.restoreKey,.winner]
  (by intro k;cases k <;> simp)
/-- Physical copy source/destination/scratch fields. Existing marker words are extended by actual copies. -/
def copyStack (part:Copy) (k:Fin 3) :Stack :=
  if k=0 then match part with
    | .owners=>aux .owners | .factors=>aux .factors | .saveKey=>nextKey | .catalogue=>aux .catalogue
    | .bestID=>candidate | .bestScore|.scoreOperand=>score | .bestOperand=>aux .bestScore
    | .restoreKey=>aux .savedKey | .winner=>aux .bestID
  else if k=1 then match part with
    | .owners|.factors=>aux .todo | .saveKey=>aux .savedKey | .catalogue=>aux .reader
    | .bestID=>aux .bestID | .bestScore=>aux .bestScore | .scoreOperand=>aux .compareLeft
    | .bestOperand=>aux .compareRight | .restoreKey=>nextKey | .winner=>candidate
  else aux .copyScratch
/-- The real five-word subtract/borrow/cleanup comparison uses discard only when its parser use has finished. -/
def lessStack :Less.Stack→Stack
  | .inl .left=>aux .compareLeft | .inl .right=>aux .compareRight | .inl .scratch=>aux .compareScratch
  | .inl .output=>aux .discard | .inr _=>aux .compareOutput
/-- Actual candidate ID, unused colour row and temporary dictionary-head parser phases. -/
inductive Part where | candidate | colour | rollback deriving DecidableEq
/-- Literal parser-phase inventory; no input ordinal is a controller label. -/
instance :Fintype Part :=Fintype.ofList [.candidate,.colour,.rollback] (by intro k;cases k <;> simp)
/-- Every actual field call reads a real tape; both rollback fields are read and drained sequentially. -/
def fieldStack (part:Part) :Field.Stack→Stack
  | .inl .input=>if part=.rollback then dictionary else aux .reader
  | .inl .scratch=>aux .parserScratch
  | .inl .output=>if part=.candidate then candidate else aux .discard
  | .inr _=>aux .valid
/-- Real preserving framing prepends the winner to the existing physical newest-first selected vector. -/
def frameStack (k:Fin 3) :Stack :=if k=0 then aux .bestID else if k=1 then selected else aux .parserScratch
/-- Every decision is a fixed finite controller stage; first-candidate mode is not inferred from an empty score/ID. -/
inductive Control where
  | start | initialize | copyOwners | copyFactors | loopVariable | saveKey | copyCatalogue
  | header (first:Bool) | parseID (first:Bool) | idValid (first:Bool) | parseColour (first:Bool)
  | colourValid (first:Bool) | drainColour (first:Bool) | install (first:Bool) | evaluate (first:Bool) | acquired (first:Bool)
  | saveFirstScore | copyBestOperand | compare | compared | clearBestID | clearBestScore | saveBetterID | saveBetterScore
  | clearScore | rollbackTag | rollbackKey | rollbackKeyValid | drainRollbackKey | rollbackValue | rollbackValueValid
  | drainRollbackValue | clearTempKey | restoreKey | clearCandidate | catalogueEOF | copyWinner | commit | frameWinner
  | prefixTag | clearCommittedChosen | clearSavedKey | clearWinnerID | clearWinnerScore | done | abort
  deriving DecidableEq,Fintype
/-- All actual query/environment/copy/field/compare/frame return labels are fixed finite before the input. -/
inductive Label where
  | local (pc:Control) | queryCode (pc:Q.Label) | copier (part:Copy) (pc:Fin 9)
  | parser (part:Part) (pc:Field.Label) | less (pc:Less.Label) | framer (pc:Fin 11)
  deriving Fintype
local notation "ctl" => Label.local
/-- Same real environment entries already embedded by the query engine; no environment source is cloned. -/
def environmentLabel (pc:E.Label) :Label :=.queryCode (.environment pc)
/-- One parameterless literal prepared selector, with no native score/evaluator/owner/count/prefix callback input. -/
def program :Label→C.Instruction Stack Label
  | .local .start=>.base (.push selected false (ctl .initialize))
  | .local .initialize=>.call (environmentLabel (.local .initialize)) (ctl .copyOwners)
  | .local .copyOwners=>.call (.copier .owners 0) (ctl .copyFactors)
  | .local .copyFactors=>.call (.copier .factors 0) (ctl .loopVariable)
  | .local .loopVariable=>.base (.pop (aux .todo) (ctl .done) (ctl .abort) (ctl .saveKey))
  | .local .saveKey=>.call (.copier .saveKey 0) (ctl .copyCatalogue)
  | .local .copyCatalogue=>.call (.copier .catalogue 0) (ctl (.header true))
  | .local (.header first)=>.base (.pop (aux .reader) (ctl .abort) (ctl (if first then .abort else .catalogueEOF)) (ctl (.parseID first)))
  | .local (.parseID first)=>.call (.parser .candidate (Field.active .tagPop (none,false))) (ctl (.idValid first))
  | .local (.idValid first)=>.base (.pop (aux .valid) (ctl .abort) (ctl .abort) (ctl (.parseColour first)))
  | .local (.parseColour first)=>.call (.parser .colour (Field.active .tagPop (none,false))) (ctl (.colourValid first))
  | .local (.colourValid first)=>.base (.pop (aux .valid) (ctl .abort) (ctl .abort) (ctl (.drainColour first)))
  | .local (.drainColour first)=>.base (.pop (aux .discard) (ctl (.install first)) (ctl (.drainColour first)) (ctl (.drainColour first)))
  | .local (.install first)=>.call (environmentLabel (.local .extend)) (ctl (.evaluate first))
  | .local (.evaluate first)=>.call (.queryCode .start) (ctl (.acquired first))
  | .local (.acquired true)=>.call (.copier .bestID 0) (ctl .saveFirstScore)
  | .local .saveFirstScore=>.call (.copier .bestScore 0) (ctl .clearScore)
  | .local (.acquired false)=>.call (.copier .scoreOperand 0) (ctl .copyBestOperand)
  | .local .copyBestOperand=>.call (.copier .bestOperand 0) (ctl .compare)
  | .local .compare=>.call (.less .start) (ctl .compared)
  | .local .compared=>.base (.pop (aux .compareOutput) (ctl .abort) (ctl .clearScore) (ctl .clearBestID))
  | .local .clearBestID=>.base (.pop (aux .bestID) (ctl .clearBestScore) (ctl .clearBestID) (ctl .clearBestID))
  | .local .clearBestScore=>.base (.pop (aux .bestScore) (ctl .saveBetterID) (ctl .clearBestScore) (ctl .clearBestScore))
  | .local .saveBetterID=>.call (.copier .bestID 0) (ctl .saveBetterScore)
  | .local .saveBetterScore=>.call (.copier .bestScore 0) (ctl .clearScore)
  | .local .clearScore=>.base (.pop score (ctl .rollbackTag) (ctl .clearScore) (ctl .clearScore))
  | .local .rollbackTag=>.base (.pop dictionary (ctl .abort) (ctl .abort) (ctl .rollbackKey))
  | .local .rollbackKey=>.call (.parser .rollback (Field.active .tagPop (none,false))) (ctl .rollbackKeyValid)
  | .local .rollbackKeyValid=>.base (.pop (aux .valid) (ctl .abort) (ctl .abort) (ctl .drainRollbackKey))
  | .local .drainRollbackKey=>.base (.pop (aux .discard) (ctl .rollbackValue) (ctl .drainRollbackKey) (ctl .drainRollbackKey))
  | .local .rollbackValue=>.call (.parser .rollback (Field.active .tagPop (none,false))) (ctl .rollbackValueValid)
  | .local .rollbackValueValid=>.base (.pop (aux .valid) (ctl .abort) (ctl .abort) (ctl .drainRollbackValue))
  | .local .drainRollbackValue=>.base (.pop (aux .discard) (ctl .clearTempKey) (ctl .drainRollbackValue) (ctl .drainRollbackValue))
  | .local .clearTempKey=>.base (.pop nextKey (ctl .restoreKey) (ctl .clearTempKey) (ctl .clearTempKey))
  | .local .restoreKey=>.call (.copier .restoreKey 0) (ctl .clearCandidate)
  | .local .clearCandidate=>.base (.pop candidate (ctl (.header false)) (ctl .clearCandidate) (ctl .clearCandidate))
  | .local .catalogueEOF=>.base (.peek (aux .reader) (ctl .copyWinner) (ctl .abort) (ctl .abort))
  | .local .copyWinner=>.call (.copier .winner 0) (ctl .commit)
  | .local .commit=>.call (environmentLabel (.local .extend)) (ctl .frameWinner)
  | .local .frameWinner=>.call (.framer 0) (ctl .prefixTag)
  | .local .prefixTag=>.base (.push selected true (ctl .clearCommittedChosen))
  | .local .clearCommittedChosen=>.base (.pop candidate (ctl .clearSavedKey) (ctl .clearCommittedChosen) (ctl .clearCommittedChosen))
  | .local .clearSavedKey=>.base (.pop (aux .savedKey) (ctl .clearWinnerID) (ctl .clearSavedKey) (ctl .clearSavedKey))
  | .local .clearWinnerID=>.base (.pop (aux .bestID) (ctl .clearWinnerScore) (ctl .clearWinnerID) (ctl .clearWinnerID))
  | .local .clearWinnerScore=>.base (.pop (aux .bestScore) (ctl .loopVariable) (ctl .clearWinnerScore) (ctl .clearWinnerScore))
  | .local .done|.local .abort=>.base .halt
  | .queryCode pc=>SemiprimeD1StackValidationLink.instruction queryStack Label.queryCode (Q.program pc)
  | .copier part pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack part) (Label.copier part) (SemiprimeD1StackCopy.code pc)
  | .parser part pc=>SemiprimeD1StackMultiplierLink.instruction (fieldStack part) (Label.parser part) (Field.code pc)
  | .less pc=>SemiprimeD1StackValidationLink.instruction lessStack Label.less (Less.program pc)
  | .framer pc=>SemiprimeD1StackMultiplierLink.instruction frameStack Label.framer (SemiprimeD1StackFrame.code pc)
/-- Exactly seven actual acquired words are initialized; every environment/helper/score/prefix word starts empty. -/
def input (occurrences catalogue square cube fourth owners factors:List Bool) :Stack→List Bool :=
  Sum.elim (Q.data (fun _=>[]) occurrences square cube fourth) (fun k=>match k with
    | .catalogue=>catalogue | .owners=>owners | .factors=>factors | _=>[])
/-- Literal prepared front door, with no advised environment/prefix/score/variable-index/time operand. -/
def initial (occurrences catalogue square cube fourth owners factors:List Bool) :C.State Stack Label :=
  ⟨some (ctl .start),none,none,input occurrences catalogue square cube fourth owners factors,[]⟩
/-- One fixed finite machine; caller acquisition of its seven physical inputs remains explicit. -/
def machine :Turing.FinTM2 :=SemiprimeD1StackCalls.machine (queryStack (Q.aux .source)) selected (ctl .start) program
/-- Every one of the47query/cache fields and16selector words is counted, with no omitted alias shadows. -/
theorem stack_card :Fintype.card Stack=63 :=by
  rw [Fintype.card_sum,SemiprimeD1StackSourceIncidence.stack_card]
  decide
/-- Every preserving copy reads/writes three distinct actual roles. -/
theorem copy_injective (part:Copy) :Function.Injective (copyStack part) :=by cases part <;> decide
/-- Every five-role real comparison operand is distinct, including its reused difference word. -/
theorem less_injective :Function.Injective lessStack :=by decide
/-- Both actual framed fields have separate source/output/scratch/valid words. -/
theorem field_injective (part:Part) :Function.Injective (fieldStack part) :=by cases part <;> decide
/-- Winner framing has separate actual source/prefix/scratch roles. -/
theorem frame_injective :Function.Injective frameStack :=by decide
/-- All data/real-return alphabets are fixed finite before the original incidence family. -/
theorem alphabets_finite :∀k,Finite (machine.Γ k) :=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
/-- No natural counter, score function, owner getter or source callback occurs in transient control. -/
theorem control_finite :Finite machine.σ :=SemiprimeD1StackCalls.control_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect
