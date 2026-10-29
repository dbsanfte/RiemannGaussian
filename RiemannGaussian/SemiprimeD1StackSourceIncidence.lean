/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSpec
import RiemannGaussian.SemiprimeD1StackSourceEnvironmentOriginal
import RiemannGaussian.SemiprimeD1StackWordEqualExecution
import RiemannGaussian.SemiprimeD1StackAdderExecution
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
/-! # Actual incidence-only ordered-pair source query
One fixed47-role program scans acquired occurrence bytes and a real retained
prefix cache. Endpoint keys, fixed IDs, flags, count words and additions are all
physical. No graph, count, predicate, decoded ID, score or clock is an opcode.
This is a prepared physical query, not an N-only selector or packet front door.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidence
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace E
export SemiprimeD1StackSourceEnvironment (Stack Label program query output aux)
end E
namespace Field
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end Field
namespace A
export SemiprimeD1StackAdder (Stack Label code)
end A
namespace Q
export SemiprimeD1StackWordEqual (Label code)
end Q
open SemiprimeD1StackSourceIncidenceSpec (Status)
/-- Complete private parser/comparison/accumulator bank; all22 roles are physical Boolean words. -/
inductive Aux where
  | source | outerReader | innerReader | ownerLeft | factorLeft | ownerRight | factorRight
  | square | cube | fourth | copyScratch | fieldScratch | valid
  | eqLeft | eqRight | eqScratch | eqOutput | savedQuery | sumLeft | term | sumScratch | total
  deriving DecidableEq,Repr
instance :Fintype Aux :=Fintype.ofList
  [.source,.outerReader,.innerReader,.ownerLeft,.factorLeft,.ownerRight,.factorRight,
   .square,.cube,.fourth,.copyScratch,.fieldScratch,.valid,.eqLeft,.eqRight,.eqScratch,
   .eqOutput,.savedQuery,.sumLeft,.term,.sumScratch,.total] (by intro k;cases k <;> simp)
/-- Actual acquired environment plus every private query role, including unused equality scratch. -/
abbrev Stack :=E.Stack⊕Aux
/-- All25 acquired cache roles have an injective physical inclusion. -/
def environmentStack :E.Stack→Stack :=Sum.inl
/-- All22 query roles have fixed physical addresses. -/
def aux :Aux→Stack :=Sum.inr
/-- The two disjoint original endpoint namespaces are fixed finite branches. -/
inductive Edge where | owner | factor deriving DecidableEq,Repr
instance :Fintype Edge :=Fintype.ofList [.owner,.factor] (by intro k;cases k <;> simp)
/-- Actual retained count-word selectors, never supplied decoded powers. -/
inductive Power where | square | cube | fourth deriving DecidableEq,Repr
instance :Fintype Power :=Fintype.ofList [.square,.cube,.fourth] (by intro k;cases k <;> simp)
/-- Physical endpoint field; false selects the retained outer descriptor, true the inner descriptor. -/
def key (inner:Bool) :Edge→Stack
  | .owner=>aux (if inner then .ownerRight else .ownerLeft)
  | .factor=>aux (if inner then .factorRight else .factorLeft)
/-- The retained environment query is saved/restored; no caller query operand is lost. -/
def query :Stack :=environmentStack E.query
/-- Actual environment ID output, kept distinct from its found flag. -/
def idOutput :Stack :=environmentStack E.output
/-- Actual lookup presence singleton, distinct even when the returned ID is zero[]. -/
def found :Stack :=environmentStack (E.aux .found)
/-- Literal preserving-copy sites and their fixed finite operand selections. -/
inductive Copy where
  | saveQuery | restoreQuery | outer | inner | keyLeft (kind:Edge) | keyRight (kind:Edge)
  | query (kind:Edge) (side:Bool) | id (side:Bool) | power (part:Power) | sum
  deriving DecidableEq,Fintype
/-- Actual source, empty destination and shared empty restoration scratch for each paid copy. -/
def copyStack (part:Copy) (k:Fin 3) :Stack :=
  if k=0 then match part with
    | .saveQuery=>query | .restoreQuery=>aux .savedQuery | .outer|.inner=>aux .source
    | .keyLeft kind=>key false kind | .keyRight kind=>key true kind
    | .query kind side=>key side kind | .id _=>idOutput
    | .power .square=>aux .square | .power .cube=>aux .cube | .power .fourth=>aux .fourth
    | .sum=>aux .total
  else if k=1 then match part with
    | .saveQuery=>aux .savedQuery | .restoreQuery=>query | .outer=>aux .outerReader | .inner=>aux .innerReader
    | .keyLeft _=>aux .eqLeft | .keyRight _=>aux .eqRight | .query _ _=>query
    | .id side=>aux (if side then .eqRight else .eqLeft) | .power _=>aux .term | .sum=>aux .sumLeft
  else aux .copyScratch
/-- Real four-role numeric equality, accepting unequal high-zero padding. -/
def equalStack :A.Stack→Stack
  | .left=>aux .eqLeft | .right=>aux .eqRight | .scratch=>aux .eqScratch | .output=>aux .eqOutput
/-- Real four-role ripple addition; operands are actually consumed and the new total is physically written. -/
def addStack :A.Stack→Stack
  | .left=>aux .sumLeft | .right=>aux .term | .scratch=>aux .sumScratch | .output=>aux .total
/-- Every occurrence field is physically parsed from its actual enclosing stream. -/
def fieldStack (inner:Bool) (kind:Edge) :Field.Stack→Stack
  | .inl .input=>aux (if inner then .innerReader else .outerReader)
  | .inl .scratch=>aux .fieldScratch | .inl .output=>key inner kind | .inr _=>aux .valid
/-- Fixed caller, parser and classifier labels; statuses carry only previously read finite Booleans. -/
inductive Label where
  | start | clearOriginalQuery | copyOuter | outerHeader | outerEOF | copyInner | innerHeader | innerEOF
  | parse (inner:Bool) (kind:Edge) | valid (inner:Bool) (kind:Edge) | clearKey (inner:Bool) (kind:Edge)
  | ownerCall | ownerPossible | ownerDrop (possible:Bool) | factorCall (first:Status)
  | factorPossible (first:Status) | factorDrop (first:Status) (possible:Bool)
  | payload (first second:Status) | copySum | clearTotal | add
  | restoreQuery | clearSavedQuery | done | abort
  | edgeStart (kind:Edge) | edgeRight (kind:Edge) | compareKeys (kind:Edge) | keysEqual (kind:Edge)
  | copyQuery (kind:Edge) (side:Bool) | lookup (kind:Edge) (side:Bool)
  | readFound (kind:Edge) (side:Bool) | copyID (kind:Edge) (side:Bool)
  | clearID (kind:Edge) (side present:Bool) | clearQuery (kind:Edge) (side present:Bool)
  | afterLookup (kind:Edge) (side present:Bool) | clearFreeLeft | compareIDs | idsEqual
  | status (outcome:Status) | statusPossible (outcome:Status) | edgeReturn
  | environment (pc:E.Label) | copier (part:Copy) (pc:Fin 9)
  | parser (inner:Bool) (kind:Edge) (pc:Field.Label) | equality (pc:Q.Label) | adder (pc:A.Label)
  deriving Fintype
/-- Next literal parser stage; no field ordinal from the input enters control. -/
def afterField (inner:Bool) :Edge→Label
  | .owner=>.parse inner .factor | .factor=>if inner then .ownerCall else .copyInner
/-- Complete same fixed physical program, including actual lookup calls and all cleanup. -/
def program :Label→C.Instruction Stack Label
  | .start=>.call (.copier .saveQuery 0) .clearOriginalQuery
  | .clearOriginalQuery=>.base (.pop query .copyOuter .clearOriginalQuery .clearOriginalQuery)
  | .copyOuter=>.call (.copier .outer 0) .outerHeader
  | .outerHeader=>.base (.pop (aux .outerReader) .abort .outerEOF (.parse false .owner))
  | .outerEOF=>.base (.peek (aux .outerReader) .restoreQuery .abort .abort)
  | .copyInner=>.call (.copier .inner 0) .innerHeader
  | .innerHeader=>.base (.pop (aux .innerReader) .abort .innerEOF (.parse true .owner))
  | .innerEOF=>.base (.peek (aux .innerReader) (.clearKey false .owner) .abort .abort)
  | .parse inner kind=>.call (.parser inner kind (Field.active .tagPop (none,false))) (.valid inner kind)
  | .valid inner kind=>.base (.pop (aux .valid) .abort .abort (afterField inner kind))
  | .clearKey inner kind=>
    let next:=match kind with | .owner=>.clearKey inner .factor | .factor=>if inner then .innerHeader else .outerHeader
    .base (.pop (key inner kind) next (.clearKey inner kind) (.clearKey inner kind))
  | .ownerCall=>.call (.edgeStart .owner) .ownerPossible
  | .ownerPossible=>.base (.pop (aux .eqOutput) .abort (.ownerDrop false) (.ownerDrop true))
  | .ownerDrop false=>.base (.pop (aux .eqOutput) .abort (.factorCall .reject) .abort)
  | .ownerDrop true=>.base (.pop (aux .eqOutput) .abort (.factorCall .stable) (.factorCall .free))
  | .factorCall first=>.call (.edgeStart .factor) (.factorPossible first)
  | .factorPossible first=>.base (.pop (aux .eqOutput) .abort (.factorDrop first false) (.factorDrop first true))
  | .factorDrop first false=>.base (.pop (aux .eqOutput) .abort (.payload first .reject) .abort)
  | .factorDrop first true=>.base (.pop (aux .eqOutput) .abort (.payload first .stable) (.payload first .free))
  | .payload .reject _|.payload _ .reject=>.base (.jump .copySum)
  | .payload .free .free=>.call (.copier (.power .square) 0) .copySum
  | .payload .free .stable|.payload .stable .free=>.call (.copier (.power .cube) 0) .copySum
  | .payload .stable .stable=>.call (.copier (.power .fourth) 0) .copySum
  | .copySum=>.call (.copier .sum 0) .clearTotal
  | .clearTotal=>.base (.pop (aux .total) .add .clearTotal .clearTotal)
  | .add=>.call (.adder (.start false)) (.clearKey true .owner)
  | .restoreQuery=>.call (.copier .restoreQuery 0) .clearSavedQuery
  | .clearSavedQuery=>.base (.pop (aux .savedQuery) .done .clearSavedQuery .clearSavedQuery)
  | .done|.abort=>.base .halt
  | .edgeStart kind=>.call (.copier (.keyLeft kind) 0) (.edgeRight kind)
  | .edgeRight kind=>.call (.copier (.keyRight kind) 0) (.compareKeys kind)
  | .compareKeys kind=>.call (.equality .loop) (.keysEqual kind)
  | .keysEqual kind=>.base (.pop (aux .eqOutput) .abort (.copyQuery kind false) (.status .stable))
  | .copyQuery kind side=>.call (.copier (.query kind side) 0) (.lookup kind side)
  | .lookup kind side=>.call (.environment (.local .lookup)) (.readFound kind side)
  | .readFound kind side=>.base (.pop found .abort (.clearID kind side false) (.copyID kind side))
  | .copyID kind side=>.call (.copier (.id side) 0) (.clearID kind side true)
  | .clearID kind side present=>.base (.pop idOutput (.clearQuery kind side present)
      (.clearID kind side present) (.clearID kind side present))
  | .clearQuery kind side present=>.base (.pop query (.afterLookup kind side present)
      (.clearQuery kind side present) (.clearQuery kind side present))
  | .afterLookup _ false false=>.base (.jump (.status .free))
  | .afterLookup kind false true=>.base (.jump (.copyQuery kind true))
  | .afterLookup _ true false=>.base (.jump .clearFreeLeft)
  | .afterLookup _ true true=>.base (.jump .compareIDs)
  | .clearFreeLeft=>.base (.pop (aux .eqLeft) (.status .free) .clearFreeLeft .clearFreeLeft)
  | .compareIDs=>.call (.equality .loop) .idsEqual
  | .idsEqual=>.base (.pop (aux .eqOutput) .abort (.status .reject) (.status .stable))
  | .status outcome=>.base (.push (aux .eqOutput) (SemiprimeD1StackSourceIncidenceSpec.drop outcome) (.statusPossible outcome))
  | .statusPossible outcome=>.base (.push (aux .eqOutput) (SemiprimeD1StackSourceIncidenceSpec.possible outcome) .edgeReturn)
  | .edgeReturn=>.ret
  | .environment pc=>SemiprimeD1StackValidationLink.instruction environmentStack Label.environment (E.program pc)
  | .copier part pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack part) (Label.copier part) (SemiprimeD1StackCopy.code pc)
  | .parser inner kind pc=>SemiprimeD1StackMultiplierLink.instruction (fieldStack inner kind) (Label.parser inner kind) (Field.code pc)
  | .equality pc=>SemiprimeD1StackMultiplierLink.instruction equalStack Label.equality (Q.code pc)
  | .adder pc=>SemiprimeD1StackMultiplierLink.instruction addStack Label.adder (A.code pc)
/-- Actual multiword prepared input; every private work word starts empty. -/
def data (environment:E.Stack→List Bool) (stream square cube fourth:List Bool) :Stack→List Bool :=
  Sum.elim environment (fun k=>match k with
    | .source=>stream | .square=>square | .cube=>cube | .fourth=>fourth | _=>[])
/-- Whole fixed query entry; acquired environment, occurrence and power lineage remains explicit. -/
def initial (environment:E.Stack→List Bool) (stream square cube fourth:List Bool) :C.State Stack Label :=
  ⟨some .start,none,none,data environment stream square cube fourth,[]⟩
/-- SAME finite compiled query for all physically acquired caches and streams. -/
def machine :Turing.FinTM2 :=SemiprimeD1StackCalls.machine (aux .source) (aux .total) .start program
/-- Actual inventory includes all25 environment fields and22 client words. -/
theorem stack_card :Fintype.card Stack=47 :=by
  rw [Fintype.card_sum,SemiprimeD1StackSourceEnvironment.stack_card]
  decide
/-- Each preserving-copy site's operands are pairwise distinct physical words. -/
theorem copy_injective (part:Copy) :Function.Injective (copyStack part) :=by
  cases part with
  | keyLeft kind|keyRight kind=>cases kind <;> decide
  | query kind side=>cases kind <;> cases side <;> decide
  | id side=>cases side <;> decide
  | power part=>cases part <;> decide
  | _=>decide
/-- The retained complete acquired environment has no alias shadow. -/
theorem environment_injective :Function.Injective environmentStack :=Sum.inl_injective
/-- The four equality roles, including its unused scratch, are distinct. -/
theorem equal_injective :Function.Injective equalStack :=by decide
/-- The four actual ripple-adder roles are distinct. -/
theorem add_injective :Function.Injective addStack :=by decide
/-- Every actual parser instance has four distinct physical operands. -/
theorem field_injective (inner:Bool) (kind:Edge) :Function.Injective (fieldStack inner kind) :=by cases inner <;> cases kind <;> decide
/-- Runtime flags and all labels are finite before every graph/prefix/power input. -/
theorem control_finite :Finite machine.σ :=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- Every47 data and real-return alphabet is fixed finite. -/
theorem alphabets_finite :∀k,Finite (machine.Γ k) :=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackSourceIncidence
