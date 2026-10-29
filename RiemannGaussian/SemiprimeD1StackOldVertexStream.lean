/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOldVertexStreamRoles
import RiemannGaussian.SemiprimeD1StackChildVertexChoiceOriginal
/-! # Physical chronological zip of every original child vertex
Parent record fields, activity bits and the acquired scope/order vectors are
read in lockstep. Each real whole vertex call is followed by one EOF splice
and a complete physical workspace sweep. The history is reversed only once.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOldVertexStream
open SemiprimeD1StackOldVertexStreamRoles
namespace X
export SemiprimeD1StackChildVertexChoice (Label program output activity)
end X
namespace P
export SemiprimeD1TensorTapeFieldBytecode (Label code active)
end P
namespace S
export SemiprimeD1StackVertexRecordSplice (Label program)
end S
namespace C
export SemiprimeD1StackCalls (State Instruction)
end C
/-- Four physically preserved input streams, each copied exactly once. -/
inductive Copy where | records | activation | scopes | orders deriving DecidableEq
/-- Exactly the four fixed initial copy sites. -/
instance copyFintype : Fintype Copy:=Fintype.ofList [.records,.activation,.scopes,.orders] (by intro k;cases k <;> simp)
/-- Four literal parser sites; acquired port numbers never become instruction labels. -/
inductive Field where | ports | table | scope | order deriving DecidableEq
/-- Exactly the four literal field-parser sites. -/
instance fieldFintype : Fintype Field:=Fintype.ofList [.ports,.table,.scope,.order] (by intro k;cases k <;> simp)
/-- Fixed caller stages, including every one of the169 physical cleanup sites. -/
inductive Control where
  | start | copyActivation | copyScopes | copyOrders | recordTag
  | ports | portsValid | table | tableValid | scopeTag | scope | scopeValid
  | orderTag | order | orderValid | activity | setActivity (bit : Bool)
  | vertex | splice | clearPorts | clearWork (position : Fin 169)
  | checkRecordEnd | checkActivationEnd | scopeEnd | checkScopeEnd
  | orderEnd | checkOrderEnd | seed | reverse | success | done | abort
  deriving DecidableEq, Fintype
/-- All labels are finite literal source/copy/parser sites. -/
inductive Label where
  | local (pc : Control) | copy (site : Copy) (pc : Fin 9)
  | field (site : Field) (pc : P.Label) | vertex (pc : X.Label)
  | splice (pc : S.Label) | reverse (pc : Fin 4)
  deriving Fintype
/-- Actual old parent table retained by the active source template. -/
def parentRole : ChoiceStack:=.inl (A.table (V.template (E.aux .parentTable)))
/-- Actual acquired canonical order, read by that same template. -/
def orderRole : ChoiceStack:=.inl (A.table (V.template (E.aux .order)))
/-- Actual acquired child scope, read by the same source's physical dimension counter. -/
def scopeRole : ChoiceStack:=.inl (A.table (V.counter .bank))
/-- Each parser consumes its current physical reader. -/
def fieldInput : Field→Stack
  | .ports|.table=>aux .recordsReader | .scope=>aux .scopesReader | .order=>aux .ordersReader
/-- Parsed words enter the real vertex-source operands directly. -/
def fieldOutput : Field→Stack
  | .ports=>aux .oldPorts | .table=>choice parentRole
  | .scope=>choice scopeRole | .order=>choice orderRole
/-- All four parser roles, including real scratch and validity. -/
def fieldStack (site : Field) : F.Stack→Stack
  | .inl .input=>fieldInput site | .inl .output=>fieldOutput site
  | .inl .scratch=>fieldWork (.inl .scratch) | .inr ()=>fieldWork (.inr ())
/-- Literal source and destination addresses for each of the four initial copies. -/
def copyEnds : Copy→Aux×Aux
  | .records=>(.records,.recordsReader) | .activation=>(.activation,.activationReader)
  | .scopes=>(.scopes,.scopesReader) | .orders=>(.orders,.ordersReader)
/-- Preserving copies share one scratch word; the source and reader remain distinct. -/
def copyStack (site : Copy) (pc : Fin 3) : Stack:=
  if pc=0 then aux (copyEnds site).1 else if pc=1 then aux (copyEnds site).2 else aux .copyScratch
/-- Only the newly acquired singleton and accumulated history are visited by the splicer. -/
def spliceStack (pc : Fin 2) : Stack:=if pc=0 then choice X.output else aux .history
/-- A single final consuming reversal restores chronological output order. -/
def reverseStack (pc : Fin 2) : Stack:=if pc=0 then aux .history else aux .output
/-- Literal source: actual stream parsing, real whole169 call, linear splice and complete cleanup. -/
def program : Label→C.Instruction Stack Label
  | .local .start=>.call (.copy .records 0) (.local .copyActivation)
  | .local .copyActivation=>.call (.copy .activation 0) (.local .copyScopes)
  | .local .copyScopes=>.call (.copy .scopes 0) (.local .copyOrders)
  | .local .copyOrders=>.call (.copy .orders 0) (.local .recordTag)
  | .local .recordTag=>.base (.pop (aux .recordsReader) (.local .abort) (.local .checkRecordEnd) (.local .ports))
  | .local .ports=>.call (.field .ports (P.active .tagPop (none,false))) (.local .portsValid)
  | .local .portsValid=>.base (.pop (fieldWork (.inr ())) (.local .abort) (.local .abort) (.local .table))
  | .local .table=>.call (.field .table (P.active .tagPop (none,false))) (.local .tableValid)
  | .local .tableValid=>.base (.pop (fieldWork (.inr ())) (.local .abort) (.local .abort) (.local .scopeTag))
  | .local .scopeTag=>.base (.pop (aux .scopesReader) (.local .abort) (.local .abort) (.local .scope))
  | .local .scope=>.call (.field .scope (P.active .tagPop (none,false))) (.local .scopeValid)
  | .local .scopeValid=>.base (.pop (fieldWork (.inr ())) (.local .abort) (.local .abort) (.local .orderTag))
  | .local .orderTag=>.base (.pop (aux .ordersReader) (.local .abort) (.local .abort) (.local .order))
  | .local .order=>.call (.field .order (P.active .tagPop (none,false))) (.local .orderValid)
  | .local .orderValid=>.base (.pop (fieldWork (.inr ())) (.local .abort) (.local .abort) (.local .activity))
  | .local .activity=>.base (.pop (aux .activationReader) (.local .abort) (.local (.setActivity false)) (.local (.setActivity true)))
  | .local (.setActivity bit)=>.base (.push (choice X.activity) bit (.local .vertex))
  | .local .vertex=>.call (.vertex (.local .start)) (.local .splice)
  | .local .splice=>.call (.splice (.local .start)) (.local .clearPorts)
  | .local .clearPorts=>.base (.pop (aux .oldPorts) (.local (.clearWork 0)) (.local .clearPorts) (.local .clearPorts))
  | .local (.clearWork i)=>.base (.pop (work (role i))
      (if h:i.val<168 then .local (.clearWork ⟨i.val+1,by omega⟩) else .local .recordTag)
      (.local (.clearWork i)) (.local (.clearWork i)))
  | .local .checkRecordEnd=>.base (.pop (aux .recordsReader) (.local .checkActivationEnd) (.local .abort) (.local .abort))
  | .local .checkActivationEnd=>.base (.pop (aux .activationReader) (.local .scopeEnd) (.local .abort) (.local .abort))
  | .local .scopeEnd=>.base (.pop (aux .scopesReader) (.local .abort) (.local .checkScopeEnd) (.local .abort))
  | .local .checkScopeEnd=>.base (.pop (aux .scopesReader) (.local .orderEnd) (.local .abort) (.local .abort))
  | .local .orderEnd=>.base (.pop (aux .ordersReader) (.local .abort) (.local .checkOrderEnd) (.local .abort))
  | .local .checkOrderEnd=>.base (.pop (aux .ordersReader) (.local .seed) (.local .abort) (.local .abort))
  | .local .seed=>.base (.push (aux .output) false (.local .reverse))
  | .local .reverse=>.call (.reverse 0) (.local .success)
  | .local .success=>.base (.push (aux .success) true (.local .done))
  | .local .done|.local .abort=>.base .halt
  | .copy site pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack site) (Label.copy site) (SemiprimeD1StackCopy.code pc)
  | .field site pc=>SemiprimeD1StackMultiplierLink.instruction (fieldStack site) (Label.field site) (P.code pc)
  | .vertex pc=>SemiprimeD1StackValidationLink.instruction choice Label.vertex (X.program pc)
  | .splice pc=>SemiprimeD1StackValidationLink.instruction spliceStack Label.splice (S.program pc)
  | .reverse pc=>SemiprimeD1StackMultiplierLink.instruction reverseStack Label.reverse (SemiprimeD1StackReverseWord.code pc)
/-- Eight genuine physical words: current parent records, three acquired streams and distinct headers. -/
structure Inputs where
  /-- Complete original current parent record tape. -/
  records : List Bool
  /-- Entire acquired owner-first activity mask. -/
  activation : List Bool
  /-- Acquired framed vector of actual scope rows. -/
  scopes : List Bool
  /-- Acquired framed vector of actual canonical order rows. -/
  orders : List Bool
  /-- Actual old axis-vector header. -/
  oldAxes : List Bool
  /-- Actual old binary tensor precision. -/
  oldPrecision : List Bool
  /-- Appended new axis-vector header. -/
  newAxes : List Bool
  /-- Actual new binary tensor precision. -/
  newPrecision : List Bool
/-- Initial input bank; every reader, helper, history and displaced shadow starts empty. -/
def inputData (i : Inputs) : Stack→List Bool:=Sum.elim (fun _=>[]) (Sum.elim (fun _=>[]) (fun k=>match k with
  | .records=>i.records | .activation=>i.activation | .scopes=>i.scopes | .orders=>i.orders
  | .oldAxes=>i.oldAxes | .oldPrecision=>i.oldPrecision | .newAxes=>i.newAxes | .newPrecision=>i.newPrecision
  | _=>[]))
/-- Same literal enclosing source starts from only its eight physical operands. -/
def initial (i : Inputs) : C.State Stack Label:=⟨some (.local .start),none,none,inputData i,[]⟩
/-- Actual fixed190-role compiled Boolean machine. -/
def machine : Turing.FinTM2:=SemiprimeD1StackCalls.machine (aux .records) (aux .output) (.local .start) program
/-- Each parser has four distinct source/output/scratch/validity addresses. -/
theorem field_injective (site : Field) : Function.Injective (fieldStack site):=by cases site <;> decide
/-- Each physical preserving copy uses three distinct actual words. -/
theorem copy_injective (site : Copy) : Function.Injective (copyStack site):=by cases site <;> decide
/-- The exact two-word splicer changes no source metadata/header location. -/
theorem splice_injective : Function.Injective spliceStack:=by decide
/-- The final reversal has distinct history and output addresses. -/
theorem reverse_injective : Function.Injective reverseStack:=by decide
/-- All control labels are fixed finite before any graph, word, coefficient or dimension. -/
theorem control_finite : Finite machine.σ:=SemiprimeD1StackCalls.control_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackOldVertexStream
