/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackInputDescriptorRecordOriginal
import RiemannGaussian.SemiprimeD1StackCarryDescriptorRecord
import RiemannGaussian.SemiprimeD1StackScaleDescriptorRecordOriginal
import RiemannGaussian.SemiprimeD1StackTransformDescriptorRecordOriginal
import RiemannGaussian.SemiprimeD1StackProductRecordOriginal
import RiemannGaussian.SemiprimeD1StackBoundaryRecordOriginal
import RiemannGaussian.SemiprimeD1StackBooleanRecordOriginal
/-! # One actual original eighteen-tag descriptor-to-record dispatcher
Only six acquired original words, a physical binary scope and caller
accumulators enter. A paid tag copy and bounded true-marker decoder select a
literal component call. Every allocated private word is physically drained
before returning, including dormant aliases. No mode/table/count is supplied.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 1000000
namespace RiemannGaussian.SemiprimeD1StackAllDescriptorRecord
namespace C
export SemiprimeD1StackCalls (Instruction State run)
end C
namespace I
export SemiprimeD1StackInputDescriptorRecord (Stack Label program)
end I
namespace A
export SemiprimeD1StackCarryDescriptorRecord (Stack Label program)
end A
namespace S
export SemiprimeD1StackScaleDescriptorRecord (Stack Label program)
end S
namespace T
export SemiprimeD1StackTransformDescriptorRecord (Stack Label program)
end T
namespace P
export SemiprimeD1StackProductRecord (Stack Label program)
end P
namespace Z
export SemiprimeD1StackBoundaryRecord (Stack Label program)
end Z
namespace B
export SemiprimeD1StackBooleanRecord (Stack Label program)
end B
/-- Exactly six original fields, physical scope/caller words and paid tag work. -/
inductive Common where | source (part : Fin 6) | bank | history | output | tagReader | copyScratch
  deriving DecidableEq
instance : Fintype Common :=Fintype.ofList
  ((List.finRange 6).map .source++[.bank,.history,.output,.tagReader,.copyScratch])
  (by intro k;cases k <;> simp)
/-- All1252 allocated component words, including every unused shared-input shadow. -/
abbrev Private :=I.Stack⊕(A.Stack⊕(S.Stack⊕(T.Stack⊕(P.Stack⊕(Z.Stack⊕B.Stack)))))
/-- All1263 physical Boolean data words, fixed before original N. -/
abbrev Stack :=Common⊕Private
/-- Cached equality for this one fixed allocated private inventory. -/
instance privateDecidableEq : DecidableEq Private :=inferInstance
/-- Cached equality for this one fixed1263-role physical store. -/
instance stackDecidableEq : DecidableEq Stack :=inferInstance
/-- One actual acquired source field: N/tag/coord0/coord1/coord2/coord3. -/
def source (part : Fin 6) : Stack :=.inl (.source part)
/-- Actual acquired binary occurrence-ID vector. -/
def scopeBank : Stack :=.inl .bank
/-- Caller accumulated reverse chronological row log. -/
def history : Stack :=.inl .history
/-- Caller final output suffix. -/
def output : Stack :=.inl .output
/-- Physical tag-copy reader. -/
def tagReader : Stack :=.inl .tagReader
/-- Physical preserving-copy scratch. -/
def copyScratch : Stack :=.inl .copyScratch
/-- Raw private slot embedding, deliberately distinct from every shared alias. -/
def privateStack (k : Private) : Stack :=.inr k
/-- Ordinary metadata-loader aliases; all sources and both caller words remain shared. -/
def metadataAlias {K : Type} : SemiprimeD1StackDescriptorRecord.Stack K→Option Common
  | .inr (.inl i)=>some (.source i)
  | .inl (.inl (.inr (.inr (.inl .bank))))=>some .bank
  | .inl (.inr (.inr .history))=>some .history
  | .inl (.inr (.inr .output))=>some .output
  | _=>none
/-- Physically decoded selectors stay private; original raw tag/coord0 stay shared. -/
def selectedAlias {K : Type} : SemiprimeD1StackSelectedDescriptorRecord.Stack K→Option Common
  | .inr .tag=>some (.source 1)
  | .inr .transform=>some (.source 2)
  | .inr _=>none
  | .inl k=>match metadataAlias k with
    | some (.source i)=>if i=1 ∨ i=2 then none else some (.source i)
    | value=>value
/-- The product compiler reads actual shared binary N and binary scope directly. -/
def productAlias : P.Stack→Option Common
  | .inl (.inr .source)=>some (.source 0)
  | .inr (.inl .bank)=>some .bank
  | .inr (.inr .history)=>some .history
  | .inr (.inr .output)=>some .output
  | _=>none
/-- The same actual boundary table serves both original carry endpoints. -/
def boundaryAlias (k : Z.Stack) : Option Common :=
  if k=SemiprimeD1StackBoundaryRecord.original then some (.source 0) else
  match k with
  | .inr (.inl .bank)=>some .bank
  | .inr (.inr .history)=>some .history
  | .inr (.inr .output)=>some .output
  | _=>none
/-- Literal Boolean sources need the actual scope and caller accumulators only. -/
def booleanAlias : B.Stack→Option Common
  | .inr (.inl .bank)=>some .bank
  | .inr (.inr .history)=>some .history
  | .inr (.inr .output)=>some .output
  | _=>none
/-- Actual input client wiring, with all inactive slots still allocated. -/
def inputStack (k : I.Stack) : Stack :=(metadataAlias k).elim (privateStack (.inl k)) Sum.inl
/-- Actual carry client wiring. -/
def carryStack (k : A.Stack) : Stack :=(metadataAlias k).elim (privateStack (.inr (.inl k))) Sum.inl
/-- Actual scale client wiring with privately computed inverse. -/
def scaleStack (k : S.Stack) : Stack :=(selectedAlias k).elim (privateStack (.inr (.inr (.inl k)))) Sum.inl
/-- Actual first/second transform wiring with both privately computed selectors. -/
def transformStack (k : T.Stack) : Stack :=(selectedAlias k).elim (privateStack (.inr (.inr (.inr (.inl k))))) Sum.inl
/-- Actual N-only product table/ordinal/logger source wiring. -/
def productStack (k : P.Stack) : Stack :=(productAlias k).elim (privateStack (.inr (.inr (.inr (.inr (.inl k)))))) Sum.inl
/-- Actual N-only zero-boundary source wiring. -/
def boundaryStack (k : Z.Stack) : Stack :=(boundaryAlias k).elim (privateStack (.inr (.inr (.inr (.inr (.inr (.inl k))))))) Sum.inl
/-- Actual finite Boolean table source wiring. -/
def booleanStack (k : B.Stack) : Stack :=(booleanAlias k).elim (privateStack (.inr (.inr (.inr (.inr (.inr (.inr k))))))) Sum.inl
/-- Fixed complete digit-counter inventory. -/
def counterRoles : List SemiprimeD1StackDigitCount.Stack :=[.bank,.reader,.count,.word,.fieldScratch,.valid,.copyScratch]
/-- Fixed complete actual stream-serializer inventory, including its unused alias. -/
def scopeRoles : List SemiprimeD1StackPortOrdinalStream.Stack :=
  [.bank,.reader,.word,.fieldScratch,.valid,.copyScratch,.digits,.unaryScratch,.unary,.logScratch,.history,.output]
/-- Fixed complete actual row logger inventory, including its input shadows. -/
def loggerRoles : List SemiprimeD1StackVertexRecordStream.Stack :=[.ports,.table,.history,.output]
/-- Literal role inventory for a whole static record compiler. -/
def staticRecordRoles {K : Type} (roles : List K) : List (SemiprimeD1StackStaticRecord.Stack K) :=
  roles.map (fun k=>.inl (.inl k))++roles.map (fun k=>.inl (.inr (.inl k)))++
    counterRoles.map (fun k=>.inl (.inr (.inr (.inl k))))++
    ([.prefix,.work,.scratch,.reversed,.output]:List SemiprimeD1StackStaticTable.Aux).map
      (fun k=>.inl (.inr (.inr (.inr k))))++scopeRoles.map (fun k=>.inr (.inl k))++loggerRoles.map (fun k=>.inr (.inr k))
/-- Literal role inventory for the actual complete template loader. -/
def metadataRoles {K : Type} (roles : List K) : List (SemiprimeD1StackDescriptorRecord.Stack K) :=
  (staticRecordRoles roles).map Sum.inl++(List.finRange 6).map (fun k=>.inr (.inl k))++[.inr (.inr ())]
/-- Literal complete finite-selector inventory, including both unused output shadows. -/
def selectorRoles : List SemiprimeD1StackTransformSelectors.Stack :=[.tag,.transform,.tagReader,.transformReader,.scratch,.stage,.inverse]
/-- Literal role inventory for actual selector acquisition followed by metadata loading. -/
def selectedRoles {K : Type} (roles : List K) : List (SemiprimeD1StackSelectedDescriptorRecord.Stack K) :=
  (metadataRoles roles).map Sum.inl++selectorRoles.map Sum.inr
/-- All actual product-table, serializer and row-logger roles. -/
def productRoles : List P.Stack :=
  (SemiprimeD1StackProductTable.checkerRoles.map Sum.inl++
    ([.source,.depth,.prefix,.work,.scratch,.reversed,.output]:List SemiprimeD1StackProductTable.Aux).map Sum.inr).map Sum.inl++
      scopeRoles.map (fun k=>.inr (.inl k))++loggerRoles.map (fun k=>.inr (.inr k))
/-- All actual public-source/boundary-tree, serializer and row-logger roles. -/
def boundaryRoles : List Z.Stack :=
  ((SemiprimeD1StackPublicInputTable.publicRoles.map Sum.inl)++
    ([.input,.depth,.history,.output]:List SemiprimeD1StackBooleanTree.Stack).map Sum.inr).map Sum.inl++
      scopeRoles.map (fun k=>.inr (.inl k))++loggerRoles.map (fun k=>.inr (.inr k))
/-- Every literal Boolean table/serializer/logger role. -/
def booleanRoles : List B.Stack :=[Sum.inl ()]++scopeRoles.map (fun k=>.inr (.inl k))++loggerRoles.map (fun k=>.inr (.inr k))
/-- Exactly all1252 physical PRIVATE slots, including unused shared-input shadows. -/
def privateRoles : List Private :=
  (metadataRoles SemiprimeD1StackPublicInputTable.roles).map Sum.inl++
  (metadataRoles SemiprimeD1StackPublicCarryTable.roles).map (fun k=>.inr (.inl k))++
  (selectedRoles SemiprimeD1StackPublicScaleTable.roles).map (fun k=>.inr (.inr (.inl k)))++
  (selectedRoles SemiprimeD1StackPublicTransformTable.roles).map (fun k=>.inr (.inr (.inr (.inl k))))++
  productRoles.map (fun k=>.inr (.inr (.inr (.inr (.inl k)))))++
  boundaryRoles.map (fun k=>.inr (.inr (.inr (.inr (.inr (.inl k))))))++
  booleanRoles.map (fun k=>.inr (.inr (.inr (.inr (.inr (.inr k))))))
/-- The fixed cleanup code has exactly1252 literal physical positions. -/
theorem privateRoles_length : privateRoles.length=1252 :=by decide
/-- One fixed private word at a literal finite cleanup-control position. -/
def privateAt (position : Fin 1252) : Private :=privateRoles[position.val]'(by rw [privateRoles_length];exact position.isLt)
/-- Finite family stages are reached ONLY through actual descriptor-tag pops. -/
inductive Family where | input | carry | scale | transform | product | boundary | boolean (mode : SemiprimeD1StackBooleanEntry.Mode)
  deriving DecidableEq,Fintype
/-- Complete literal dispatcher and1252-position physical cleanup control. -/
inductive Control where | start | decode (count : Fin 18) | record (family : Family) | clear (position : Fin 1253) | done | abort
  deriving DecidableEq,Fintype
/-- Every included component return label, fixed before original N. -/
abbrev ComponentLabel :=I.Label⊕(A.Label⊕(S.Label⊕(T.Label⊕(P.Label⊕(Z.Label⊕B.Label)))))
/-- All actual dispatcher, preserving-copy and component labels. -/
abbrev Label :=Control⊕(Fin 9⊕ComponentLabel)
/-- Literal included input-client label. -/
def inputLabel (pc : I.Label) : Label :=.inr (.inr (.inl pc))
/-- Literal included carry-client label. -/
def carryLabel (pc : A.Label) : Label :=.inr (.inr (.inr (.inl pc)))
/-- Literal included scale-client label. -/
def scaleLabel (pc : S.Label) : Label :=.inr (.inr (.inr (.inr (.inl pc))))
/-- Literal included first/second transform-client label. -/
def transformLabel (pc : T.Label) : Label :=.inr (.inr (.inr (.inr (.inr (.inl pc)))))
/-- Literal included product-client label. -/
def productLabel (pc : P.Label) : Label :=.inr (.inr (.inr (.inr (.inr (.inr (.inl pc))))))
/-- Literal included zero-boundary-client label. -/
def boundaryLabel (pc : Z.Label) : Label :=.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl pc)))))))
/-- Literal included Boolean table-source label. -/
def booleanLabel (pc : B.Label) : Label :=.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr pc)))))))
/-- Fixed exhaustive eighteen-tag mapping, never an input mode or answer. -/
def dispatch (code : Fin 18) : Label :=.inl (.record (
  if code.val=0 then .input else if code.val=1 then .transform else if code.val=2 then .scale
  else if code.val=3 then .transform else if code.val=4 then .product else if code.val=5 then .boundary
  else if code.val=6 then .carry else if code.val=7 then .boundary else if code.val=8 then .boolean .orGate
  else if code.val=9 then .boolean .inputCheck else .boolean .equality))
/-- One bounded true constructor-marker read; overflow goes to real abort. -/
def nextDecode (code : Fin 18) : Label :=if h:code.val<17 then .inl (.decode ⟨code.val+1,by omega⟩) else .inl .abort
/-- Three distinct actual preserving tag-copy operands. -/
def copyStack (i : Fin 3) : Stack :=if i=0 then source 1 else if i=1 then tagReader else copyScratch
/-- One literal actual cached-descriptor dispatcher and complete physical private drain. -/
def program : Label→C.Instruction Stack Label
  | .inl .start=>.call (.inr (.inl 0)) (.inl (.decode 0))
  | .inl (.decode code)=>.base (.pop tagReader (dispatch code) (.inl .abort) (nextDecode code))
  | .inl (.record family)=>match family with
    | .input=>.call (inputLabel (.inl .start)) (.inl (.clear 0))
    | .carry=>.call (carryLabel (.inl .start)) (.inl (.clear 0))
    | .scale=>.call (scaleLabel (.inl .start)) (.inl (.clear 0))
    | .transform=>.call (transformLabel (.inl .start)) (.inl (.clear 0))
    | .product=>.call (productLabel (.inl .start)) (.inl (.clear 0))
    | .boundary=>.call (boundaryLabel (.inl .start)) (.inl (.clear 0))
    | .boolean mode=>.call (booleanLabel (.inl (.start mode))) (.inl (.clear 0))
  | .inl (.clear position)=>if h:position.val<1252 then
      .base (.pop (privateStack (privateAt ⟨position.val,h⟩)) (.inl (.clear ⟨position.val+1,by omega⟩))
        (.inl (.clear position)) (.inl (.clear position))) else .base (.jump (.inl .done))
  | .inl .done|.inl .abort=>.base .halt
  | .inr (.inl pc)=>SemiprimeD1StackMultiplierLink.instruction copyStack (fun pc=>.inr (.inl pc)) (SemiprimeD1StackCopy.code pc)
  | .inr (.inr (.inl pc))=>SemiprimeD1StackValidationLink.instruction inputStack inputLabel (I.program pc)
  | .inr (.inr (.inr (.inl pc)))=>SemiprimeD1StackValidationLink.instruction carryStack carryLabel (A.program pc)
  | .inr (.inr (.inr (.inr (.inl pc))))=>SemiprimeD1StackValidationLink.instruction scaleStack scaleLabel (S.program pc)
  | .inr (.inr (.inr (.inr (.inr (.inl pc)))))=>SemiprimeD1StackValidationLink.instruction transformStack transformLabel (T.program pc)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl pc))))))=>SemiprimeD1StackValidationLink.instruction productStack productLabel (P.program pc)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl pc)))))))=>SemiprimeD1StackValidationLink.instruction boundaryStack boundaryLabel (Z.program pc)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr pc)))))))=>SemiprimeD1StackValidationLink.instruction booleanStack booleanLabel (B.program pc)
/-- Actual retained common data, including empty tag/copy work. -/
def commonData (raw : Fin 6→List Bool) (bank hist out : List Bool) : Common→List Bool
  | .source i=>raw i | .bank=>bank | .history=>hist | .output=>out | .tagReader|.copyScratch=>[]
/-- Complete clean private store; no template, selector, table, arity or verdict is supplied. -/
def cleanData (raw : Fin 6→List Bool) (bank hist out : List Bool) : Stack→List Bool :=
  Sum.elim (commonData raw bank hist out) (fun _=>[])
/-- Only physically acquired N/descriptor/scope bytes and caller accumulators. -/
def initial (raw : Fin 6→List Bool) (bank hist out : List Bool) : C.State Stack Label :=
  ⟨some (.inl .start),none,none,cleanData raw bank hist out,[]⟩
/-- Genuine fixed1263-role finite machine with the actual enlarged return alphabet. -/
def machine : Turing.FinTM2 :=SemiprimeD1StackCalls.machine (source 0) output (.inl .start) program
/-- Every allocated private and common role, including all aliases/shadows, is counted. -/
theorem stack_card : Fintype.card Stack=1263 :=by
  have hi:=SemiprimeD1StackInputDescriptorRecord.stack_card
  have ha:=SemiprimeD1StackCarryDescriptorRecord.stack_card
  have hs:=SemiprimeD1StackScaleDescriptorRecord.stack_card
  have ht:=SemiprimeD1StackTransformDescriptorRecord.stack_card
  have hp:=SemiprimeD1StackProductRecord.stack_card
  have hz:=SemiprimeD1StackBoundaryRecord.stack_card
  have hb:=SemiprimeD1StackBooleanRecord.stack_card
  have hc:Fintype.card Common=11:=by decide
  change Fintype.card (Common⊕Private)=_
  simp only [Fintype.card_sum,Private] at *
  omega
end RiemannGaussian.SemiprimeD1StackAllDescriptorRecord
