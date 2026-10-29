/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildLiftVertexMeaning
import RiemannGaussian.SemiprimeD1StackChildUnitVertexMeaning
import RiemannGaussian.SemiprimeD1StackVertexRecordSpliceStorage
/-! # Complete literal old-vertex stream workspace and immutable header aliases
These are fixed source locations only. Current parent records and acquired
activity/scope/order streams are physical words. No table dictionary, native
getter or data-valued instruction label is introduced by the role inventory.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOldVertexStreamRoles
namespace A
export SemiprimeD1StackChildLiftVertex (Stack table aux stack_card)
end A
namespace U
export SemiprimeD1StackChildUnitVertex (Stack context unitWork aux stack_card)
end U
namespace V
export SemiprimeD1StackVectorTable (checker template counter aux)
end V
namespace E
export SemiprimeD1StackChildTableEntry (Stack context aux)
end E
namespace J
export SemiprimeD1StackJetContext (axesCache precisionBits)
end J
namespace F
export SemiprimeD1TensorTapeFieldBytecode (Stack)
end F
/-- The exact whole169-word activity-source allocation, described without importing an unsealed caller. -/
abbrev ChoiceStack:=A.Stack⊕(U.Stack⊕Unit)
/-- Eight immutable inputs, four actual readers, old-port disposal and real logging/copy/status work. -/
inductive Aux where
  | records | activation | scopes | orders | oldAxes | oldPrecision | newAxes | newPrecision
  | recordsReader | activationReader | scopesReader | ordersReader | oldPorts | history | output | copyScratch | success
  deriving DecidableEq,Repr
instance auxFintype : Fintype Aux:=Fintype.ofList
  [.records,.activation,.scopes,.orders,.oldAxes,.oldPrecision,.newAxes,.newPrecision,
    .recordsReader,.activationReader,.scopesReader,.ordersReader,.oldPorts,.history,.output,.copyScratch,.success]
    (by intro k;cases k <;> simp)
/-- All169 source words, all4 parser words and all17 enclosing words, including every displaced shadow. -/
abbrev Stack:=ChoiceStack⊕(F.Stack⊕Aux)
/-- Dedicated complete activity-source work bank; its four displaced headers remain counted. -/
def work (k : ChoiceStack) : Stack:=.inl k
/-- All actual parser work and both unused input/output shadows. -/
def fieldWork (k : F.Stack) : Stack:=.inr (.inl k)
/-- Fixed actual enclosing-stream address. -/
def aux (k : Aux) : Stack:=.inr (.inr k)
/-- The actual old/new original axis-header locations in the whole active source. -/
def axesRole (new : Bool) : ChoiceStack:=.inl (A.table (V.template (E.context new J.axesCache)))
/-- The actual old/new original binary-precision locations in that source. -/
def precisionRole (new : Bool) : ChoiceStack:=.inl (A.table (V.template (E.context new J.precisionBits)))
/-- All four caller input headers are read IN PLACE by the included source; its displaced shadows are empty. -/
def choice (k : ChoiceStack) : Stack:=
  if k=axesRole false then aux .oldAxes
  else if k=precisionRole false then aux .oldPrecision
  else if k=axesRole true then aux .newAxes
  else if k=precisionRole true then aux .newPrecision else work k
/-- Table/counting roles are literal fixed constructors, never runtime graph indices. -/
def tableRoles : List SemiprimeD1StackChildLiftTable.Stack:=
  SemiprimeD1StackChildLiftTable.roles.map V.checker++
    SemiprimeD1StackChildLiftTable.roles.map V.template++
    ([.bank,.reader,.count,.word,.fieldScratch,.valid,.copyScratch] : List SemiprimeD1StackDigitCount.Stack).map V.counter++
    [V.aux .prefix,V.aux .work,V.aux .scratch,V.aux .reversed,V.aux .output]
/-- Both complete active-record words and every original table word are counted. -/
def activeRoles : List A.Stack:=tableRoles.map A.table++[A.aux .record,A.aux .scratch]
/-- Full literal dense-unit arithmetic allocation, including precision/work and all nine vector roles. -/
def unitRoles : List SemiprimeD1StackJetUnit.Stack:=
  [.inl (.inl .left),.inl (.inl .right),.inl (.inl .scratch),.inl (.inl .output),
    .inl (.inr false),.inl (.inr true),.inr .leftTape,.inr .rightTape,.inr .rank,.inr .active,
    .inr .reverseOut,.inr .output,.inr .valid,.inr .parser,.inr .copy]
/-- The inactive source retains both full context/unit banks and both new record words. -/
def inactiveRoles : List U.Stack:=SemiprimeD1StackChildLiftTable.contextRoles.map U.context++
  unitRoles.map U.unitWork++[U.aux .record,U.aux .scratch]
/-- Every actual role in the169-word branch source, in a constant literal cleanup order. -/
def choiceRoles : List ChoiceStack:=activeRoles.map Sum.inl++inactiveRoles.map (fun k=>.inr (.inl k))++[.inr (.inr ())]
/-- No source/template/helper/framing/activity shadow is omitted. -/
theorem choice_roles_length : choiceRoles.length=169:=by decide
/-- No physical source word is counted twice. -/
theorem choice_roles_nodup : choiceRoles.Nodup:=by decide
/-- The complete physical activity-source allocation is169 independent of all inputs. -/
theorem choice_card : Fintype.card ChoiceStack=169:=by
  have h : Fintype.card Unit=1:=by decide
  rw [Fintype.card_sum,A.stack_card,Fintype.card_sum,U.stack_card,h]
/-- Literal inventory cardinality proves complete169-role coverage. -/
theorem choice_roles_complete (k : ChoiceStack) : k∈choiceRoles:=by
  have h : choiceRoles.toFinset.card=Fintype.card ChoiceStack:=by
    rw [List.toFinset_card_of_nodup choice_roles_nodup,choice_roles_length,choice_card]
  have hu:=Finset.eq_univ_of_card choiceRoles.toFinset h
  apply List.mem_toFinset.mp
  rw [hu]
  exact Finset.mem_univ k
/-- Fixed cleanup positions are bounded literal code sites, never acquired port IDs. -/
def role (i : Fin 169) : ChoiceStack:=choiceRoles[i.val]'(by rw [choice_roles_length];exact i.isLt)
/-- Every actual included-source word is cleaned exactly once. -/
theorem role_injective : Function.Injective role:=by
  intro a b h
  apply Fin.ext
  exact choice_roles_nodup.getElem_inj.mp h
/-- Every physical work/shadow word has an actual bounded cleanup position. -/
theorem role_complete (k : ChoiceStack) : ∃i : Fin 169,role i=k:=by
  obtain ⟨i,hi,he⟩:=List.mem_iff_getElem.mp (choice_roles_complete k)
  exact ⟨⟨i,by rw [←choice_roles_length];exact hi⟩,he⟩
/-- Sharing four original headers preserves distinct addresses inside the included source. -/
theorem choice_injective : Function.Injective choice:=by decide
/-- Every data role, including all displaced source/parser shadows and all input caches, is counted. -/
theorem stack_card : Fintype.card Stack=190:=by
  have hf : Fintype.card F.Stack=4:=by decide
  have ha : Fintype.card Aux=17:=by decide
  rw [Fintype.card_sum,choice_card,Fintype.card_sum,hf,ha]
end RiemannGaussian.SemiprimeD1StackOldVertexStreamRoles
