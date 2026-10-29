/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWeightedModeResources
import RiemannGaussian.SemiprimeD1StackPortOwnerMaddExecution
import RiemannGaussian.SemiprimeD1ModeCatalog
/-! # Physical mode-catalogue acquisition and actual feasible-enumerator call
Inputs are actual paid unary packet/tile counts and actual unary precision
WIDTH. Packet construction remains upstream. This finite source multiplies
the counts, visits each order/slot pair, writes literal weights and labels,
then calls the actual feasible DFS. No catalogue or tuple is supplied.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWeightedModeCatalogue
namespace W
export SemiprimeD1StackWeightedMode (Stack Label program initial machine input)
end W
namespace M
export SemiprimeD1StackPortOwnerMadd (Stack Label program data)
end M
namespace C
export SemiprimeD1StackCalls (Instruction State run)
end C
namespace Body
export SemiprimeD1StackAssignmentBody (Stack Label code entry)
end Body
/-- Eleven additional physical Boolean words, including both acquired logs. -/
inductive Aux where
  | orders | weight | order | slotsTodo | slot | word | labelHistory | weightHistory
  | copyScratch | frameScratch | labels
  deriving DecidableEq,Repr
instance :Fintype Aux where
  elems:={.orders,.weight,.order,.slotsTodo,.slot,.word,.labelHistory,.weightHistory,.copyScratch,.frameScratch,.labels}
  complete:=by intro k;cases k <;> simp
/-- All seventeen enumerator roles and seven multiply roles remain allocated. -/
abbrev Stack:=W.Stack⊕(M.Stack⊕Aux)
/-- Literal catalogue iteration locations, independent of every numerical value. -/
inductive Control where
  | start | copyWidth | precisionPred | weightSeed | orderCheck | copySlots | slotCheck
  | emitWeight | frameOrder | frameSlot | emitLabel | clearWord | incrementSlot
  | clearSlot | orderPop | incrementOrder | incrementWeight
  | catalogueSeed | reverseWeights | labelsSeed | reverseLabels | enumerate | done
  deriving DecidableEq,Repr
instance :Fintype Control where
  elems:={.start,.copyWidth,.precisionPred,.weightSeed,.orderCheck,.copySlots,.slotCheck,
    .emitWeight,.frameOrder,.frameSlot,.emitLabel,.clearWord,.incrementSlot,.clearSlot,
    .orderPop,.incrementOrder,.incrementWeight,.catalogueSeed,.reverseWeights,.labelsSeed,
    .reverseLabels,.enumerate,.done}
  complete:=by intro k;cases k <;> simp
/-- Every real program and return alphabet is finite before all metadata inputs. -/
abbrev Label:=Control⊕(W.Label⊕(M.Label⊕((Bool×Fin 9)⊕((Bool×Fin 11)⊕((Bool×Body.Label)⊕(Bool×Fin 4))))))
/-- Literal frontend-word inclusion; no address is supplied by the input. -/
def aux (k:Aux) :Stack:=.inr (.inr k)
/-- Literal inclusion of every enumerator role. -/
def weighted (k:W.Stack) :Stack:=.inl k
/-- Literal inclusion of every real multiplier role. -/
def multiply (k:M.Stack) :Stack:=.inr (.inl k)
/-- Static nested enumerator label inclusion. -/
def weightedLabel (pc:W.Label) :Label:=.inr (.inl pc)
/-- Static nested multiply-plus-offset label inclusion. -/
def multiplyLabel (pc:M.Label) :Label:=.inr (.inr (.inl pc))
/-- Static preserving-copy label inclusion. -/
def copyLabel (slots:Bool) (pc:Fin 9) :Label:=.inr (.inr (.inr (.inl (slots,pc))))
/-- Static two-field framing label inclusion. -/
def frameLabel (slot:Bool) (pc:Fin 11) :Label:=.inr (.inr (.inr (.inr (.inl (slot,pc)))))
/-- Static chronological weight/label logger inclusion. -/
def bodyLabel (weight:Bool) (pc:Body.Label) :Label:=.inr (.inr (.inr (.inr (.inr (.inl (weight,pc))))))
/-- Static acquired-log reversal label inclusion. -/
def reverseLabel (weight:Bool) (pc:Fin 4) :Label:=.inr (.inr (.inr (.inr (.inr (.inr (weight,pc))))))
/-- Actual readonly WIDTH or computed product source, with disjoint scratch. -/
def copyStack (slots:Bool) (k:Fin 3) :Stack:=
  if k=0 then (if slots then multiply (.inr .output) else weighted .width)
  else if k=1 then aux (if slots then .slotsTodo else .orders) else aux .copyScratch
/-- The literal mode record is built order-first, then slot-first. -/
def frameStack (slot:Bool) (k:Fin 3) :Stack:=
  if k=0 then aux (if slot then .slot else .order)
  else if k=1 then aux .word else aux .frameScratch
/-- Each actual weight and label is copied to its chronological reverse log. -/
def bodyStack (weight:Bool) :Body.Stack→Stack
  | .word=>aux (if weight then .weight else .word)
  | .scratch=>aux .copyScratch
  | .history=>aux (if weight then .weightHistory else .labelHistory)
/-- Only actual reversal writes the acquired catalogue and labels. -/
def reverseStack (weight:Bool) (k:Fin 2) :Stack:=
  if k=0 then aux (if weight then .weightHistory else .labelHistory)
  else if weight then weighted .catalogue else aux .labels
local notation "ctl" => (Sum.inl :Control→Label)
/-- The full fixed finite multiplication/catalogue/enumeration source. -/
def program :Label→C.Instruction Stack Label
  | .inl .start=>.call (multiplyLabel (.inl .start)) (ctl .copyWidth)
  | .inl .copyWidth=>.call (copyLabel false 0) (ctl .precisionPred)
  | .inl .precisionPred=>.base (.pop (aux .orders) (ctl .weightSeed) (ctl .weightSeed) (ctl .weightSeed))
  | .inl .weightSeed=>.base (.push (aux .weight) true (ctl .orderCheck))
  | .inl .orderCheck=>.base (.peek (aux .orders) (ctl .catalogueSeed) (ctl .copySlots) (ctl .copySlots))
  | .inl .copySlots=>.call (copyLabel true 0) (ctl .slotCheck)
  | .inl .slotCheck=>.base (.pop (aux .slotsTodo) (ctl .clearSlot) (ctl .emitWeight) (ctl .emitWeight))
  | .inl .emitWeight=>.call (bodyLabel true Body.entry) (ctl .frameOrder)
  | .inl .frameOrder=>.call (frameLabel false 0) (ctl .frameSlot)
  | .inl .frameSlot=>.call (frameLabel true 0) (ctl .emitLabel)
  | .inl .emitLabel=>.call (bodyLabel false Body.entry) (ctl .clearWord)
  | .inl .clearWord=>.base (.pop (aux .word) (ctl .incrementSlot) (ctl .clearWord) (ctl .clearWord))
  | .inl .incrementSlot=>.base (.push (aux .slot) true (ctl .slotCheck))
  | .inl .clearSlot=>.base (.pop (aux .slot) (ctl .orderPop) (ctl .clearSlot) (ctl .clearSlot))
  | .inl .orderPop=>.base (.pop (aux .orders) (ctl .catalogueSeed) (ctl .incrementOrder) (ctl .incrementOrder))
  | .inl .incrementOrder=>.base (.push (aux .order) true (ctl .incrementWeight))
  | .inl .incrementWeight=>.base (.push (aux .weight) true (ctl .orderCheck))
  | .inl .catalogueSeed=>.base (.push (weighted .catalogue) false (ctl .reverseWeights))
  | .inl .reverseWeights=>.call (reverseLabel true 0) (ctl .labelsSeed)
  | .inl .labelsSeed=>.base (.push (aux .labels) false (ctl .reverseLabels))
  | .inl .reverseLabels=>.call (reverseLabel false 0) (ctl .enumerate)
  | .inl .enumerate=>.call (weightedLabel (.inl .start)) (ctl .done)
  | .inl .done=>.base .halt
  | .inr (.inl pc)=>SemiprimeD1StackValidationLink.instruction weighted weightedLabel (W.program pc)
  | .inr (.inr (.inl pc))=>SemiprimeD1StackValidationLink.instruction multiply multiplyLabel (M.program pc)
  | .inr (.inr (.inr (.inl (site,pc))))=>SemiprimeD1StackMultiplierLink.instruction (copyStack site) (copyLabel site) (SemiprimeD1StackCopy.code pc)
  | .inr (.inr (.inr (.inr (.inl (site,pc)))))=>SemiprimeD1StackMultiplierLink.instruction (frameStack site) (frameLabel site) (SemiprimeD1StackFrame.code pc)
  | .inr (.inr (.inr (.inr (.inr (.inl (site,pc))))))=>SemiprimeD1StackMultiplierLink.instruction (bodyStack site) (bodyLabel site) (Body.code pc)
  | .inr (.inr (.inr (.inr (.inr (.inr (site,pc))))))=>SemiprimeD1StackMultiplierLink.instruction (reverseStack site) (reverseLabel site) (SemiprimeD1StackReverseWord.code pc)
/-- Actual metadata front door; no catalogue, feasible tuple, answer or clock is supplied. -/
def input (packets tiles width:List Bool) :Stack→List Bool
  | .inl .width=>width
  | .inr (.inl (.inl .a))=>packets
  | .inr (.inl (.inl .b))=>tiles
  | _=>[]
/-- Prepared physical entry contains only the three actual metadata words. -/
def initial (packets tiles width:List Bool) :C.State Stack Label:=⟨some (ctl .start),none,none,input packets tiles width,[]⟩
/-- One genuine fixed finite machine; its prepared multiword initialization is explicit. -/
def machine:Turing.FinTM2:=SemiprimeD1StackCalls.machine (weighted .width) (weighted .output) (ctl .start) program
theorem stack_card:Fintype.card Stack=35:=by decide
theorem copy_injective (s:Bool):Function.Injective (copyStack s):=by cases s <;> decide
theorem frame_injective (s:Bool):Function.Injective (frameStack s):=by cases s <;> decide
theorem body_injective (s:Bool):Function.Injective (bodyStack s):=by cases s <;> decide
theorem reverse_injective (s:Bool):Function.Injective (reverseStack s):=by cases s <;> decide
theorem weighted_injective:Function.Injective weighted:=Sum.inl_injective
theorem multiply_injective:Function.Injective multiply:=by intro a b h;exact Sum.inl.inj (Sum.inr.inj h)
theorem control_finite:Finite machine.σ:=SemiprimeD1StackCalls.control_finite _ _ _ _
theorem alphabets_finite:∀k,Finite (machine.Γ k):=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackWeightedModeCatalogue
