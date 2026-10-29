/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPacketInventorySources
import RiemannGaussian.SemiprimeD1StackPacketInventoryOriginal
import RiemannGaussian.SemiprimeD1StackPacketInventoryStorage
/-! # One original-input source retains width and acquires the sparse inventory
Actual Root2211 executes ONCE. Two real preserving copies of its actual key
vector and original catalogue feed the actual Inventory59 source. No class,
packet, placement, frequency, width or old-index answer is an input.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPacketInventory
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace R
export SemiprimeD1StackRootRecoveryWidth (Stack Label program input initial originalInput copyScratch output stack_card)
end R
namespace I
export SemiprimeD1StackPacketInventory (Stack Label program input initial source catalogue packets output stack_card)
end I
namespace Source
export SemiprimeD1StackRootPacketInventorySources (keysRole catalogueRole)
end Source
/-- Both whole actual sources, including the retained width72 and every inventory shadow/global. -/
abbrev Stack:=R.Stack⊕I.Stack
/-- Compose the two actual computable bank equalities explicitly to avoid deep instance-search recursion. -/
instance :DecidableEq Stack:=by
  letI :DecidableEq R.Stack:=inferInstance
  letI :DecidableEq I.Stack:=inferInstance
  infer_instance
/-- All2211 original-input/selected/frequency/width roles remain allocated. -/
def rootStack:R.Stack→Stack:=Sum.inl
/-- All59 actual inventory roles remain allocated and separate from retained root frequency maps. -/
def inventoryStack:I.Stack→Stack:=Sum.inr
/-- Empty actual retained root scratch is reused and physically restored by both copies. -/
def copyScratch:Stack:=rootStack R.copyScratch
/-- Exactly two actual stopped-source handoffs, fixed before N. -/
inductive Copy where | keys | catalogue deriving DecidableEq,Repr
instance :Fintype Copy:=Fintype.ofList [.keys,.catalogue] (by intro k;cases k <;> simp)
/-- Read only actual retained producer words. -/
def copySource:Copy→Stack
  | .keys=>rootStack Source.keysRole
  | .catalogue=>rootStack Source.catalogueRole
/-- Populate ONLY the honest selected-key/catalogue front door of the real next source. -/
def copyTarget:Copy→Stack
  | .keys=>inventoryStack I.source
  | .catalogue=>inventoryStack I.catalogue
/-- Actual preserving-copy operands; no input-derived address or getter executes. -/
def copyStack (site:Copy) (k:Fin 3):Stack:=
  if k=0 then copySource site else if k=1 then copyTarget site else copyScratch
/-- Fixed whole-root/copy/inventory/halt controller. -/
inductive Control where | start | copy (site:Copy) | inventory | done deriving DecidableEq,Fintype
/-- Every real component and saved return label is fixed finite. -/
inductive Label where
  | local (pc:Control) | root (pc:R.Label) | inventory (pc:I.Label) | copy (site:Copy) (pc:Fin 9)
  deriving Fintype
local notation "ctl"=>Label.local
/-- Actual literal handoff order. -/
def copyNext:Copy→Label
  | .keys=>ctl (.copy .catalogue)
  | .catalogue=>ctl .inventory
/-- ONE actual source starts with binary N and acquires every sparse packet/placement after the shared root. -/
def program:Label→C.Instruction Stack Label
  | .local .start=>.call (.root (.local .start)) (ctl (.copy .keys))
  | .local (.copy site)=>.call (.copy site 0) (copyNext site)
  | .local .inventory=>.call (.inventory (.local .start)) (ctl .done)
  | .local .done=>.base .halt
  | .root pc=>SemiprimeD1StackValidationLink.instruction rootStack Label.root (R.program pc)
  | .inventory pc=>SemiprimeD1StackValidationLink.instruction inventoryStack Label.inventory (I.program pc)
  | .copy site pc=>SemiprimeD1StackMultiplierLink.instruction
      (copyStack site) (Label.copy site) (SemiprimeD1StackCopy.code pc)
/-- Entire actual bank; no older source/frequency/template word is reset or omitted. -/
def data (root:R.Stack→List Bool) (inventory:I.Stack→List Bool):Stack→List Bool:=Sum.elim root inventory
/-- Sole front-door initialized physical word is original binary N. -/
def input (bits:List Bool):Stack→List Bool:=data (R.input bits) (fun _=>[])
/-- Inventory maps/classes and all other new private roles begin genuinely empty. -/
def initial (bits:List Bool):C.State Stack Label:=⟨some (ctl .start),none,none,input bits,[]⟩
/-- Actual original binary input address. -/
def originalInput:Stack:=rootStack R.originalInput
/-- Actual chronological six-field placement vector. -/
def output:Stack:=inventoryStack I.output
/-- Actual newest-first discovered packet vector, retained for the real mode source. -/
def packets:Stack:=inventoryStack I.packets
/-- Actual already acquired authoritative false width template remains available. -/
def template:Stack:=rootStack R.output
/-- One fixed finite original-input source with all2270 words present. -/
def machine:Turing.FinTM2:=SemiprimeD1StackCalls.machine originalInput output (ctl .start) program
/-- All2270 source/cache/frequency/width/inventory/shadow allocations are counted. -/
theorem stack_card:Fintype.card Stack=2270:=by rw [Fintype.card_sum,R.stack_card,I.stack_card]
/-- Every actual source/target/restoring scratch triple is physically distinct. -/
theorem copy_injective (site:Copy):Function.Injective (copyStack site):=by cases site <;> decide
/-- Runtime sigma contains no N, natural counter, list, evaluator or supplied result. -/
theorem control_finite:Finite machine.σ:=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- All actual Boolean and real return alphabets are finite before every original input. -/
theorem alphabets_finite:∀k,Finite (machine.Γ k):=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackRootPacketInventory
