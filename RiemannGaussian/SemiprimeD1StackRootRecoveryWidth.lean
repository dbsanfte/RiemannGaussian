/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPacketPaddingOriginal
import RiemannGaussian.SemiprimeD1StackRecoveryWidthOriginal
/-! # Original binary N to the actual recovery-width template
One actual whole root source acquires the real exponent and incidence count.
Two paid preserving copies feed the real width source. All2211 actual words
remain allocated, including the original selected keys/frequency/padding banks.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootRecoveryWidth
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace R
export SemiprimeD1StackRootPacketPadding (Stack Label program input initial originalInput copyScratch stack_card)
end R
namespace W
export SemiprimeD1StackRecoveryWidth (Stack Label program initial input aux stack_card)
end W
namespace O
export SemiprimeD1StackRecoveryWidthOriginal (exponentRole edgesRole originalA originalM)
end O
/-- Both complete actual sources; no newly allocated scratch or omitted cache word. -/
abbrev Stack:=R.Stack⊕W.Stack
/-- Complete original-input root/selection/frequency/padding bank. -/
def rootStack:R.Stack→Stack:=Sum.inl
/-- Complete real width-acquisition bank, including all64 physical arithmetic registers. -/
def widthStack:W.Stack→Stack:=Sum.inr
/-- The actual stopped root's already allocated empty restoring scratch is reused. -/
def copyScratch:Stack:=rootStack R.copyScratch
/-- Exactly two actual retained metadata handoffs. -/
inductive Copy where | exponent | edges deriving DecidableEq,Repr
instance :Fintype Copy:=Fintype.ofList [.exponent,.edges] (by intro k;cases k <;> simp)
/-- Every source address is the real retained metadata field of Root2139. -/
def copySource:Copy→Stack
  | .exponent=>rootStack O.exponentRole
  | .edges=>rootStack O.edgesRole
/-- Only the two honest width-source input words are written. -/
def copyTarget:Copy→Stack
  | .exponent=>widthStack (W.aux .a)
  | .edges=>widthStack (W.aux .m)
/-- Physical preserving-copy operands are finite and independent of all original inputs. -/
def copyStack (part:Copy) (k:Fin 3):Stack:=
  if k=0 then copySource part else if k=1 then copyTarget part else copyScratch
/-- Fixed original-source, two-copy, width-source and halt controller. -/
inductive Control where | start | copy (part:Copy) | width | done deriving DecidableEq,Fintype
/-- Actual included-source labels and finite real return symbols. -/
inductive Label where
  | local (pc:Control) | root (pc:R.Label) | width (pc:W.Label) | copy (part:Copy) (pc:Fin 9)
  deriving Fintype
local notation "ctl"=>Label.local
/-- Fixed physical successor after each actual metadata copy. -/
def copyNext:Copy→Label
  | .exponent=>ctl (.copy .edges)
  | .edges=>ctl .width
/-- Sole actual source program, with no parameter/template evaluator in runtime control. -/
def program:Label→C.Instruction Stack Label
  | .local .start=>.call (.root (.local .start)) (ctl (.copy .exponent))
  | .local (.copy part)=>.call (.copy part 0) (copyNext part)
  | .local .width=>.call (.width .start) (ctl .done)
  | .local .done=>.base .halt
  | .root pc=>SemiprimeD1StackValidationLink.instruction rootStack Label.root (R.program pc)
  | .width pc=>SemiprimeD1StackValidationLink.instruction widthStack Label.width (W.program pc)
  | .copy part pc=>SemiprimeD1StackMultiplierLink.instruction
      (copyStack part) (Label.copy part) (SemiprimeD1StackCopy.code pc)
/-- Both complete real banks, retaining every allocated role. -/
def data (root:R.Stack→List Bool) (width:W.Stack→List Bool):Stack→List Bool:=Sum.elim root width
/-- Original binary N is the sole initialized actual word. -/
def input (bits:List Bool):Stack→List Bool:=data (R.input bits) (fun _=>[])
/-- No exponent/incidence/grid/width/template advice at the actual front door. -/
def initial (bits:List Bool):C.State Stack Label:=⟨some (ctl .start),none,none,input bits,[]⟩
/-- Actual sole original-input address. -/
def originalInput:Stack:=rootStack R.originalInput
/-- Exact physical false-template output address. -/
def output:Stack:=widthStack (W.aux .output)
/-- One fixed finite original-input width-source machine. -/
def machine:Turing.FinTM2:=SemiprimeD1StackCalls.machine originalInput output (ctl .start) program
/-- All2211 original/cache/shadow/gate/scratch words remain counted. -/
theorem stack_card:Fintype.card Stack=2211:=by rw [Fintype.card_sum,R.stack_card,W.stack_card]
/-- Each actual preserving copy has three distinct physical operands. -/
theorem copy_injective (part:Copy):Function.Injective (copyStack part):=by cases part <;> decide
/-- All transient flags and labels are finite before the original binary input. -/
theorem control_finite:Finite machine.σ:=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- Both Boolean data and all actual return alphabets are fixed finite. -/
theorem alphabets_finite:∀k,Finite (machine.Γ k):=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackRootRecoveryWidth
