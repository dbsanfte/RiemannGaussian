/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootSelectionAcquireOriginal
import RiemannGaussian.SemiprimeD1StackSourcePacketPaddingOriginal
import RiemannGaussian.SemiprimeD1StackSourcePacketPaddingBounds
/-! # Original binary N to actual packet-padding acquisition
One real original-input selection source produces the actual key vector and
unary dimension. Two paid preserving copies feed the real padding source.
Its actual frequency acquisition and rounding execute, and every2139 word
remains counted. No maximum, frequency map, exponent or padding is supplied.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPacketPadding
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace R
export SemiprimeD1StackRootSelectionAcquire
  (Stack Label program input initial originalInput output copyScratch parameterStack stack_card)
end R
namespace Q
export SemiprimeD1StackSourcePacketPadding (Stack Label program initial frequencyStack aux stack_card)
end Q
/-- Both complete actual sources, with no additional scratch allocation or omitted shadow. -/
abbrev Stack :=R.Stack⊕Q.Stack
/-- Every original-input producer/selection/cache role remains physically retained. -/
def rootStack :R.Stack→Stack :=Sum.inl
/-- Every actual frequency/rounding/input/work/output role remains allocated. -/
def paddingStack :Q.Stack→Stack :=Sum.inr
/-- The actual original selection source's already allocated empty restoring scratch is reused. -/
def copyScratch :Stack :=rootStack R.copyScratch
/-- Two actual source-result handoffs, fixed before every original N. -/
inductive Copy where | keys | dimension deriving DecidableEq,Repr
instance :Fintype Copy :=Fintype.ofList [.keys,.dimension] (by intro k;cases k <;> simp)
/-- Read only the actual stopped source's key-vector/dimension fields. -/
def copySource :Copy→Stack
  | .keys=>rootStack R.output
  | .dimension=>rootStack (R.parameterStack SemiprimeD1StackRootParameters.exponent)
/-- Populate only the actual two inputs of the next real source. -/
def copyTarget :Copy→Stack
  | .keys=>paddingStack (Q.frequencyStack (SemiprimeD1StackSourceKeyFrequency.aux .source))
  | .dimension=>paddingStack (Q.aux .exponent)
/-- A real preserving-copy map, with distinct input, output and restoring scratch. -/
def copyStack (part:Copy) (k:Fin 3) :Stack :=
  if k=0 then copySource part else if k=1 then copyTarget part else copyScratch
/-- Fixed finite original-source/handoff/padding/halt control. -/
inductive Control where | start | copy (part:Copy) | padding | done deriving DecidableEq,Fintype
/-- Every actual source and copy return label is fixed finite. -/
inductive Label where
  | local (pc:Control) | root (pc:R.Label) | padding (pc:Q.Label) | copy (part:Copy) (pc:Fin 9)
  deriving Fintype
local notation "ctl" => Label.local
/-- Actual continuation after each of the two paid copies. -/
def copyNext :Copy→Label
  | .keys=>ctl (.copy .dimension)
  | .dimension=>ctl .padding
/-- One genuine source acquires the exact rounded packet maximum from binary N alone. -/
def program :Label→C.Instruction Stack Label
  | .local .start=>.call (.root (.local (.copy .number))) (ctl (.copy .keys))
  | .local (.copy part)=>.call (.copy part 0) (copyNext part)
  | .local .padding=>.call (.padding .start) (ctl .done)
  | .local .done=>.base .halt
  | .root pc=>SemiprimeD1StackValidationLink.instruction rootStack Label.root (R.program pc)
  | .padding pc=>SemiprimeD1StackValidationLink.instruction paddingStack Label.padding (Q.program pc)
  | .copy part pc=>SemiprimeD1StackMultiplierLink.instruction
      (copyStack part) (Label.copy part) (SemiprimeD1StackCopy.code pc)
/-- Complete source/cache/frequency/output boundary, without resetting any retained word. -/
def data (root:R.Stack→List Bool) (padding:Q.Stack→List Bool) :Stack→List Bool :=Sum.elim root padding
/-- Sole actual front-door operand is original binary N. -/
def input (bits:List Bool) :Stack→List Bool :=data (R.input bits) (fun _=>[])
/-- No row, count, dimension, maximum or frequency state is prepared at the source entry. -/
def initial (bits:List Bool) :C.State Stack Label :=⟨some (ctl .start),none,none,input bits,[]⟩
/-- Genuine sole original-input address. -/
def originalInput :Stack :=rootStack R.originalInput
/-- Actual compact binary packet-padding output address. -/
def output :Stack :=paddingStack (Q.aux .padding)
/-- Fixed finite2139-role original-input machine. -/
def machine :Turing.FinTM2 :=SemiprimeD1StackCalls.machine originalInput output (ctl .start) program
/-- All2139 actual retained/source/frequency/cache/shadow words are counted. -/
theorem stack_card :Fintype.card Stack=2139 :=by rw [Fintype.card_sum,R.stack_card,Q.stack_card]
/-- Both actual copies preserve distinct source, destination and restoration words. -/
theorem copy_injective (part:Copy) :Function.Injective (copyStack part) :=by cases part <;> decide
/-- Runtime sigma contains only fixed finite flags and labels. -/
theorem control_finite :Finite machine.σ :=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- Every actual Boolean/return alphabet is fixed finite before all original N. -/
theorem alphabets_finite :∀k,Finite (machine.Γ k) :=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackRootPacketPadding
