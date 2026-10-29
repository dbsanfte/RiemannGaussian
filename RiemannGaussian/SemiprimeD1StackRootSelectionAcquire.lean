/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootNetworkRowsOriginal
import RiemannGaussian.SemiprimeD1StackRootParametersOriginal
import RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireOriginal
/-! # Binary N alone to the original complete selected-key vector
The real row source, real root-parameter source and real whole selection
source execute once each. Four preserving copies connect their physical
words. The shared copy scratch is an allocated selection-source word; all
2114 roles remain counted. No row, graph, count, dimension, selected prefix,
dictionary, score or answer is a physical input.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootSelectionAcquire
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace R
export SemiprimeD1StackRootNetworkRows (Stack Label program input initial originalInput output stack_card)
export SemiprimeD1StackRootNetworkRowsOriginal (leftCount)
end R
namespace P
export SemiprimeD1StackRootParameters (Stack Label program initial originalInput exponent stack_card)
end P
namespace Q
export SemiprimeD1StackSourceSelectionAcquire
  (Stack Label program initial occurrenceStack alphabetStack keyStack copyScratch stack_card)
end Q
/-- Every actual retained row/parameter/selection source role is allocated. -/
abbrev Stack :=R.Stack⊕(P.Stack⊕Q.Stack)
/-- Complete real original-N row/record/index bank. -/
def rootStack :R.Stack→Stack :=Sum.inl
/-- Complete real original-N scheduling bank. -/
def parameterStack (k:P.Stack) :Stack :=.inr (.inl k)
/-- Complete real row-to-selected-key acquisition bank. -/
def acquisitionStack (k:Q.Stack) :Stack :=.inr (.inr k)
/-- The actual already allocated selection copy scratch is reused before its source call. -/
def copyScratch :Stack :=acquisitionStack Q.copyScratch
/-- Four fixed physical input handoffs; no input-derived address occurs. -/
inductive Copy where | number | rows | owners | dimension deriving DecidableEq,Repr
instance :Fintype Copy :=Fintype.ofList [.number,.rows,.owners,.dimension] (by intro k;cases k <;> simp)
/-- Every handoff reads an actual input or actual stopped producer word. -/
def copySource :Copy→Stack
  | .number=>rootStack R.originalInput
  | .rows=>rootStack R.output
  | .owners=>rootStack R.leftCount
  | .dimension=>parameterStack P.exponent
/-- Only the next real source's literal physical inputs are populated. -/
def copyTarget :Copy→Stack
  | .number=>parameterStack P.originalInput
  | .rows=>acquisitionStack (Q.occurrenceStack .rows)
  | .owners=>acquisitionStack (Q.occurrenceStack .number)
  | .dimension=>acquisitionStack (Q.alphabetStack (SemiprimeD1StackSourceAlphabet64.aux .source))
/-- Real preserving copies use three distinct physical words. -/
def copyStack (site:Copy) (k:Fin 3) :Stack :=
  if k=0 then copySource site else if k=1 then copyTarget site else copyScratch
/-- Fixed finite whole-source control, independent of N and every derived value. -/
inductive Control where | copy (site:Copy) | parameters | root | acquire | done
  deriving DecidableEq,Fintype
/-- Actual component and copy return labels are finite before the whole input family. -/
inductive Label where
  | local (pc:Control) | root (pc:R.Label) | parameters (pc:P.Label)
  | acquire (pc:Q.Label) | copy (site:Copy) (pc:Fin 9)
  deriving Fintype
local notation "ctl" => Label.local
/-- Exact real continuation of every paid preserving copy. -/
def copyNext :Copy→Label
  | .number=>ctl .parameters
  | .rows=>ctl (.copy .owners)
  | .owners=>ctl (.copy .dimension)
  | .dimension=>ctl .acquire
/-- One finite program acquires rows/counts/dimension and every original selected key from N alone. -/
def program :Label→C.Instruction Stack Label
  | .local (.copy site)=>.call (.copy site 0) (copyNext site)
  | .local .parameters=>.call (.parameters (.inl .start)) (ctl .root)
  | .local .root=>.call (.root (.inl .start)) (ctl (.copy .rows))
  | .local .acquire=>.call (.acquire (.local .start)) (ctl .done)
  | .local .done=>.base .halt
  | .root pc=>SemiprimeD1StackValidationLink.instruction rootStack Label.root (R.program pc)
  | .parameters pc=>SemiprimeD1StackValidationLink.instruction parameterStack Label.parameters (P.program pc)
  | .acquire pc=>SemiprimeD1StackValidationLink.instruction acquisitionStack Label.acquire (Q.program pc)
  | .copy site pc=>SemiprimeD1StackMultiplierLink.instruction
      (copyStack site) (Label.copy site) (SemiprimeD1StackCopy.code pc)
/-- All2114 actual source/cache/output/shadow words are included in the physical boundary. -/
def data (root:R.Stack→List Bool) (parameters:P.Stack→List Bool) (acquisition:Q.Stack→List Bool) :Stack→List Bool :=
  Sum.elim root (Sum.elim parameters acquisition)
/-- Sole actual input is binary N; every derived bank starts genuinely empty. -/
def input (bits:List Bool) :Stack→List Bool :=data (R.input bits) (fun _=>[]) (fun _=>[])
/-- The whole N-only source starts by really copying N before either producer executes. -/
def initial (bits:List Bool) :C.State Stack Label :=
  ⟨some (ctl (.copy .number)),none,none,input bits,[]⟩
/-- Actual sole input address is inherited from the original row source. -/
def originalInput :Stack :=rootStack R.originalInput
/-- Actual compact selected-key vector remains in the executed acquisition bank. -/
def output :Stack :=acquisitionStack (Q.keyStack (SemiprimeD1StackSourceSelectedKeys.aux .output))
/-- One genuine fixed finite original-binary-input machine. -/
def machine :Turing.FinTM2 :=SemiprimeD1StackCalls.machine originalInput output (ctl (.copy .number)) program
/-- All actual preserving-copy operands remain distinct, including the reused scratch. -/
theorem copy_injective (site:Copy) :Function.Injective (copyStack site) :=by cases site <;> decide
/-- All2114 physical data roles, including every unused shadow, remain counted. -/
theorem stack_card :Fintype.card Stack=2114 :=by
  rw [Fintype.card_sum,R.stack_card,Fintype.card_sum,P.stack_card,Q.stack_card]
/-- No graph, count, evaluator, continuation or natural value inhabits runtime control. -/
theorem control_finite :Finite machine.σ :=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- Data and actual return alphabets are fixed finite before all original N. -/
theorem alphabets_finite :∀k,Finite (machine.Γ k) :=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackRootSelectionAcquire
