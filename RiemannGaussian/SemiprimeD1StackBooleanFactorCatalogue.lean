/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFactorScopeFibre
import RiemannGaussian.SemiprimeD1StackBooleanDescriptorRecordReject
import RiemannGaussian.SemiprimeD1StackVertexCatalogueBounds
/-! # Fixed original-N Boolean factor-record acquisition controller
The retained factor/scope catalogue is acquired once. Each original descriptor
is physically parsed; the actual factor counter drives the numeric scope filter.
Boolean descriptors log real rows, arithmetic descriptors take the real empty
branch. Every cached field and retained scope is physically drained before reuse.
The complete execution and original-order clock proofs belong to following modules.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackBooleanFactorCatalogue
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace F
export SemiprimeD1StackFactorScopeFibre (Stack Label program initial originalInput query output)
end F
namespace V
export SemiprimeD1StackVertexCatalogue (Stack Label program originalInput kernelStack)
end V
namespace D
export SemiprimeD1StackBooleanDescriptorRecord (Stack Label program cache aux)
end D
namespace Log
export SemiprimeD1StackVertexRecordStream (Stack Label code)
end Log
/-- All218 physical roles, including both unused direct-alias shadow registers. -/
abbrev Stack := F.Stack ⊕ (V.Stack ⊕ (D.Stack ⊕ Unit))
/-- The complete137-role actual source/filter inventory. -/
def sourceStack : F.Stack→Stack := Sum.inl
/-- The complete53-role actual original descriptor catalogue inventory. -/
def catalogueStack (k : V.Stack) : Stack := .inr (.inl k)
/-- Each descriptor's real reader IS the acquired catalogue's output tape. -/
def descriptorReader : Stack := catalogueStack (V.kernelStack (SemiprimeD1StackCartesian4.aux 2))
/-- The actual ordered binary scope produced by the real numeric filter. -/
def scope : Stack := sourceStack F.output
/-- All descriptor work is private except the two physically shared acquired operands. -/
def descriptorStack (k : D.Stack) : Stack :=
  if k=D.aux .reader then descriptorReader
  else if k=Sum.inl SemiprimeD1StackBooleanRecord.original then scope
  else .inr (.inr (.inl k))
/-- The logger shares only its real consuming operands and row accumulators. -/
def loggerStack (k : Log.Stack) : Stack :=
  descriptorStack (.inl (SemiprimeD1StackBooleanRecord.recordStack k))
/-- Original binary N is loaded only here before any acquisition. -/
def originalInput : Stack := sourceStack F.originalInput
/-- The final actual chronological factor-record tape. -/
def output : Stack := loggerStack .output
/-- Shared real reverse row history; no host concatenation constructs a record. -/
def history : Stack := loggerStack .history
/-- The actual factor key starts empty and gains one unary marker per descriptor. -/
def counter : Stack := sourceStack F.query
/-- One private scratch for preserving original binary N into the catalogue source. -/
def scratch : Stack := .inr (.inr (.inr ()))
/-- The original N copy has actual static source, destination and scratch roles. -/
def copyStack (k : Fin 3) : Stack :=
  if k=0 then originalInput else if k=1 then catalogueStack V.originalInput else scratch
/-- Literal EOF, row, cleanup, unary-counter and final-reversal controls. -/
inductive Control where
  | main | copyN | catalogue | seed | loop | row | clearField (part : Fin 5)
  | clearScope | advance | next | query | reverse | done
  deriving DecidableEq, Fintype
/-- Included literal programs and all return tags are fixed before every input. -/
inductive Label where
  | local (pc : Control) | source (pc : F.Label) | catalogue (pc : V.Label)
  | descriptor (pc : D.Label) | copy (pc : Fin 9) | logger (pc : Log.Label)
  deriving Fintype
/-- Each actual field payload is fully drained, including its EOF read. -/
def nextClear (part : Fin 5) : Label :=
  if h:part.val<4 then .local (.clearField ⟨part.val+1,by omega⟩) else .local .clearScope
/-- One literal source/descriptor/filter/record controller. No typed vertex,
factor number, scope list, table, mode function or row evaluator enters control. -/
def program : Label→C.Instruction Stack Label
  | .local .main=>.call (.source .main) (.local .copyN)
  | .local .copyN=>.call (.copy 0) (.local .catalogue)
  | .local .catalogue=>.call (.catalogue (.inl .main)) (.local .seed)
  | .local .seed=>.base (.push output false (.local .loop))
  | .local .loop=>.base (.peek descriptorReader (.local .reverse) (.local .row) (.local .row))
  | .local .row=>.call (.descriptor (.local (.field 0))) (.local (.clearField 0))
  | .local (.clearField part)=>.base (.pop (descriptorStack (D.cache part)) (nextClear part)
      (.local (.clearField part)) (.local (.clearField part)))
  | .local .clearScope=>.base (.pop scope (.local .advance) (.local .clearScope) (.local .clearScope))
  | .local .advance=>.base (.push counter true (.local .next))
  | .local .next=>.base (.peek descriptorReader (.local .reverse) (.local .query) (.local .query))
  | .local .query=>.call (.source .copy) (.local .loop)
  | .local .reverse=>.call (.logger .reverse) (.local .done)
  | .local .done=>.base .halt
  | .source pc=>SemiprimeD1StackValidationLink.instruction sourceStack Label.source (F.program pc)
  | .catalogue pc=>SemiprimeD1StackValidationLink.instruction catalogueStack Label.catalogue (V.program pc)
  | .descriptor pc=>SemiprimeD1StackValidationLink.instruction descriptorStack Label.descriptor (D.program pc)
  | .copy pc=>SemiprimeD1StackMultiplierLink.instruction copyStack Label.copy (SemiprimeD1StackCopy.code pc)
  | .logger pc=>SemiprimeD1StackMultiplierLink.instruction loggerStack Label.logger (Log.code pc)
/-- Binary N is the only nonempty physical input, with factor key initially empty. -/
def input (bits : List Bool) : Stack→List Bool :=
  Sum.elim (F.initial bits []).data (fun _=>[])
/-- Actual original-N entry; the terminator and every cache are acquired by program steps. -/
def initial (bits : List Bool) : C.State Stack Label :=
  ⟨some (.local .main),none,none,input bits,[]⟩
/-- One fixed finite-alphabet machine; the complete run proof remains a following join. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine originalInput output (.local .main) program
/-- All original source caches, aliases and actual scratch are counted. -/
theorem stack_card : Fintype.card Stack=218 := by decide
/-- Directly shared reader and scope operands preserve descriptor-program injectivity. -/
theorem descriptor_injective : Function.Injective descriptorStack := by decide
/-- All actual logger operands are distinct despite sharing the two acquired fields. -/
theorem logger_injective : Function.Injective loggerStack := by decide
/-- The binary original-input copy has disjoint physical operands. -/
theorem copy_injective : Function.Injective copyStack := by decide
/-- The runtime has only finite Boolean/label flags and a real label-return stack. -/
theorem control_finite : Finite machine.σ :=
  SemiprimeD1StackCalls.control_finite originalInput output (.local .main) program
/-- Every actual data and return alphabet is finite before all original N. -/
theorem all_alphabets_finite (k : machine.K) : Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite originalInput output (.local .main) program k
end RiemannGaussian.SemiprimeD1StackBooleanFactorCatalogue
