/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetUnitBounds
import RiemannGaussian.SemiprimeD1StackFrame
/-! # A literal32-word inactive child-vertex source from original context headers
The context supplier acquires rank and precision markers from the two actual
headers. The literal unit source uses those SAME physical words. One actual
frame and fixed empty-scope/vertex/EOF bits form the whole native record.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildUnitVertex
namespace J
export SemiprimeD1StackJetContext (Stack Label program initial widthCache rankCache axesCache)
end J
namespace U
export SemiprimeD1StackJetUnit (Stack Label program widthCache rankCache output)
end U
namespace C
export SemiprimeD1StackCalls (State Instruction)
end C
/-- Only the record output and shared restoring-frame scratch are new. -/
inductive Aux where | record | scratch deriving DecidableEq,Repr
instance auxFintype : Fintype Aux := Fintype.ofList [.record,.scratch] (by intro k;cases k <;> simp)
/-- Both whole15-word banks and their displaced cache shadows are counted. -/
abbrev Stack := J.Stack⊕(U.Stack⊕Aux)
/-- Whole original-context source inclusion. -/
def context (k : J.Stack) : Stack := .inl k
/-- Dedicated unit work, including two empty displaced cache shadows. -/
def unitWork (k : U.Stack) : Stack := .inr (.inl k)
/-- Fixed actual output/frame-work address. -/
def aux (k : Aux) : Stack := .inr (.inr k)
/-- The unit source reads rank and precision DIRECTLY where context acquisition wrote them. -/
def unit (k : U.Stack) : Stack :=
  if k=U.widthCache then context J.widthCache else if k=U.rankCache then context J.rankCache else unitWork k
/-- One real preserving table-field frame; empty scope is a fixed three-bit literal frame. -/
def frameStack (k : Fin 3) : Stack := if k=0 then unit U.output else if k=1 then aux .record else aux .scratch
/-- Fixed literal source phases; no dimension or coefficient occurs in control. -/
inductive Control where
  | start | unit | leaf | eof | frame | scope0 | scope1 | scopeTag | vertexTag | done
  deriving DecidableEq
instance controlFintype : Fintype Control := Fintype.ofList
  [.start,.unit,.leaf,.eof,.frame,.scope0,.scope1,.scopeTag,.vertexTag,.done] (by intro k;cases k <;> simp)
/-- Context/unit/frame inclusions preserve their genuine nested labels. -/
inductive Label where
  | local (pc : Control) | context (pc : J.Label) | unit (pc : U.Label) | frame (pc : Fin 11)
  deriving Fintype
/-- Only literal calls, stack operations and fixed framing bits execute. -/
def program : Label→C.Instruction Stack Label
  | .local .start=>.call (.context .start) (.local .unit)
  | .local .unit=>.call (.unit .seed0) (.local .leaf)
  | .local .leaf=>.base (.push (unit U.output) false (.local .eof))
  | .local .eof=>.base (.push (aux .record) false (.local .frame))
  | .local .frame=>.call (.frame 0) (.local .scope0)
  | .local .scope0=>.base (.push (aux .record) false (.local .scope1))
  | .local .scope1=>.base (.push (aux .record) false (.local .scopeTag))
  | .local .scopeTag=>.base (.push (aux .record) true (.local .vertexTag))
  | .local .vertexTag=>.base (.push (aux .record) true (.local .done))
  | .local .done=>.base .halt
  | .context pc=>SemiprimeD1StackValidationLink.instruction context Label.context (J.program pc)
  | .unit pc=>SemiprimeD1StackValidationLink.instruction unit Label.unit (U.program pc)
  | .frame pc=>SemiprimeD1StackMultiplierLink.instruction frameStack Label.frame (SemiprimeD1StackFrame.code pc)
/-- Full physical bank; both displaced cache shadows remain explicit and empty. -/
def bank (j : J.Stack→List Bool) (u : U.Stack→List Bool) (record scratch : List Bool) : Stack→List Bool :=
  Sum.elim j (Sum.elim (fun k=>if k=U.widthCache ∨ k=U.rankCache then [] else u k)
    (fun k=>match k with | .record=>record | .scratch=>scratch))
/-- Only the actual axis-vector and binary-precision words are present. -/
def initial (axes precision : List Bool) : C.State Stack Label :=
  ⟨some (.local .start),none,none,bank (J.initial axes precision).data (fun _=>[]) [] [],[]⟩
/-- Actual fixed finite32-role header-to-unit-record machine. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine (context J.axesCache) (aux .record) (.local .start) program
/-- No source register alias within context acquisition. -/
theorem context_injective : Function.Injective context := Sum.inl_injective
/-- Actual shared rank/precision locations preserve distinct unit roles. -/
theorem unit_injective : Function.Injective unit := by decide
/-- The real framing source/output/scratch are separate physical words. -/
theorem frame_injective : Function.Injective frameStack := by decide
/-- Complete allocation includes all source banks, displaced shadows and framing work. -/
theorem stack_card : Fintype.card Stack=32 := by decide
/-- Data-valued dimensions stay on tapes; only literal labels and flags inhabit control. -/
theorem control_finite : Finite machine.σ := SemiprimeD1StackCalls.control_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackChildUnitVertex
