/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsOriginalResources
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsOriginalResources
/-! # Literal141-role original-phase to complete original weight-array source
Five physical words feed whole Grid/affine/inverse/powers acquisition. Six
actually acquired fields alias the real weight source; all clean helpers are
reused. Only ONE additional output word is allocated. No value/clock advice.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryNode
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace N
export SemiprimeD1StackRecoveryNodeInputs (Stack Label program input initial ctl affine inverse inverseReg inverseWork
  inverseOutput powersOutput scalarSigned scalarDen qWord widthWord)
end N
namespace I
export SemiprimeD1StackNormalizedInverse (Stack Reg Aux reg aux)
end I
namespace W
export SemiprimeD1StackRecoveryWeights (Stack Label program input initial aux scalar)
end W
/-- ALL old140 words and allocated shadows plus one actual output. -/
abbrev Stack:=N.Stack⊕Unit
/-- Complete literal old140 physical inclusion. -/
def node:N.Stack→Stack:=Sum.inl
/-- The only additional physical word, initially EMPTY. -/
def output:Stack:=Sum.inr ()
/-- Actual58 helper inclusion, with only source and output words redirected. -/
def weightHelper:I.Stack→Stack
  | .inl r=>node (N.inverse (.inl r))
  | .inr (.inl cache)=>node (N.inverseReg cache)
  | .inr (.inr slot)=>match slot with
    | .denominator=>node N.inverseOutput
    | .prefixReverse=>node N.powersOutput
    | .originalQ=>node N.qWord
    | .output=>output
    | slot=>node (N.inverse (I.aux slot))
/-- Complete real60-role weight call shares six actual operands and clean helpers. -/
def weight:W.Stack→Stack
  | .inl role=>weightHelper role
  | .inr .signed=>node N.scalarSigned
  | .inr .den=>node N.scalarDen
/-- Static caller stages, independent of all words, dimensions and clocks. -/
inductive Control where | start | readyGrid | weights | done deriving DecidableEq,Repr
/-- Literal complete finite stage inventory. -/
instance controlFintype:Fintype Control:=Fintype.ofList [.start,.readyGrid,.weights,.done] (by intro pc;cases pc <;> simp)
/-- Runtime control carries only fixed finite labels. -/
abbrev Label:=Control⊕(N.Label⊕W.Label)
/-- Literal caller label. -/
def ctl:Control→Label:=Sum.inl
/-- Exact old Node140 source-label inclusion. -/
def nodeLabel (pc:N.Label):Label:=.inr (.inl pc)
/-- Exact complete weight-source label inclusion. -/
def weightLabel (pc:W.Label):Label:=.inr (.inr pc)
/-- One parameterless source: actual Node140, actual whole weights, true halt. -/
def program:Label→C.Instruction Stack Label
  | .inl .start=>.call (nodeLabel (N.ctl .start)) (ctl .weights)
  | .inl .readyGrid=>.call (nodeLabel (N.ctl .readyGrid)) (ctl .weights)
  | .inl .weights=>.call (weightLabel (.local .start)) (ctl .done)
  | .inl .done=>.base .halt
  | .inr (.inl pc)=>SemiprimeD1StackValidationLink.instruction node nodeLabel (N.program pc)
  | .inr (.inr pc)=>SemiprimeD1StackValidationLink.instruction weight weightLabel (W.program pc)
/-- Fixed physical bank view, not an executable value function in runtime control. -/
def bank (old:N.Stack→List Bool) (out:List Bool):Stack→List Bool:=Sum.elim old (fun _=>out)
/-- ONLY original unary a/M/u, BINARY t and physical W initially occur. -/
def input (a M u t width:List Bool):Stack→List Bool:=bank (N.input a M u t width) []
/-- Whole entry precedes ALL Grid/affine/inverse/power/weight acquisition. -/
def initial (a M u t width:List Bool):C.State Stack Label:=⟨some (ctl .start),none,none,input a M u t width,[]⟩
/-- Honest prepared original-phase machine; the N-only outercaller is separate. -/
def machine:Turing.FinTM2:=SemiprimeD1StackCalls.machine
  (node (N.affine (SemiprimeD1StackRecoveryAffine.oldAux .originalA))) output (ctl .start) program
/-- Every actual data word and old allocated shadow is counted. -/
theorem stack_card:Fintype.card Stack=141:=by
  rw [Fintype.card_sum,SemiprimeD1StackRecoveryNodeInputs.stack_card,Fintype.card_unique]
/-- Finite actual control precedes every phase and physical template. -/
theorem control_finite:Finite machine.σ:=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- All141 Boolean and actual none-label return alphabets are finite. -/
theorem alphabets_finite:∀role,Finite (machine.Γ role):=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackRecoveryNode
