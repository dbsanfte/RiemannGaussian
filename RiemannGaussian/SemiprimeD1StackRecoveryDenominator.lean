/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMultiplierExecution
import RiemannGaussian.SemiprimeD1StackWordFitExecution
import RiemannGaussian.SemiprimeD1TensorTapeFieldBytecode
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
/-! # Literal streaming canonical-row common-denominator product
Only an actual five-field tagged row tape and an actual physical width template
are supplied. Four fields are parsed and drained before the actual denominator
is parsed into the FIRST operand of the real full multiplier. The growing raw
product is its SECOND operand. One final paid fit preserves the old public width;
an empty row tape returns the old literal one. Canonical-row acquisition is upstream.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryDenominator
namespace C
export SemiprimeD1StackCalls (Instruction State run)
end C
namespace M
export SemiprimeD1StackMultiplier (Stack Label code payload input factor copyScratch)
end M
namespace Fit
export SemiprimeD1StackWordFit (Stack Label program operand template counter scratch output)
end Fit
namespace Field
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end Field
/-- Five finite caller roles beside the complete allocated multiplier and fit banks. -/
inductive Aux where
  | rows | reader | discard | valid | output
  deriving DecidableEq,Repr
instance :Fintype Aux:=Fintype.ofList [.rows,.reader,.discard,.valid,.output]
  (by intro k;cases k <;> simp)
/-- All19 allocated roles include both unused fit-input/output shadows. -/
abbrev Stack:=M.Stack⊕(Fit.Stack⊕Aux)
/-- Actual included multiplier role. -/
def main:M.Stack → Stack:=Sum.inl
/-- Complete allocated five-role fit bank, including unused shadows. -/
def fitWork (k:Fit.Stack):Stack:=.inr (.inl k)
/-- Caller source, parser and result roles. -/
def aux (k:Aux):Stack:=.inr (.inr k)
/-- Full raw product accumulator in the actual multiplier. -/
def accumulator:Stack:=main (.inl .right)
/-- The genuinely supplied physical width template is retained. -/
def template:Stack:=fitWork Fit.template
/-- Final actual result word. -/
def output:Stack:=aux .output
/-- Shared actual restoring-copy/parser scratch is clean before every full product. -/
def scratch:Stack:=main M.copyScratch
/-- Final WordFit consumes the actual multiplier accumulator and writes the caller output. -/
def fitStack (k:Fit.Stack):Stack:=
  if k=Fit.operand then accumulator else if k=Fit.output then output else fitWork k
/-- Current denominator is always the FIRST actual multiplier operand. -/
def fieldTarget (part:Fin 5):Stack:=if part=4 then main M.input else aux .discard
/-- Literal real four-role parser inclusion, with no supplied parsed field. -/
def fieldStack (part:Fin 5):Field.Stack → Stack
  | .inl .input=>aux .reader | .inl .scratch=>scratch | .inl .output=>fieldTarget part | .inr () =>aux .valid
/-- Two fixed actual copy sites: retained input to reader, raw product to second operand. -/
def copyStack (rowCopy:Bool) (k:Fin 3):Stack:=
  if k=0 then if rowCopy then aux .rows else accumulator
  else if k=1 then if rowCopy then aux .reader else main M.factor else scratch
/-- Fixed finite caller labels; seen is one finite bit, never a row count. -/
inductive Control where
  | start | seed | loop (seen:Bool) | load | clearAccumulator
  | field (part:Fin 5) | valid (part:Fin 5) | clearField (part:Fin 5)
  | multiply | fit | emptyPop | emptyPush | done | abort
  deriving DecidableEq,Fintype,Repr
/-- Actual fixed finite labels include all real component returns. -/
inductive Label where
  | local (pc:Control) | multiply (pc:M.Label) | fit (pc:Fit.Label)
  | field (part:Fin 5) (pc:Field.Label) | copy (rowCopy:Bool) (pc:Fin 9)
  deriving DecidableEq,Fintype,Repr
local notation "ctl"=>Label.local
/-- Static successor after one of the first four discarded source fields. -/
def nextField (part:Fin 5):Label:=
  if h:part.val+1<5 then ctl (.field ⟨part.val+1,h⟩) else ctl .multiply
/-- Literal finite program: all parsing, copies, products, cleanup and fitting execute. -/
def program:Label → C.Instruction Stack Label
  | .local .start=>.call (.copy true 0) (ctl .seed)
  | .local .seed=>.base (.push accumulator true (ctl (.loop false)))
  | .local (.loop seen)=>.base (.pop (aux .reader) (ctl .abort)
      (if seen then ctl .fit else ctl .emptyPop) (ctl .load))
  | .local .load=>.call (.copy false 0) (ctl .clearAccumulator)
  | .local .clearAccumulator=>.base (.pop accumulator (ctl (.field 0)) (ctl .clearAccumulator) (ctl .clearAccumulator))
  | .local (.field part)=>.call (.field part (Field.active .tagPop (none,false))) (ctl (.valid part))
  | .local (.valid part)=>.base (.pop (aux .valid) (ctl .abort) (ctl .abort)
      (if part=4 then ctl .multiply else ctl (.clearField part)))
  | .local (.clearField part)=>.base (.pop (aux .discard) (nextField part)
      (ctl (.clearField part)) (ctl (.clearField part)))
  | .local .multiply=>.call (.multiply (.control .start)) (ctl (.loop true))
  | .local .fit=>.call (.fit .start) (ctl .done)
  | .local .emptyPop=>.base (.pop accumulator (ctl .abort) (ctl .abort) (ctl .emptyPush))
  | .local .emptyPush=>.base (.push output true (ctl .done))
  | .local .done|.local .abort=>.base .halt
  | .multiply pc=>SemiprimeD1StackValidationLink.instruction main Label.multiply (M.code pc)
  | .fit pc=>SemiprimeD1StackValidationLink.instruction fitStack Label.fit (Fit.program pc)
  | .field part pc=>SemiprimeD1StackMultiplierLink.instruction (fieldStack part) (Label.field part) (Field.code pc)
  | .copy rowCopy pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack rowCopy) (Label.copy rowCopy) (SemiprimeD1StackCopy.code pc)
/-- Exactly two actual input tapes; all counters, products and work words start empty. -/
def input (rows widthTemplate:List Bool):Stack → List Bool:=
  Function.update (Function.update (fun _=>[]) (aux .rows) rows) template widthTemplate
/-- Honest prepared two-word physical entry. -/
def initial (rows widthTemplate:List Bool):C.State Stack Label:=
  ⟨some (ctl .start),none,none,input rows widthTemplate,[]⟩
/-- One parameterless fixed finite machine; row/template acquisition is an explicit caller obligation. -/
def machine:Turing.FinTM2:=SemiprimeD1StackCalls.machine (aux .rows) output (ctl .start) program
/-- All19 roles, including both shadows, remain in the real machine. -/
theorem stack_card:Fintype.card Stack=19:=by decide
/-- Actual parser operands are distinct. -/
theorem field_injective (part:Fin 5):Function.Injective (fieldStack part):=by fin_cases part <;> decide
/-- Both real copies use three distinct roles. -/
theorem copy_injective (rowCopy:Bool):Function.Injective (copyStack rowCopy):=by cases rowCopy <;> decide
/-- Actual final fit operands are distinct despite its two counted unused shadows. -/
theorem fit_injective:Function.Injective fitStack:=by decide
/-- Every data and genuine return alphabet is finite before the inputs. -/
theorem all_alphabets_finite:∀k,Finite (machine.Γ k):=
  SemiprimeD1StackCalls.all_alphabets_finite (aux .rows) output (ctl .start) program
/-- Runtime transient control is fixed finite, without values, lists or evaluators. -/
theorem control_finite:Finite machine.σ:=
  SemiprimeD1StackCalls.control_finite (aux .rows) output (ctl .start) program
end RiemannGaussian.SemiprimeD1StackRecoveryDenominator
