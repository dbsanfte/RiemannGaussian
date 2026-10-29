/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexedExecution
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexedBounds
import RiemannGaussian.SemiprimeD1StackFrame
import RiemannGaussian.SemiprimeD1StackReverseWord
/-! # Actual column acquisition from retained phase-block bytes
Only a physical phase/block/word vector and a binary coordinate enter the
fixed21-role program. No coordinate cache, rank, precision or getter is supplied.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryCoordinate
namespace C
export SemiprimeD1StackCalls (Instruction State run)
end C
namespace I
export SemiprimeD1StackRecoveryEntriesIndexed (Stack Label Aux program aux initial input)
end I
namespace F
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end F
/-- Nine literal retained-bank/parser/two-level logger roles. -/
inductive Aux where
  | phases | reader | blocks | valid | rowHistory | rowOutput | history | buffer | output
  deriving DecidableEq,Repr
instance :Fintype Aux:=Fintype.ofList [.phases,.reader,.blocks,.valid,.rowHistory,.rowOutput,.history,.buffer,.output]
  (by intro k;cases k <;> simp)
/-- Full12-role binary reader and all9 allocated outer roles. -/
abbrev Stack:=I.Stack⊕Aux
/-- The actual binary indexed reader inclusion. -/
def indexed:I.Stack→Stack:=Sum.inl
/-- Actual phase source/parser/logger tape. -/
def aux:Aux→Stack:=Sum.inr
/-- Retained original raw binary coordinate; high-zero padding is allowed. -/
def coordinate:Stack:=indexed (I.aux .query)
/-- Current physically parsed block vector. -/
def block:Stack:=indexed (I.aux .cache)
/-- Actual selected/default coefficient word. -/
def selected:Stack:=indexed (I.aux .value)
/-- Shared real restoring-copy/parser/frame scratch, empty between all calls. -/
def scratch:Stack:=indexed (I.aux .copy)
/-- Actual resulting nested child-coordinate vector. -/
def output:Stack:=aux .output
/-- One preserving copy of the whole original phase bank. -/
def copyStack (k:Fin 3):Stack:=if k=0 then aux .phases else if k=1 then aux .reader else scratch
/-- Two physical parser inclusions: a phase payload, then each actual block. -/
def fieldStack (inner:Bool):F.Stack→Stack
  | .inl .input=>if inner then aux .blocks else aux .reader
  | .inl .scratch=>scratch
  | .inl .output=>if inner then block else aux .blocks
  | .inr () =>aux .valid
/-- Two real preserving frame sites; coefficients and completed phase rows. -/
def frameStack (phase:Bool) (k:Fin 3):Stack:=
  if k=0 then if phase then aux .rowOutput else selected
  else if k=1 then aux .buffer else scratch
/-- Four genuine reversals, with two separate accumulated histories. -/
def reverseStack (site:Fin 4) (k:Fin 2):Stack:=
  if k=0 then if site=0 ∨site=2 then aux .buffer else if site=1 then aux .rowHistory else aux .history
  else if site=0 then aux .rowHistory else if site=1 then aux .rowOutput else if site=2 then aux .history else output
/-- Literal finite nested-vector/lookup/logger control. -/
inductive Control where
  | start | sentinel | phaseLoop | phaseField | phaseValid | rowSeed | blockLoop | blockField | blockValid
  | lookup | coefficientFrame | coefficientTag | coefficientReverse | clearBlock | clearSelected
  | rowReverse | phaseFrame | phaseTag | phaseReverse | clearRow | finish | done | abort
  deriving DecidableEq,Repr
instance :Fintype Control:=Fintype.ofList [.start,.sentinel,.phaseLoop,.phaseField,.phaseValid,.rowSeed,.blockLoop,.blockField,.blockValid,
  .lookup,.coefficientFrame,.coefficientTag,.coefficientReverse,.clearBlock,.clearSelected,
  .rowReverse,.phaseFrame,.phaseTag,.phaseReverse,.clearRow,.finish,.done,.abort] (by intro k;cases k <;> simp)
/-- All component entry and saved-return labels are fixed before both tapes. -/
inductive Label where
  | local (pc:Control) | indexed (pc:I.Label) | copy (pc:Fin 9)
  | field (inner:Bool) (pc:F.Label) | frame (phase:Bool) (pc:Fin 11) | reverse (site:Fin 4) (pc:Fin 4)
  deriving DecidableEq,Fintype,Repr
local notation "ctl"=>Label.local
/-- The ONE parameterless physical coordinate source, including every call, drain and halt. -/
def program:Label→C.Instruction Stack Label
  | .local .start=>.call (.copy 0) (ctl .sentinel)
  | .local .sentinel=>.base (.push output false (ctl .phaseLoop))
  | .local .phaseLoop=>.base (.pop (aux .reader) (ctl .abort) (ctl .finish) (ctl .phaseField))
  | .local .phaseField=>.call (.field false (F.active .tagPop (none,false))) (ctl .phaseValid)
  | .local .phaseValid=>.base (.pop (aux .valid) (ctl .abort) (ctl .abort) (ctl .rowSeed))
  | .local .rowSeed=>.base (.push (aux .rowOutput) false (ctl .blockLoop))
  | .local .blockLoop=>.base (.pop (aux .blocks) (ctl .abort) (ctl .rowReverse) (ctl .blockField))
  | .local .blockField=>.call (.field true (F.active .tagPop (none,false))) (ctl .blockValid)
  | .local .blockValid=>.base (.pop (aux .valid) (ctl .abort) (ctl .abort) (ctl .lookup))
  | .local .lookup=>.call (.indexed (.local .start)) (ctl .coefficientFrame)
  | .local .coefficientFrame=>.call (.frame false 0) (ctl .coefficientTag)
  | .local .coefficientTag=>.base (.push (aux .buffer) true (ctl .coefficientReverse))
  | .local .coefficientReverse=>.call (.reverse 0 0) (ctl .clearBlock)
  | .local .clearBlock=>.base (.pop block (ctl .clearSelected) (ctl .clearBlock) (ctl .clearBlock))
  | .local .clearSelected=>.base (.pop selected (ctl .blockLoop) (ctl .clearSelected) (ctl .clearSelected))
  | .local .rowReverse=>.call (.reverse 1 0) (ctl .phaseFrame)
  | .local .phaseFrame=>.call (.frame true 0) (ctl .phaseTag)
  | .local .phaseTag=>.base (.push (aux .buffer) true (ctl .phaseReverse))
  | .local .phaseReverse=>.call (.reverse 2 0) (ctl .clearRow)
  | .local .clearRow=>.base (.pop (aux .rowOutput) (ctl .phaseLoop) (ctl .clearRow) (ctl .clearRow))
  | .local .finish=>.call (.reverse 3 0) (ctl .done)
  | .local .done|.local .abort=>.base .halt
  | .indexed pc=>SemiprimeD1StackValidationLink.instruction indexed Label.indexed (I.program pc)
  | .copy pc=>SemiprimeD1StackMultiplierLink.instruction copyStack Label.copy (SemiprimeD1StackCopy.code pc)
  | .field inner pc=>SemiprimeD1StackMultiplierLink.instruction (fieldStack inner) (Label.field inner) (F.code pc)
  | .frame phase pc=>SemiprimeD1StackMultiplierLink.instruction (frameStack phase) (Label.frame phase) (SemiprimeD1StackFrame.code pc)
  | .reverse site pc=>SemiprimeD1StackMultiplierLink.instruction (reverseStack site) (Label.reverse site) (SemiprimeD1StackReverseWord.code pc)
/-- Exactly the retained actual phase bank and raw binary coordinate are initialized. -/
def input (phases key:List Bool):Stack→List Bool:=
  Function.update (Function.update (fun _=>[]) (aux .phases) phases) coordinate key
/-- Both real operands enter with every work/output role empty. -/
def initial (phases key:List Bool):C.State Stack Label:=⟨some (ctl .start),none,none,input phases key,[]⟩
/-- Genuine finite21-tape machine with no prepared coordinate-cache operand. -/
def machine:Turing.FinTM2:=SemiprimeD1StackCalls.machine (aux .phases) output (ctl .start) program
/-- All21 allocated physical roles are counted. -/
theorem stack_card:Fintype.card Stack=21:=by decide
/-- Full reader inclusion retains all12 real roles. -/
theorem indexed_injective:Function.Injective indexed:=Sum.inl_injective
/-- Actual phase-bank copy has distinct physical operands. -/
theorem copy_injective:Function.Injective copyStack:=by decide
/-- Both physical field parsers use distinct operands. -/
theorem field_injective (inner:Bool):Function.Injective (fieldStack inner):=by cases inner <;> decide
/-- Both physical preserving frame sites use distinct operands. -/
theorem frame_injective (phase:Bool):Function.Injective (frameStack phase):=by cases phase <;> decide
/-- All four actual reversals have different source and target roles. -/
theorem reverse_injective (site:Fin 4):Function.Injective (reverseStack site):=by fin_cases site <;> decide
/-- Every data/return alphabet is finite before the input bytes. -/
theorem alphabets_finite:∀k,Finite (machine.Γ k):=
  SemiprimeD1StackCalls.all_alphabets_finite (aux .phases) output (ctl .start) program
/-- No address value, list, evaluator or supplied result inhabits runtime control. -/
theorem control_finite:Finite machine.σ:=SemiprimeD1StackCalls.control_finite (aux .phases) output (ctl .start) program
end RiemannGaussian.SemiprimeD1StackRecoveryCoordinate
