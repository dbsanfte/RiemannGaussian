/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootScopeBankMachine
import RiemannGaussian.SemiprimeD1StackRootScheduleOriginal
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace

/-! # Original-input acquisition of root incidence and schedule metadata
The existing scope source already acquires separate physical E and M tallies.
This program retains that source and bank, then acquires the original schedule
using the very same retained binary-N stack. No count rescan, copied N input,
prepared logarithm or branch supplier is used. Scale/leaf acquisition remains
the separate next stage.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackRootControllerMetadata
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace S
export SemiprimeD1StackRootScopeBank (Stack Label program originalInput count wireCount ids input initial)
export SemiprimeD1StackRootScopeBankExecution (result done)
end S
namespace R
export SemiprimeD1StackRootSchedule (Stack Label program boot aux input initial)
export SemiprimeD1StackRootScheduleExecution (result done)
end R
/-- All98 allocated Boolean roles, including the unused shared-input shadow. -/
abbrev Stack := S.Stack ⊕ R.Stack
/-- Every acquired original graph/source role is retained literally. -/
def sourceStack : S.Stack→Stack := Sum.inl
/-- The schedule bootstrap reads the already retained binary N directly. -/
def scheduleStack (k:R.Stack) : Stack :=
  if k=R.boot .input then sourceStack S.originalInput else .inr k
/-- Literal original-input designation; all other roles start empty. -/
def originalInput : Stack := sourceStack S.originalInput
/-- Actual occurrence cardinality, distinct from the retained original wire count. -/
def edges : Stack := sourceStack S.count
/-- Actual retained original wire count; this role is never used as M. -/
def wires : Stack := sourceStack S.wireCount
/-- Exact original logarithm output, physically acquired by repeated division. -/
def lambda : Stack := scheduleStack (R.aux .lambda)
/-- Exact root valuation-level output. -/
def levels : Stack := scheduleStack (R.aux .levels)
/-- Exact cumulative root exponent output. -/
def exponent : Stack := scheduleStack (R.aux .exponent)
/-- Exact original minimum-level guard output. -/
def minimum : Stack := scheduleStack (R.aux .minimum)
/-- Three fixed source-composition phases, independent of N. -/
inductive Control where
  | start | schedule | done
  deriving DecidableEq,Repr
instance : Fintype Control where
  elems := {.start,.schedule,.done}
  complete := by intro k;cases k <;> simp
/-- Included real-return locations are fixed before all original inputs. -/
abbrev Label := Control ⊕ (S.Label ⊕ R.Label)
/-- Literal original source label inclusion. -/
def sourceLabel (pc:S.Label) : Label := .inr (.inl pc)
/-- Literal original schedule label inclusion. -/
def scheduleLabel (pc:R.Label) : Label := .inr (.inr pc)
local notation "ctl" => (Sum.inl : Control→Label)
/-- One fixed source/count/bank/schedule program; no input-dependent code is generated. -/
def program : Label→C.Instruction Stack Label
  | .inl .start=>.call (sourceLabel (.inl .start)) (ctl .schedule)
  | .inl .schedule=>.call (scheduleLabel .start) (ctl .done)
  | .inl .done=>.base .halt
  | .inr (.inl pc)=>SemiprimeD1StackValidationLink.instruction sourceStack sourceLabel (S.program pc)
  | .inr (.inr pc)=>SemiprimeD1StackValidationLink.instruction scheduleStack scheduleLabel (R.program pc)
/-- Complete physical state, including the unused private N-input shadow. -/
def payload (source:S.Stack→List Bool) (schedule:R.Stack→List Bool) : Stack→List Bool
  | .inl k=>source k
  | .inr k=>if k=R.boot .input then [] else schedule k
/-- Original binary N alone; no derived counter or metadata word is initially supplied. -/
def input (bits:List Bool) : Stack→List Bool := Sum.elim (S.input bits) (fun _=>[])
/-- Actual one-input source entry, before all acquisition. -/
def initial (bits:List Bool) : C.State Stack Label :=
  ⟨some (ctl .start),none,none,input bits,[]⟩
/-- Exact physical state after the actual graph/count/bank source. -/
def afterSource (bits:List Bool) : Stack→List Bool := payload (S.result bits) (R.input bits)
/-- Exact retained source and fully acquired root schedule, with the original N shared. -/
def result (bits:List Bool) : Stack→List Bool := payload (S.result bits) (R.result bits)
/-- Real clean halt with the complete acquisition output retained. -/
def done (bits:List Bool) : C.State Stack Label := ⟨none,none,none,result bits,[]⟩
/-- Closed own time bound: both actual source clocks, two calls and the final halt. -/
def runBound (bits:List Bool) : Nat := SemiprimeD1StackRootScopeBankBounds.polynomial bits.length+
  SemiprimeD1StackRootScheduleExecution.runBound bits+3
/-- One genuine finite machine from original N alone; M is its designated output. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine originalInput edges (ctl .start) program
/-- Sharing binary N does not alias two distinct schedule operands. -/
theorem schedule_injective : Function.Injective scheduleStack := by decide
/-- Every physical role, including the unused shared-input shadow, is counted. -/
theorem stack_card : Fintype.card Stack=98 := by decide
/-- Every actual Boolean and finite-return alphabet is fixed and finite. -/
theorem alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
/-- The internal control contains only finite read and return-label flags. -/
theorem control_finite : Finite machine.σ := SemiprimeD1StackCalls.control_finite _ _ _ _
/-- The original graph source really retains the exact original N bytes. -/
theorem source_retained_N (bits:List Bool) : S.result bits S.originalInput=bits := by rfl
/-- Projection of the shared-input schedule roles is exact, including its input. -/
theorem payload_schedule (s:S.Stack→List Bool) (r:R.Stack→List Bool)
    (h:s S.originalInput=r (R.boot .input)) (k:R.Stack) : payload s r (scheduleStack k)=r k := by
  by_cases hk:k=R.boot .input
  · subst k
    simpa only [scheduleStack,ite_true,sourceStack,payload] using h
  · simp only [scheduleStack,hk,ite_false,payload]
end RiemannGaussian.SemiprimeD1StackRootControllerMetadata
