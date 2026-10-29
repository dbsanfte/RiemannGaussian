/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerPrefixBounds
import RiemannGaussian.SemiprimeD1StackDigitCountExecution
import RiemannGaussian.SemiprimeD1StackOwnerPaletteSource
import RiemannGaussian.SemiprimeD1StackValidationLink
/-! # Physical scope/prefix to complete original owner table
Actual scope records acquire degree by the literal counter. Every prefix key
and value is then physically read. Only COMPUTED degree/compatibility flags
select the finite literal output code. Scope/key acquisition is caller work;
no count, allowed-value answer, table, predicate or clock is an input here.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackOwnerTable
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace P
export SemiprimeD1StackOwnerPrefix (Stack Label program data)
end P
namespace D
export SemiprimeD1StackDigitCount (Stack Label program data)
end D
namespace T
export SemiprimeD1StackOwnerPaletteSource (Mode Label code)
end T
/-- All ten scan roles, all seven count roles and one literal output role. -/
abbrev Stack := P.Stack⊕(D.Stack⊕Unit)
/-- Every actual code alternative is fixed and finite before original input. -/
inductive Label where
  | start | count0 | count1 | count2 | scan (degree : Fin 3)
  | low (degree : Fin 3) | high (degree : Fin 3) (low : Bool)
  | emit (degree : Fin 3) (low high : Bool) | done | abort
  | prefixScan (pc : P.Label) | count (pc : D.Label) | palette (pc : T.Label)
  deriving Fintype
/-- Physical original wire key. -/
def query : Stack := .inl (.inr .query)
/-- Actual framed original-prefix reader. -/
def reader : Stack := .inl (.inr .reader)
/-- Actual scope-ID vector, acquired by the graph caller. -/
def scope : Stack := .inr (.inl .bank)
/-- Actual degree tally, computed by a physical vector scan. -/
def tally : Stack := .inr (.inl .count)
/-- Actual two compatibility bits, computed by physical prefix reads. -/
def answer : Stack := .inl (.inr .output)
/-- Complete actually written original-codec owner tensor. -/
def output : Stack := .inr (.inr ())
/-- Actual count-loop role map, sharing the retained scope vector directly. -/
def countStack (k : D.Stack) : Stack := .inr (.inl k)
/-- One fixed finite original owner-table acquisition program. -/
def program : Label→C.Instruction Stack Label
  | .start=>.call (.count (.inl .main)) .count0
  | .count0=>.base (.pop tally (.scan 0) .count1 .count1)
  | .count1=>.base (.pop tally (.scan 1) .count2 .count2)
  | .count2=>.base (.pop tally (.scan 2) .abort .abort)
  | .scan degree=>.call (.prefixScan (.loop true true)) (.low degree)
  | .low degree=>.base (.pop answer .abort (.high degree false) (.high degree true))
  | .high degree low=>.base (.pop answer .abort (.emit degree low false) (.emit degree low true))
  | .emit degree low high=>.call (.palette ((degree,low,high),0)) .done
  | .done | .abort=>.base .halt
  | .prefixScan pc=>SemiprimeD1StackValidationLink.instruction Sum.inl Label.prefixScan (P.program pc)
  | .count pc=>SemiprimeD1StackValidationLink.instruction countStack Label.count (D.program pc)
  | .palette pc=>SemiprimeD1StackMultiplierLink.instruction (fun _=>output) Label.palette (T.code pc)
/-- Pure specification of ALL physical roles, not an instruction-time getter. -/
def data (key prefixBytes scopeBytes count prefixAnswer outputBytes : List Bool) : Stack→List Bool :=
  Sum.elim (P.data key prefixBytes [] [] [] [] prefixAnswer)
    (Sum.elim (D.data scopeBytes [] count [] [] [] []) (fun _=>outputBytes))
/-- Initial data includes only actual key/prefix/scope records, no count/flags. -/
def initial (key prefixBytes scopeBytes : List Bool) : C.State Stack Label :=
  ⟨some .start,none,none,data key prefixBytes scopeBytes [] [] [],[]⟩
/-- The whole fixed source compiles into ONE finite machine. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine reader output .start program
/-- All eighteen roles, including shadow/work caches, are counted. -/
theorem stack_card : Fintype.card Stack=18 := by decide
/-- Scope-counter roles never alias. -/
theorem count_injective : Function.Injective countStack := by intro a b h;exact Sum.inl.inj (Sum.inr.inj h)
/-- Every Boolean/real-return alphabet is fixed and finite before every family. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite reader output Label.start program
/-- Finite control never contains an unbounded list, numeric value or evaluator. -/
theorem control_finite : Finite machine.σ := SemiprimeD1StackCalls.control_finite reader output Label.start program
end RiemannGaussian.SemiprimeD1StackOwnerTable
