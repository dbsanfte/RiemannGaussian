/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootParametersOriginal
import RiemannGaussian.SemiprimeD1StackRecursiveScheduleOriginal

/-! # Literal original-N root branch and conditional child-schedule controller
All five retained operands are directly shared with the paid root-parameter
source. Eleven fresh roles implement the actual guard and optional successor.
No prepared activity bit, leaf threshold or child metadata is an input.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackRootRecursiveControl
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace P
export SemiprimeD1StackRootParameters
  (Stack Label program input initial originalInput edges lambda levels exponent minimum scale squareRoot leaf)
export SemiprimeD1StackRootParametersExecution (result done)
end P
namespace G
export SemiprimeD1StackRecursiveSchedule (Stack Label program)
end G
/-- Eleven actual guard/successor work roles, including the unused level shadow. -/
inductive Fresh where
  | left | right | limit | valid | scratch | output | shadow
  | reader | scheduleScratch | nextLevels | nextExponent
  deriving DecidableEq,Repr
instance : Fintype Fresh where
  elems := {.left,.right,.limit,.valid,.scratch,.output,.shadow,.reader,.scheduleScratch,.nextLevels,.nextExponent}
  complete := by intro k;cases k <;> simp
/-- All119 physical roles; the five actual parent operands are shared. -/
abbrev Stack := P.Stack ⊕ Fresh
/-- Entire original-N root source bank, retained during the guard and successor. -/
def sourceStack : P.Stack→Stack := Sum.inl
/-- Real guard/successor operands are aliases of acquired data, with disjoint fresh work. -/
def gateStack : G.Stack→Stack
  | .inl .leaf=>sourceStack P.leaf
  | .inl .minimum=>sourceStack P.minimum
  | .inl .levels=>sourceStack P.levels
  | .inl .edges=>sourceStack P.edges
  | .inl .left=>.inr .left
  | .inl .right=>.inr .right
  | .inl .limit=>.inr .limit
  | .inl .valid=>.inr .valid
  | .inl .scratch=>.inr .scratch
  | .inl .output=>.inr .output
  | .inr .exponent=>sourceStack P.exponent
  | .inr .levels=>.inr .shadow
  | .inr .reader=>.inr .reader
  | .inr .scratch=>.inr .scheduleScratch
  | .inr .nextLevels=>.inr .nextLevels
  | .inr .nextExponent=>.inr .nextExponent
/-- Actual original binary N is the only supplied input. -/
def originalInput : Stack := sourceStack P.originalInput
/-- Physically computed root activity bit. -/
def output : Stack := .inr .output
/-- Physically computed child valuation count, empty on inactive calls. -/
def nextLevels : Stack := .inr .nextLevels
/-- Physically computed child cumulative exponent, empty on inactive calls. -/
def nextExponent : Stack := .inr .nextExponent
/-- Three fixed entry, control and halt phases before every N. -/
inductive Control where
  | start | gate | done
  deriving DecidableEq,Repr
instance : Fintype Control where
  elems := {.start,.gate,.done}
  complete := by intro k;cases k <;> simp
/-- All included program and actual return labels remain fixed before original N. -/
abbrev Label := Control ⊕ (P.Label ⊕ G.Label)
/-- Original-input root-parameter source labels. -/
def sourceLabel (pc:P.Label) : Label := .inr (.inl pc)
/-- Actual nested guard/successor controller labels. -/
def gateLabel (pc:G.Label) : Label := .inr (.inr pc)
local notation "ctl" => (Sum.inl : Control→Label)
/-- One constant program acquires its own operands and physically chooses the original branch. -/
def program : Label→C.Instruction Stack Label
  | .inl .start=>.call (sourceLabel (.inl .start)) (ctl .gate)
  | .inl .gate=>.call (gateLabel (.inl .start)) (ctl .done)
  | .inl .done=>.base .halt
  | .inr (.inl pc)=>SemiprimeD1StackValidationLink.instruction sourceStack sourceLabel (P.program pc)
  | .inr (.inr pc)=>SemiprimeD1StackValidationLink.instruction gateStack gateLabel (G.program pc)
/-- Entire retained source and every actual fresh role, with no unbounded data in control. -/
def data (source:P.Stack→List Bool) (fresh:Fresh→List Bool) : Stack→List Bool := Sum.elim source fresh
/-- N alone, with no counters, cache, branch or child word supplied. -/
def input (bits:List Bool) : Stack→List Bool := data (P.input bits) (fun _=>[])
/-- Actual original-input entry before all acquisition. -/
def initial (bits:List Bool) : C.State Stack Label :=
  ⟨some (ctl .start),none,none,input bits,[]⟩
/-- Real gate-entry data after the entire actual parameter source has returned. -/
def afterSource (bits:List Bool) : Stack→List Bool := data (P.result bits) (fun _=>[])
/-- One genuine finite machine, with the actual acquired branch bit as designated output. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine originalInput output (ctl .start) program
/-- The five shared source operands and eleven fresh roles never alias inside the gate. -/
theorem gate_injective : Function.Injective gateStack := by decide
/-- Every one of119 allocated roles, including the unused level shadow, is counted. -/
theorem stack_card : Fintype.card Stack=119 := by
  rw [Fintype.card_sum,SemiprimeD1StackRootParameters.stack_card]
  decide
/-- Every physical Boolean/return alphabet is finite before N. -/
theorem alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
/-- The internal state has only finite Boolean and real-return-label flags. -/
theorem control_finite : Finite machine.σ := SemiprimeD1StackCalls.control_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackRootRecursiveControl
