/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackUnarySumLessBytecode
import RiemannGaussian.SemiprimeD1StackProcedureTrace
import RiemannGaussian.SemiprimeD1Schedule

/-! # Literal original active-call guard
All four bounded metadata counters live on Boolean stacks. Three actual
comparisons, preserving copies and physical verdict reads replace the native
active predicate. Acquiring those counters remains the caller's obligation.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackScheduleActive
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace Less
export SemiprimeD1StackUnarySumLess (Stack contents)
export SemiprimeD1StackUnarySumLessBytecode (Label code entry)
end Less
/-- Four retained bounded-metadata operands. -/
inductive Param where
  | leaf | minimum | levels | edges
  deriving DecidableEq,Repr
instance : Fintype Param where
  elems := {.leaf,.minimum,.levels,.edges}
  complete := by intro k;cases k <;> simp
/-- Ten fixed Boolean roles, including every comparator and copy work stack. -/
inductive Stack where
  | leaf | minimum | levels | edges | left | right | limit | valid | scratch | output
  deriving DecidableEq,Repr
instance : Fintype Stack where
  elems := {.leaf,.minimum,.levels,.edges,.left,.right,.limit,.valid,.scratch,.output}
  complete := by intro k;cases k <;> simp
/-- The three fixed checks, independent of any input sizes. -/
inductive Test where
  | leaf | minimum | maximum
  deriving DecidableEq,Repr
instance : Fintype Test where
  elems := {.leaf,.minimum,.maximum}
  complete := by intro k;cases k <;> simp
/-- Fixed phases of the three actual comparison invocations. -/
inductive Control where
  | left (test:Test) | right (test:Test) | compare (test:Test) | branch (test:Test)
  | emit (value:Bool) | done
  deriving DecidableEq,Fintype,Repr
/-- Included literal copy and comparator labels. -/
abbrev Label := Control ⊕ (((Test×Bool)×Fin 9) ⊕ (Test×Less.Label))
/-- Retained parameter stack associated with a metadata field. -/
def paramStack : Param→Stack
  | .leaf=>.leaf | .minimum=>.minimum | .levels=>.levels | .edges=>.edges
/-- Literal operand choice for each of the three strict comparisons. -/
def operand : Test→Bool→Param
  | .leaf,false=>.leaf | .leaf,true=>.edges
  | .minimum,false=>.levels | .minimum,true=>.minimum
  | .maximum,false=>.edges | .maximum,true=>.levels
/-- Actual preserving-copy operands, with no numerical control. -/
def copyStack (test:Test) (right:Bool) (k:Fin 3) : Stack :=
  if k=0 then paramStack (operand test right)
  else if k=1 then if right then .limit else .left else .scratch
/-- Four real consuming-comparator roles; its spare summand is physically empty. -/
def lessStack : Less.Stack→Stack
  | .left=>.left | .right=>.right | .limit=>.limit | .valid=>.valid
/-- Included copy entry and continuation labels. -/
def copyLabel (test:Test) (right:Bool) (pc:Fin 9) : Label := .inr (.inl ((test,right),pc))
/-- Included actual comparator labels. -/
def lessLabel (test:Test) (pc:Less.Label) : Label := .inr (.inr (test,pc))
/-- Finite verdict routing implements the conjunction without an arithmetic predicate. -/
def afterCheck : Test → Bool → Control
  | .leaf,true=>.left .minimum | .minimum,false=>.left .maximum
  | .maximum,false=>.emit true | _,_=>.emit false
local notation "ctl" => (Sum.inl : Control→Label)
/-- One fixed literal guard program for every prepared metadata instance. -/
def program : Label→C.Instruction Stack Label
  | .inl (.left test)=>.call (copyLabel test false 0) (ctl (.right test))
  | .inl (.right test)=>.call (copyLabel test true 0) (ctl (.compare test))
  | .inl (.compare test)=>.call (lessLabel test Less.entry) (ctl (.branch test))
  | .inl (.branch test)=>.base (.pop .valid (ctl (.emit false))
      (ctl (afterCheck test false)) (ctl (afterCheck test true)))
  | .inl (.emit value)=>.base (.push .output value (ctl .done))
  | .inl .done=>.base .halt
  | .inr (.inl ((test,right),pc))=>SemiprimeD1StackMultiplierLink.instruction
      (copyStack test right) (copyLabel test right) (SemiprimeD1StackCopy.code pc)
  | .inr (.inr (test,pc))=>SemiprimeD1StackMultiplierLink.instruction
      lessStack (lessLabel test) (Less.code pc)
/-- Exact physical payload; comparator spare and copy scratch are explicitly empty. -/
def data (words:Param→List Bool) (left limit valid out:List Bool) : Stack→List Bool
  | .leaf=>words .leaf | .minimum=>words .minimum | .levels=>words .levels | .edges=>words .edges
  | .left=>left | .limit=>limit | .valid=>valid | .output=>out | _=>[]
/-- Original metadata counters are payload, never numerical internal registers. -/
def words (leaf minimum levels edges:Nat) : Param→List Bool
  | .leaf=>List.replicate leaf true | .minimum=>List.replicate minimum true
  | .levels=>List.replicate levels true | .edges=>List.replicate edges true
/-- Prepared guard input has no advised branch or verdict. -/
def initial (leaf minimum levels edges:Nat) : C.State Stack Label :=
  ⟨some (ctl (.left .leaf)),none,none,data (words leaf minimum levels edges) [] [] [] [],[]⟩
/-- Fixed genuine finite Boolean-stack guard machine. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine Stack.leaf Stack.output
  (ctl (.left .leaf)) program
/-- Preserving-copy operands never alias. -/
theorem copyStack_injective (test:Test) (right:Bool) : Function.Injective (copyStack test right) := by
  cases test <;> cases right <;> decide
/-- The consuming comparator has four distinct physical operands. -/
theorem lessStack_injective : Function.Injective lessStack := by decide
/-- Every physical data role is included in storage accounting. -/
theorem stack_card : Fintype.card Stack=10 := by decide
/-- Every actual alphabet, including real return labels, is finite. -/
theorem alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
/-- Internal state contains only finite read and return-label flags. -/
theorem control_finite : Finite machine.σ := SemiprimeD1StackCalls.control_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackScheduleActive
