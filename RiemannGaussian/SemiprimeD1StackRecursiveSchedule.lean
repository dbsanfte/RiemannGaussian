/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackScheduleActiveOriginal
import RiemannGaussian.SemiprimeD1StackScheduleSuccessorOriginal
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace

/-! # One physical active decision and conditional child-schedule acquisition
The level operand is physically shared between the guard and successor.
Inactive calls stop before constructing child metadata; active calls acquire
the child schedule once. Network/context acquisition and recursive phase work
remain separate caller obligations.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackRecursiveSchedule
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace A
export SemiprimeD1StackScheduleActive (Stack Label program data)
export SemiprimeD1StackScheduleActiveExecution (start done unaryWords answer volume)
end A
namespace S
export SemiprimeD1StackScheduleSuccessor (Stack Label program initial result)
export SemiprimeD1StackScheduleSuccessorExecution (done runTime)
end S
/-- All sixteen physical roles, including the unused shared-level shadow. -/
abbrev Stack := A.Stack ⊕ S.Stack
/-- Guard roles are retained literally. -/
def guardStack : A.Stack→Stack := Sum.inl
/-- The successor reads the actual guard level stack directly. -/
def successorStack (k:S.Stack) : Stack := if k=.levels then .inl .levels else .inr k
/-- Four fixed local schedule phases. -/
inductive Control where
  | start | branch | successor | done
  deriving DecidableEq,Repr
instance : Fintype Control where
  elems := {.start,.branch,.successor,.done}
  complete := by intro k;cases k <;> simp
/-- Local and actual nested component return labels, all fixed before inputs. -/
abbrev Label := Control ⊕ (A.Label ⊕ S.Label)
/-- Included guard labels. -/
def guardLabel (pc:A.Label) : Label := .inr (.inl pc)
/-- Included successor labels. -/
def successorLabel (pc:S.Label) : Label := .inr (.inr pc)
local notation "ctl" => (Sum.inl : Control→Label)
/-- One literal program physically reads the acquired guard verdict. -/
def program : Label→C.Instruction Stack Label
  | .inl .start=>.call (guardLabel (.inl (.left .leaf))) (ctl .branch)
  | .inl .branch=>.base (.peek (guardStack .output) (ctl .done) (ctl .done) (ctl .successor))
  | .inl .successor=>.call (successorLabel (.inl .start)) (ctl .done)
  | .inl .done=>.base .halt
  | .inr (.inl pc)=>SemiprimeD1StackValidationLink.instruction guardStack guardLabel (A.program pc)
  | .inr (.inr pc)=>SemiprimeD1StackValidationLink.instruction successorStack successorLabel (S.program pc)
/-- Every physical role is explicit; the aliased successor shadow stays empty. -/
def payload (guard:A.Stack→List Bool) (successor:S.Stack→List Bool) : Stack→List Bool
  | .inl k=>guard k
  | .inr k=>if k=.levels then [] else successor k
/-- Prepared metadata input; there is no advised activity bit or child schedule. -/
def initial (a:List Bool) (v:SemiprimeD1StackScheduleActive.Param→Nat) : C.State Stack Label :=
  ⟨some (ctl .start),none,none,payload (A.start v).data (S.initial a (A.unaryWords v .levels)).data,[]⟩
/-- Physical metadata after the real guard call, before its verdict is inspected. -/
def ready (a:List Bool) (v:SemiprimeD1StackScheduleActive.Param→Nat) : Stack→List Bool :=
  payload (A.done v).data (S.initial a (A.unaryWords v .levels)).data
/-- Physical metadata after a real active successor call. -/
def afterSuccessor (a:List Bool) (v:SemiprimeD1StackScheduleActive.Param→Nat) : Stack→List Bool :=
  payload (A.done v).data (S.result a (A.unaryWords v .levels))
/-- Exact conditional final payload; its test is specification only. -/
def result (a:List Bool) (v:SemiprimeD1StackScheduleActive.Param→Nat) : Stack→List Bool :=
  if A.answer v then afterSuccessor a v else ready a v
/-- Actual standalone halt, retaining the physical guard verdict and all parent metadata. -/
def done (a:List Bool) (v:SemiprimeD1StackScheduleActive.Param→Nat) : C.State Stack Label :=
  ⟨none,none,none,result a v,[]⟩
/-- Own complete prepared-input clock allowance for this same actual program. -/
def runBound (a:List Bool) (v:SemiprimeD1StackScheduleActive.Param→Nat) : Nat :=
  300*(A.volume v+a.length+1)
/-- One genuine finite machine before all prepared metadata inputs. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine (guardStack .leaf)
  (guardStack .output) (ctl .start) program
/-- Sharing the actual level operand introduces no alias inside the successor. -/
theorem successor_injective : Function.Injective successorStack := by decide
/-- The shared role and its unused shadow are both counted in physical storage. -/
theorem stack_card : Fintype.card Stack=16 := by decide
/-- All actual data and return alphabets are finite. -/
theorem alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
/-- The internal state has only finite Boolean and return-label flags. -/
theorem control_finite : Finite machine.σ := SemiprimeD1StackCalls.control_finite _ _ _ _
/-- Exact successor projection with the one physically shared level word. -/
theorem payload_successor (g:A.Stack→List Bool) (s:S.Stack→List Bool)
    (hs:g .levels=s .levels) (k:S.Stack) : payload g s (successorStack k)=s k := by
  cases k <;> simp [payload,successorStack,hs]
end RiemannGaussian.SemiprimeD1StackRecursiveSchedule
