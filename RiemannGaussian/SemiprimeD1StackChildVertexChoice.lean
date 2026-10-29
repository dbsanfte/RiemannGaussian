/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildLiftVertexMeaning
import RiemannGaussian.SemiprimeD1StackChildUnitVertexMeaning
/-! # Literal activity branch between whole active and inactive vertex sources
The actual activity bit is popped. Both acquired header words and the final
record/framing scratch are shared physically; four displaced unit shadows
remain counted. This prepared eight-word source is an enclosing zip operand.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildVertexChoice
namespace A
export SemiprimeD1StackChildLiftVertex (Stack Label program initial table aux stack_card)
end A
namespace U
export SemiprimeD1StackChildUnitVertex (Stack Label program context aux stack_card)
end U
namespace J
export SemiprimeD1StackJetContext (axesCache precisionBits)
end J
namespace C
export SemiprimeD1StackCalls (State Instruction)
end C
/-- All136 active roles, all32 inactive roles and one actual activity word. -/
abbrev Stack:=A.Stack⊕(U.Stack⊕Unit)
/-- All original active-source words remain physical. -/
def active (k : A.Stack) : Stack:=.inl k
/-- Every dedicated inactive work/shadow word is counted. -/
def inactiveWork (k : U.Stack) : Stack:=.inr (.inl k)
/-- Actual activity flag, acquired by a parent-stream caller. -/
def activity : Stack:=.inr (.inr ())
/-- New original axis header is read from the active table source's retained template. -/
def newAxes : A.Stack:=A.table (SemiprimeD1StackVectorTable.template
  (SemiprimeD1StackChildTableEntry.context true J.axesCache))
/-- New original binary precision is the SAME retained header in either branch. -/
def newPrecision : A.Stack:=A.table (SemiprimeD1StackVectorTable.template
  (SemiprimeD1StackChildTableEntry.context true J.precisionBits))
/-- Both full sources write the SAME actual canonical record word. -/
def output : Stack:=active (A.aux .record)
/-- Only the two original headers and final record/frame scratch are physically shared. -/
def inactive (k : U.Stack) : Stack:=
  if k=U.context J.axesCache then active newAxes
  else if k=U.context J.precisionBits then active newPrecision
  else if k=U.aux .record then output
  else if k=U.aux .scratch then active (A.aux .scratch) else inactiveWork k
/-- Exact four-element displaced-shadow catalogue, independent of all inputs. -/
def shared (k : U.Stack) : Prop:=k=U.context J.axesCache ∨ k=U.context J.precisionBits ∨ k=U.aux .record ∨ k=U.aux .scratch
/-- Literal four-role sharing has a fixed decidable predicate. -/
instance sharedDecidable (k : U.Stack) : Decidable (shared k):=inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))
/-- Fixed physical activity/control stages. -/
inductive Control where | start | active | inactive | done | abort deriving DecidableEq
/-- The five caller labels are fixed before all source words. -/
instance controlFintype : Fintype Control:=Fintype.ofList [.start,.active,.inactive,.done,.abort] (by intro k;cases k <;> simp)
/-- Only literal enclosing and included source labels inhabit control. -/
inductive Label where | local (pc : Control) | active (pc : A.Label) | inactive (pc : U.Label) deriving Fintype
/-- One real bit pop selects one actual whole source call, followed by true halt. -/
def program : Label→C.Instruction Stack Label
  | .local .start=>.base (.pop activity (.local .abort) (.local .inactive) (.local .active))
  | .local .active=>.call (.active (.local .start)) (.local .done)
  | .local .inactive=>.call (.inactive (.local .start)) (.local .done)
  | .local .done|.local .abort=>.base .halt
  | .active pc=>SemiprimeD1StackValidationLink.instruction active Label.active (A.program pc)
  | .inactive pc=>SemiprimeD1StackValidationLink.instruction inactive Label.inactive (U.program pc)
/-- Full physical bank, including all four empty displaced input/output shadows. -/
def bank (a : A.Stack→List Bool) (u : U.Stack→List Bool) (bit : List Bool) : Stack→List Bool:=
  Sum.elim a (Sum.elim (fun k=>if shared k then [] else u k) (fun _=>bit))
/-- Seven original active-source words plus ONE actual activity bit; all dedicated inactive work is empty. -/
def initial (parent order oldAxes oldp axes precision scope bit : List Bool) : C.State Stack Label:=
  ⟨some (.local .start),none,none,bank (A.initial parent order oldAxes oldp axes precision scope).data (fun _=>[]) bit,[]⟩
/-- Actual fixed finite169-role source. -/
def machine : Turing.FinTM2:=SemiprimeD1StackCalls.machine activity output (.local .start) program
/-- Active whole-source inclusion aliases no word. -/
theorem active_injective : Function.Injective active:=Sum.inl_injective
/-- All four physical aliases preserve distinct words within the inactive source. -/
theorem inactive_injective : Function.Injective inactive:=by decide
/-- Complete allocation, including all displaced/shared shadows and the actual activity tape. -/
theorem stack_card : Fintype.card Stack=169 := by
  have hu : Fintype.card Unit=1:=by decide
  rw [Fintype.card_sum,A.stack_card,Fintype.card_sum,U.stack_card,hu]
/-- Activity and data dimensions are Boolean tapes; internal control remains fixed finite. -/
theorem control_finite : Finite machine.σ:=SemiprimeD1StackCalls.control_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackChildVertexChoice
