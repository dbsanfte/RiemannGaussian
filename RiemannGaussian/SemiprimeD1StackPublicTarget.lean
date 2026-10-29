/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BinaryPublicAcquisitionBounds
import RiemannGaussian.SemiprimeD1StackJetReadExecution
import RiemannGaussian.SemiprimeD1StackJetPoint
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
/-! # Actual original-binary preprocess digit acquisition and physical target read
The ONLY numeric source is original binary N. A physical unary query index is
separately supplied; deriving it from a vertex/assignment remains caller work.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackPublicTarget
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace P
export SemiprimeD1BinaryPublicAcquisition (Stack Label program input initial digitStack)
end P
namespace R
export SemiprimeD1StackJetRead (Stack Label program state store)
end R
/-- Thirty-six Boolean roles, including the complete acquired original metadata. -/
abbrev Stack := P.Stack⊕R.Stack
/-- The ACTUAL publicly acquired digit-bank output, shared directly with reader cache. -/
def bank : P.Stack := P.digitStack (SemiprimeD1BinaryPublicAcquisition.Digits.bankStack SemiprimeD1StackDigitBank.output)
/-- Actual target reader shares acquired bytes; other reader roles are separate. -/
def readStack : R.Stack→Stack
  | .cache=>.inl bank
  | k=>.inr k
/-- Fixed physical caller and included literal procedure labels. -/
inductive Label where
  | start | read | done | preprocess (pc : P.Label) | reader (pc : R.Label)
  deriving DecidableEq,Fintype
/-- Physical original-input acquisition followed by the actual cached field scan. -/
def program : Label→C.Instruction Stack Label
  | .start=>.call (.preprocess (SemiprimeD1BinaryPublicAcquisition.mainLabel .start)) .read
  | .read=>.call (.reader .start) .done
  | .done=>.base .halt
  | .preprocess pc=>SemiprimeD1StackValidationLink.instruction Sum.inl Label.preprocess (P.program pc)
  | .reader pc=>SemiprimeD1StackValidationLink.instruction readStack Label.reader (R.program pc)
/-- Literal combined physical bank, not a native selected-digit supplier. -/
def store (preprocess : P.Stack→List Bool) (reader : R.Stack→List Bool) : Stack→List Bool := Sum.elim preprocess reader
/-- Original binary N and actual unary index bytes, every workspace initially empty. -/
def input (bits index : List Bool) : Stack→List Bool := store (P.input bits) (R.store [] [] index [] [] [] [] [])
/-- Actual fixed source entry. Preparing the unary query remains an explicit caller stage. -/
def initial (bits index : List Bool) : C.State Stack Label := ⟨some .start,none,none,input bits index,[]⟩
/-- No physical role alias occurs within the actual reader. -/
theorem read_injective : Function.Injective readStack := by
  intro i j h;cases i <;> cases j <;> simp_all [readStack]
/-- Actual fixed finite machine, not a native cached digit lookup. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine
  (.inl (P.digitStack (SemiprimeD1BinaryPublicAcquisition.Digits.metaStack .input))) (.inr .output) .start program
/-- ALL alphabets, including actual real return labels, are finite. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite _ _ Label.start program
/-- No decoded N, index or digit occurs in finite control. -/
theorem control_finite : Finite machine.σ := SemiprimeD1StackCalls.control_finite _ _ Label.start program
/-- Exact fixed data-role count. -/
theorem stack_card : Fintype.card Stack=36 := by decide
end RiemannGaussian.SemiprimeD1StackPublicTarget
