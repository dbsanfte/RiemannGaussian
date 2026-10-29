/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedRootMetadataOriginal
import RiemannGaussian.SemiprimeD1StackJetContextBounds
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace

/-! # Actual original-N packed root context acquisition
The binary precision is physically acquired from N, copied into a real context
source, and decoded to TRUE width markers there. The retained FALSE fit template
is not used as a context cache. No rank, precision or context answer is supplied.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPackedRootContext
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace M
export SemiprimeD1StackPackedRootMetadata (Stack Label program initial input boot aux)
export SemiprimeD1StackPackedRootMetadataEncoding (precisionWord result done)
end M
namespace J
export SemiprimeD1StackJetContext (Stack Label program initial axesCache precisionBits rankCache widthCache)
end J
/-- Every actual metadata and context allocation, including all private shadows. -/
abbrev Stack := M.Stack⊕J.Stack
/-- Full actual metadata-source inclusion. -/
def metadata (k : M.Stack) : Stack := .inl k
/-- All15 actual context words are allocated and counted. -/
def context (k : J.Stack) : Stack := .inr k
/-- The sole initial binary-input role. -/
def originalInput : Stack := metadata (M.boot .input)
/-- Actual newly acquired binary precision, retained before and after context acquisition. -/
def precision : Stack := metadata (M.aux .precision)
/-- Actual physically acquired TRUE context width, distinct from the FALSE fit template. -/
def width : Stack := context J.widthCache
/-- Actual physically acquired unary rank, equal to one at the axis-free root. -/
def rank : Stack := context J.rankCache
/-- One actual preserving copy, using the metadata source's proven empty scratch. -/
def copyStack (k : Fin 3) : Stack :=
  if k=0 then precision else if k=1 then context J.precisionBits else metadata (M.aux .copyScratch)
/-- Literal fixed source/copy/header/context phases. -/
inductive Control where | start | copyPrecision | seedAxes | acquireContext | done
  deriving DecidableEq,Repr
/-- Five fixed control locations, before all N and all context values. -/
instance controlFintype : Fintype Control := Fintype.ofList [.start,.copyPrecision,.seedAxes,.acquireContext,.done]
  (by intro k;cases k <;> simp)
/-- Complete finite label bank for both actual callees and the real copy. -/
abbrev Label := Control⊕(M.Label⊕(J.Label⊕Fin 9))
/-- Actual metadata-callee label inclusion. -/
def metadataLabel (pc : M.Label) : Label := .inr (.inl pc)
/-- Actual context-callee label inclusion. -/
def contextLabel (pc : J.Label) : Label := .inr (.inr (.inl pc))
/-- Actual paid-copy label inclusion. -/
def copyLabel (pc : Fin 9) : Label := .inr (.inr (.inr pc))
local notation "ctl" => (Sum.inl : Control→Label)
/-- One fixed finite program. EMPTY axes are written as the actual FALSE vector
terminator; binary precision and TRUE width are acquired by real sources. -/
def program : Label→C.Instruction Stack Label
  | .inl .start => .call (metadataLabel (.local .start)) (ctl .copyPrecision)
  | .inl .copyPrecision => .call (copyLabel 0) (ctl .seedAxes)
  | .inl .seedAxes => .base (.push (context J.axesCache) false (ctl .acquireContext))
  | .inl .acquireContext => .call (contextLabel .start) (ctl .done)
  | .inl .done => .base .halt
  | .inr (.inl pc) => SemiprimeD1StackValidationLink.instruction metadata metadataLabel (M.program pc)
  | .inr (.inr (.inl pc)) => SemiprimeD1StackValidationLink.instruction context contextLabel (J.program pc)
  | .inr (.inr (.inr pc)) => SemiprimeD1StackMultiplierLink.instruction copyStack copyLabel (SemiprimeD1StackCopy.code pc)
/-- Exact full two-bank physical state view. -/
def data (m : M.Stack→List Bool) (j : J.Stack→List Bool) : Stack→List Bool := Sum.elim m j
/-- Only original binary N is populated at initialization. -/
def input (bits : List Bool) : Stack→List Bool := data (M.input bits) (fun _ => [])
/-- Actual N-only front door, before either acquisition source has run. -/
def initial (bits : List Bool) : C.State Stack Label := ⟨some (ctl .start),none,none,input bits,[]⟩
/-- Genuine finite original-input machine with the newly acquired rank as output. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine originalInput rank (ctl .start) program
/-- The complete allocated data inventory is28, including every retained/private word. -/
theorem stack_card : Fintype.card Stack=28 := by decide
/-- Actual metadata operands are distinct. -/
theorem metadata_injective : Function.Injective metadata := Sum.inl_injective
/-- All context operands are physically distinct. -/
theorem context_injective : Function.Injective context := Sum.inr_injective
/-- Copy never aliases its actual source, destination or restoring scratch. -/
theorem copy_injective : Function.Injective copyStack := by decide
/-- Every actual Boolean and saved-return alphabet is finite. -/
theorem alphabets_finite : ∀k,Finite (machine.Γ k) := SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
/-- Runtime internal state contains only finite read flags and labels. -/
theorem control_finite : Finite machine.σ := SemiprimeD1StackCalls.control_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackPackedRootContext
