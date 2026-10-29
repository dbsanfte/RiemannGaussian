/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BinaryPublicAcquisitionBounds
import RiemannGaussian.SemiprimeD1StackInputWidthBounds

/-! # Original binary-input acquisition of each source-digit comparison bound
Only original binary N and the actual physical query index are initially
present. Original public preprocessing runs ONCE; the bound program directly
shares its paid bit-count/radix caches. No digit count, input width, target,
power, bound or active/inactive verdict is given to the executing machine.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPublicInputWidth
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace P
export SemiprimeD1BinaryPublicAcquisition (Stack Label program input initial digitStack)
end P
namespace W
export SemiprimeD1StackInputWidth (Stack Label Cache program initial store)
end W
/-- All37 actual Boolean roles, including unused width/radix shadow cells. -/
abbrev Stack := P.Stack⊕W.Stack
/-- Original bit-count markers physically produced by the shared preprocessing. -/
def widthKey : P.Stack := P.digitStack (SemiprimeD1BinaryPublicAcquisition.Digits.metaStack .width)
/-- Actual radix markers physically produced by that same source. -/
def radixKey : P.Stack := P.digitStack (SemiprimeD1BinaryPublicAcquisition.Digits.metaStack .radix)
/-- Actual original binary N input designation. -/
def original : Stack := .inl (P.digitStack (SemiprimeD1BinaryPublicAcquisition.Digits.metaStack .input))
/-- Child registers share the same paid public caches, without another supplier. -/
def widthStack : W.Stack→Stack
  | .widthCache=>.inl widthKey
  | .radixCache=>.inl radixKey
  | k=>.inr k
/-- Actual physically constructed binary strict bound. -/
def output : Stack := .inr .output
/-- Fixed finite entry, included control and real return labels. -/
inductive Label where
  | start | bound | done | preprocess (pc : P.Label) | acquisition (pc : W.Label)
  deriving Fintype
/-- One closed literal instruction table with no original-parameter advice. -/
def program : Label→C.Instruction Stack Label
  | .start=>.call (.preprocess (SemiprimeD1BinaryPublicAcquisition.mainLabel .start)) .bound
  | .bound=>.call (.acquisition .start) .done
  | .done=>.base .halt
  | .preprocess pc=>SemiprimeD1StackValidationLink.instruction Sum.inl Label.preprocess (P.program pc)
  | .acquisition pc=>SemiprimeD1StackValidationLink.instruction widthStack Label.acquisition (W.program pc)
/-- The only private input is the actual upstream physical index tape. -/
def privateInput (index : List Bool) (k : W.Stack) : List Bool := if k=.indexCache then index else []
/-- Original N and actual query index, with no supplied widths or bound word. -/
def input (bits index : List Bool) : Stack→List Bool := Sum.elim (P.input bits) (privateInput index)
/-- Concrete entry before both complete physical source calls. -/
def initial (bits index : List Bool) : C.State Stack Label := ⟨some .start,none,none,input bits index,[]⟩
/-- Direct public-cache sharing does not merge any two actual child registers. -/
theorem width_injective : Function.Injective widthStack := by decide
/-- Fixed actual finite machine; acquiring the physical index is caller work. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine original output .start program
/-- All real alphabets are fixed finite types before every N and query. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite original output Label.start program
/-- No unbounded numeric result, list, width or clock occurs in machine control. -/
theorem control_finite : Finite machine.σ := SemiprimeD1StackCalls.control_finite original output Label.start program
/-- Complete physical data-cell inventory, counting every unused private shadow. -/
theorem stack_card : Fintype.card Stack=37 := by decide
end RiemannGaussian.SemiprimeD1StackPublicInputWidth
