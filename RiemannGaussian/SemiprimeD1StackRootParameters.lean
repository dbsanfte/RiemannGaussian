/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootControllerMetadataOriginal
import RiemannGaussian.SemiprimeD1StackRootScaleLeaf

/-! # One original-input program for every root scheduling operand
The original incidence/schedule source runs once. The scale/square-root/leaf
stage then reuses its fifteen physically acquired root-cache roles, allocating
only ten fresh roles. The original source and binary N stay retained throughout.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackRootParameters
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace M
export SemiprimeD1StackRootControllerMetadata
  (Stack Label program input initial originalInput scheduleStack edges lambda levels exponent minimum result done runBound)
end M
namespace L
export SemiprimeD1StackRootScaleLeaf (Stack Label program Aux aux ready)
end L
/-- Exactly the ten fresh physical work/output roles used after root acquisition. -/
abbrev Fresh := SemiprimeD1StackUnaryDivmod.Stack ⊕ L.Aux
/-- All108 physical roles; the acquired old15 cache is shared rather than cloned. -/
abbrev Stack := M.Stack ⊕ Fresh
/-- Complete retained original source and root-metadata bank. -/
def metadataStack : M.Stack→Stack := Sum.inl
/-- The leaf stage shares each actual old-cache role and has ten disjoint fresh roles. -/
def leafStack : L.Stack→Stack
  | .inl k=>metadataStack (M.scheduleStack k)
  | .inr k=>.inr k
/-- Only the original binary N role is initially populated. -/
def originalInput : Stack := metadataStack M.originalInput
/-- Actual acquired original occurrence count. -/
def edges : Stack := metadataStack M.edges
/-- Actual original logarithmic parameter. -/
def lambda : Stack := metadataStack M.lambda
/-- Actual root level count. -/
def levels : Stack := metadataStack M.levels
/-- Actual root cumulative exponent. -/
def exponent : Stack := metadataStack M.exponent
/-- Actual root minimum-level guard. -/
def minimum : Stack := metadataStack M.minimum
/-- Actual materialized original public scale. -/
def scale : Stack := leafStack (L.aux .scale)
/-- Actual exact integer square root of the acquired logarithm. -/
def squareRoot : Stack := leafStack (L.aux .root)
/-- Actual original leaf-size guard, acquired by real division. -/
def leaf : Stack := leafStack (L.aux .leaf)
/-- Three fixed caller phases, independent of N. -/
inductive Control where
  | start | leaf | done
  deriving DecidableEq,Repr
instance : Fintype Control where
  elems := {.start,.leaf,.done}
  complete := by intro k;cases k <;> simp
/-- All actual component and outer return labels are fixed before every input. -/
abbrev Label := Control ⊕ (M.Label ⊕ L.Label)
/-- Actual complete metadata-source program labels. -/
def metadataLabel (pc:M.Label) : Label := .inr (.inl pc)
/-- Actual ready-stage leaf-program labels. -/
def leafLabel (pc:L.Label) : Label := .inr (.inr pc)
local notation "ctl" => (Sum.inl : Control→Label)
/-- One literal program: original N acquisition, paid ready-stage threshold construction, halt. -/
def program : Label→C.Instruction Stack Label
  | .inl .start=>.call (metadataLabel (.inl .start)) (ctl .leaf)
  | .inl .leaf=>.call (leafLabel .ready) (ctl .done)
  | .inl .done=>.base .halt
  | .inr (.inl pc)=>SemiprimeD1StackValidationLink.instruction metadataStack metadataLabel (M.program pc)
  | .inr (.inr pc)=>SemiprimeD1StackValidationLink.instruction leafStack leafLabel (L.program pc)
/-- Every old and fresh physical data role is represented literally. -/
def data (acquired:M.Stack→List Bool) (fresh:Fresh→List Bool) : Stack→List Bool := Sum.elim acquired fresh
/-- Binary N is the sole supplied input; all ten new roles are initially empty. -/
def input (bits:List Bool) : Stack→List Bool := data (M.input bits) (fun _=>[])
/-- Original-input entry before any graph, count, logarithm or threshold acquisition. -/
def initial (bits:List Bool) : C.State Stack Label :=
  ⟨some (ctl .start),none,none,input bits,[]⟩
/-- Actual threshold-stage input after all required old-cache fields have been acquired. -/
def afterMetadata (bits:List Bool) : Stack→List Bool := data (M.result bits) (fun _=>[])
/-- Own caller allowance: actual metadata bound, ready-stage cubic, two real calls and halt. -/
def runBound (bits:List Bool) : Nat := M.runBound bits+10^12*(bits.length+1)^3+3
/-- One genuine finite original-input machine, with its actual leaf threshold designated output. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine originalInput leaf (ctl .start) program
/-- Shared old-cache roles and fresh physical roles never alias within the leaf program. -/
theorem leaf_injective : Function.Injective leafStack := by
  intro i j h
  cases i with
  | inl i=>cases j with
    | inl j=>exact congrArg Sum.inl (SemiprimeD1StackRootControllerMetadata.schedule_injective (Sum.inl.inj h))
    | inr j=>cases h
  | inr i=>cases j with
    | inl j=>cases h
    | inr j=>exact congrArg Sum.inr (Sum.inr.inj h)
/-- All108 physical roles include the retained98 bank and ten actually new roles. -/
theorem stack_card : Fintype.card Stack=108 := by
  rw [Fintype.card_sum,SemiprimeD1StackRootControllerMetadata.stack_card,Fintype.card_sum]
  decide
/-- Every real data/return alphabet is finite and fixed before N. -/
theorem alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
/-- The internal state contains only finite read and actual return-label flags. -/
theorem control_finite : Finite machine.σ := SemiprimeD1StackCalls.control_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackRootParameters
