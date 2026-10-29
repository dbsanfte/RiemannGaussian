/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackDotEvaluateBounds
import RiemannGaussian.SemiprimeD1StackVectorCanonicalBounds
/-! # CLOSED guarded numerical dot caller
The real guard and real source/evaluator share the SAME physical vector and
binary modulus. Only the physically computed verdict chooses evaluation.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackGuardedDotEvaluate
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace D
export SemiprimeD1StackDotEvaluate (Stack Label program initial code modulus output)
export SemiprimeD1StackExprDot (Cache)
end D
namespace V
export SemiprimeD1StackVectorCanonical (Stack Label program initial store)
end V
/-- All 107 physical Boolean roles, including two unused empty private aliases. -/
abbrev Stack := D.Stack⊕V.Stack
/-- Numerical result, empty on the rejected path. -/
def output : Stack := .inl D.output
/-- Actual guard verdict is popped, then the successful/rejected status is pushed. -/
def status : Stack := .inr .output
/-- Actual SAME vector/modulus stacks, with all parser/comparison work private. -/
def guardStack : V.Stack→Stack
  | .cache=>.inl (.inl .cache)
  | .modulus=>.inl D.modulus
  | k=>.inr k
/-- Fixed locations of the actual gate and whole dot procedure. -/
inductive Label where
  | start | branch | evaluate | accept | reject | done | bad
  | check (pc : V.Label) | dot (pc : D.Label)
  deriving Fintype
/-- ONE closed program; no supplied validity/verdict/evaluator/clock function. -/
def program : Label→C.Instruction Stack Label
  | .start=>.call (.check .start) .branch
  | .branch=>.base (.pop status .bad .reject .evaluate)
  | .evaluate=>.call (.dot .start) .accept
  | .accept=>.base (.push status true .done)
  | .reject=>.base (.push status false .done)
  | .done | .bad=>.base .halt
  | .check pc=>SemiprimeD1StackValidationLink.instruction guardStack Label.check (V.program pc)
  | .dot pc=>SemiprimeD1StackValidationLink.instruction Sum.inl Label.dot (D.program pc)
/-- Literal status/private guard store. Unused cache/modulus shadows stay empty. -/
def flags (verdict : List Bool) : V.Stack→List Bool := fun k=>if k=.output then verdict else []
/-- Literal combined physical store, not a producer or computed answer supplier. -/
def store (dot : D.Stack→List Bool) (verdict : List Bool) : Stack→List Bool := Sum.elim dot (flags verdict)
/-- Physical prepared base/vector/metadata/modulus/suffix only, no canonicality
or whole-source validity, count answer or numerical output is initially present. -/
def initial (c : D.Cache) (cached tail : List Bool) : C.State Stack Label :=
  ⟨some .start,none,none,store (D.initial c cached tail).data [],[]⟩
/-- Guard roles have no actual alias within its included component. -/
theorem guard_injective : Function.Injective guardStack := by
  intro i j h;cases i <;> cases j <;> simp_all [guardStack,D.modulus]
/-- Actual fixed finite guarded caller; rejected vectors never invoke DotEvaluate. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine (.inl (.inl .base)) output .start program
/-- Every actual data and return alphabet is fixed and finite. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) := SemiprimeD1StackCalls.all_alphabets_finite _ _ Label.start program
/-- No input-sized syntax, number, word, function or validity answer occurs in control. -/
theorem control_finite : Finite machine.σ := SemiprimeD1StackCalls.control_finite _ _ Label.start program
/-- All private aliases and the entire real evaluator bank are counted. -/
theorem stack_card : Fintype.card Stack=107 := by decide
end RiemannGaussian.SemiprimeD1StackGuardedDotEvaluate
