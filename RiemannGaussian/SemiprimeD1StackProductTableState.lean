/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProductTableCleanup
/-! # Concrete reached stores of the product-table DFS
All functions below are correctness views of Boolean cells. The executed
program has no native depth, prefix, assignment or checker-function argument.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackProductTableState
open SemiprimeD1StackProductTable SemiprimeD1StackProductTableCleanup
open SemiprimeD1StackUnaryDivmod (unary)
/-- Stable recursion data: reusable checker clear, original N retained, unary
depth and reverse prefix physical, serialized tape accumulated in reverse. -/
def data (bits : List Bool) (depth : ℕ) (front reversed : List Bool) : Stack→List Bool
  | .inl _=>[]
  | .inr .source=>bits
  | .inr .depth=>unary depth
  | .inr .prefix=>front
  | .inr .reversed=>reversed
  | _=>[]
/-- Proof view of replacing exactly the actual checker bank, preserving callers. -/
def withChecker (base : Stack→List Bool) (checker : P.Stack→List Bool) : Stack→List Bool :=
  Sum.elim checker (fun k=>base (.inr k))
/-- Copying the actual current reverse prefix retains the prefix itself. -/
def prefixCopied (bits front reversed : List Bool) : Stack→List Bool :=
  Function.update (data bits 0 front reversed) (.inr .work) front
/-- Consuming that real copy reverses it into the actual raw checker input. -/
def rawReady (bits front reversed : List Bool) : Stack→List Bool :=
  Function.update (data bits 0 front reversed) (.inl P.assignment) front.reverse
/-- The real original-N copy completes the original checker input bank. -/
def checkerReady (bits front reversed : List Bool) : Stack→List Bool :=
  Function.update (rawReady bits front reversed) (.inl P.original) bits
/-- The ACTUAL completed checker bank is retained until physical full cleanup. -/
def checked (bits front reversed : List Bool) : Stack→List Bool :=
  withChecker (data bits 0 front reversed) (SemiprimeD1StackPublicProductExecution.done bits front.reverse).data
/-- Actual finite original acquisition initializes only its input N register. -/
private theorem public_input (bits : List Bool) (k : SemiprimeD1BinaryPublicAcquisition.Stack) :
    SemiprimeD1BinaryPublicAcquisition.input bits k=
      if k=SemiprimeD1BinaryPublicAcquisition.digitStack (SemiprimeD1BinaryPublicAcquisition.Digits.metaStack .input) then bits else [] := by
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> rfl
    · rcases k with k|k
      · rcases k with k|k
        · cases k <;> rfl
        · fin_cases k <;> rfl
      · cases k;rfl
  · rcases k with k|k
    · cases k <;> rfl
    · fin_cases k <;> rfl
/-- Actual original-checker initialization agrees with its two physical copies,
not with a supplied raw/metadata/canonicality answer. -/
theorem checkerReady_input (bits front reversed : List Bool) :
    checkerReady bits front reversed=withChecker (data bits 0 front reversed)
      (SemiprimeD1StackPublicProduct.initial bits front.reverse).data := by
  funext k
  cases k with
  | inl k=>
    rcases k with k|k
    · rw [show (withChecker (data bits 0 front reversed) (SemiprimeD1StackPublicProduct.initial bits front.reverse).data)
          (.inl (.inl k))=SemiprimeD1BinaryPublicAcquisition.input bits k from rfl,public_input]
      by_cases hk : k=SemiprimeD1BinaryPublicAcquisition.digitStack (SemiprimeD1BinaryPublicAcquisition.Digits.metaStack .input)
      · subst k;rfl
      · have ho : (Sum.inl (Sum.inl k) : Stack)≠.inl P.original := by
          intro h
          exact hk (Sum.inl.inj (Sum.inl.inj h))
        have ha : (Sum.inl (Sum.inl k) : Stack)≠.inl P.assignment := by
          intro h
          have h' : (Sum.inl k : P.Stack)=.inr SemiprimeD1StackProductCheck.rawInput := Sum.inl.inj h
          cases h'
        rw [checkerReady,Function.update_of_ne ho,rawReady,Function.update_of_ne ha]
        simp only [data,hk,ite_false]
    · change checkerReady bits front reversed (.inl (.inr k))=SemiprimeD1StackProductCheck.input front.reverse [] k
      by_cases hk : k=SemiprimeD1StackProductCheck.rawInput
      · subst k;rfl
      · have he : (.inr k : P.Stack)≠P.assignment := by
          change Sum.inr k≠Sum.inr SemiprimeD1StackProductCheck.rawInput
          exact fun h=>hk (Sum.inr.inj h)
        have ho : (Sum.inl (Sum.inr k) : Stack)≠.inl P.original := by
          intro h
          have h' : (Sum.inr k : P.Stack)=.inl (SemiprimeD1BinaryPublicAcquisition.digitStack
            (SemiprimeD1BinaryPublicAcquisition.Digits.metaStack .input)) := Sum.inl.inj h
          cases h'
        have ha : (Sum.inl (Sum.inr k) : Stack)≠.inl P.assignment := fun h=>he (Sum.inl.inj h)
        rw [checkerReady,Function.update_of_ne ho,rawReady,Function.update_of_ne ha]
        simp only [data,SemiprimeD1StackProductCheck.input,hk,ite_false,ite_self]
  | inr k=>cases k <;> rfl
/-- Full cleanup preserves exactly the private DFS data and clears all checker
cells, including fields the original checker deliberately retains. -/
theorem clean_checked (bits front reversed : List Bool) :
    clean (checked bits front reversed)=data bits 0 front reversed := by
  funext k;cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackProductTableState
