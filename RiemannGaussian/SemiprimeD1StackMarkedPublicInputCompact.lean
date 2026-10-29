/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedPublicInputOriginal
import RiemannGaussian.SemiprimeD1StackReduceExecution
import RiemannGaussian.SemiprimeD1StackReverseWord
/-! # Actual compact coefficient wrapper around the frozen marked input source
All66 physical roles are reused. Only after the real source halts is its empty
template shadow used for reverse/trim; it is empty again at the wrapper halt.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 262144
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackMarkedPublicInputCompact
namespace M
export SemiprimeD1StackMarkedPublicInput (Stack Label program initial checker word aux)
end M
namespace C
export SemiprimeD1StackCalls (Instruction State run)
end C
/-- The actual marked source's fixed66-role bank, with no extra allocation. -/
abbrev Stack := M.Stack
/-- Complete finite wrapper stages. -/
inductive Control where | start | reverse | trim | done deriving DecidableEq, Repr
/-- Literal complete stage inventory. -/
instance : Fintype Control := Fintype.ofList [.start,.reverse,.trim,.done] (by intro k;cases k <;> simp)
/-- Actual source labels, finite reverse labels and finite trim labels. -/
abbrev Label := Control ⊕ (M.Label ⊕ (Fin 4 ⊕ SemiprimeD1StackReduce.Label))
/-- Fixed local stage. -/
def ctl : Control → Label := Sum.inl
/-- Fixed source-label inclusion. -/
def sourceLabel : M.Label → Label := fun k => .inr (.inl k)
/-- Fixed consuming-reverse inclusion. -/
def reverseLabel : Fin 4 → Label := fun k => .inr (.inr (.inl k))
/-- Fixed high-zero-trim inclusion. -/
def trimLabel : SemiprimeD1StackReduce.Label → Label := fun k => .inr (.inr (.inr k))
/-- Reversal borrows only an actually empty unused shadow after source completion. -/
def reverseStack (k : Fin 2) : Stack := if k=0 then M.aux .output else M.word 1
/-- All four trim roles are distinct and actually empty except the reversed word. -/
def trimStack : SemiprimeD1StackAdder.Stack → Stack
  | .left => M.word 0
  | .right => M.word 3
  | .scratch => M.word 1
  | .output => M.aux .output
/-- Parameterless literal source→paidreverse→paidtrim→halt. -/
def program : Label → C.Instruction Stack Label
  | .inl .start => .call (sourceLabel (SemiprimeD1StackMarkedPublicInput.ctl .start)) (ctl .reverse)
  | .inl .reverse => .call (reverseLabel 0) (ctl .trim)
  | .inl .trim => .call (trimLabel .trim) (ctl .done)
  | .inl .done => .base .halt
  | .inr (.inl k) => SemiprimeD1StackValidationLink.instruction id sourceLabel (M.program k)
  | .inr (.inr (.inl k)) => SemiprimeD1StackMultiplierLink.instruction reverseStack reverseLabel (SemiprimeD1StackReverseWord.code k)
  | .inr (.inr (.inr k)) => SemiprimeD1StackMultiplierLink.instruction trimStack trimLabel (SemiprimeD1StackReduce.code k)
/-- Exactly the same four original physical words as the immutable marked source. -/
def initial (bits raw indexWord : List Bool) (side : Bool) : C.State Stack Label :=
  ⟨some (ctl .start),none,none,(M.initial bits raw indexWord [side]).data,[]⟩
/-- Compact actual output specification; no word is supplied to runtime. -/
def coefficient (bits raw indexWord : List Bool) (side : Bool) : List Bool :=
  SemiprimeD1StackReduceExecution.trimReverse
    (SemiprimeD1StackMarkedPublicInputEncoding.coefficient bits raw indexWord side).reverse
/-- The exact retained66-role bank changes only the actual coefficient output. -/
def result (bits raw indexWord : List Bool) (side : Bool) : Stack → List Bool :=
  Function.update (SemiprimeD1StackMarkedPublicInputEncoding.result bits raw indexWord side)
    (M.aux .output) (coefficient bits raw indexWord side)
/-- Actual compact wrapper halt. -/
def done (bits raw indexWord : List Bool) (side : Bool) : C.State Stack Label :=
  ⟨none,none,none,result bits raw indexWord side,[]⟩
/-- Real reverse operands are distinct. -/
theorem reverse_injective : Function.Injective reverseStack := by decide
/-- Real trim operands do not alias any two physical roles. -/
theorem trim_injective : Function.Injective trimStack := by decide
/-- Genuine fixed finite bit machine. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine
  (M.checker (.inl SemiprimeD1StackPublicInputWidth.original)) (M.aux .output) (ctl .start) program
/-- Every original data role, including the temporarily borrowed shadow, is counted. -/
theorem stack_card : Fintype.card Stack=66 := SemiprimeD1StackMarkedPublicInput.stack_card
end RiemannGaussian.SemiprimeD1StackMarkedPublicInputCompact

