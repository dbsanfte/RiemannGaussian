/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
import RiemannGaussian.SemiprimeD1StackUnaryProduct
/-! # Literal physical multiply-plus-offset for original endpoint slot routing
This is an INTERNAL concrete procedure over acquired unary coordinate words.
It REAL-calls the immutable Copy and Product code; it has no numeric product,
slot, output word, evaluator callback or cost answer as an operand.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 8192
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPortOwnerMadd
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace B
export SemiprimeD1StackBytecode (Instruction State execute step run)
end B
namespace P
export SemiprimeD1StackUnaryProduct (Stack Label code entry)
end P
namespace Link
export SemiprimeD1StackMultiplierLink (instruction DataRel)
end Link
/-- Actual readonly coordinate/axis/bit words. -/
inductive Source where | a | b | c deriving DecidableEq
instance : Fintype Source := Fintype.ofList [.a,.b,.c] (by intro k;cases k <;> simp)
/-- Actual work, including preserved-copy scratch and final unary slot. -/
inductive Aux where | multiplier | productScratch | copyScratch | output deriving DecidableEq
instance : Fintype Aux := Fintype.ofList [.multiplier,.productScratch,.copyScratch,.output]
  (by intro k;cases k <;> simp)
/-- Seven fixed Boolean data roles. -/
abbrev Stack := Source ⊕ Aux
/-- Actual source-preserving copy: first a, then c into the actual product output. -/
def copyStack (offset:Bool) (k:Fin 3) : Stack :=
  if k=0 then (if offset then .inl .c else .inl .a)
  else if k=1 then (if offset then .inr .output else .inr .multiplier) else .inr .copyScratch
/-- Actual immutable product inclusion; b is the readonly multiplicand. -/
def productStack : P.Stack→Stack
  | .multiplier => .inr .multiplier
  | .multiplicand => .inl .b
  | .scratch => .inr .productScratch
  | .product => .inr .output
/-- Three literal stages and the final actual halt. -/
inductive Control where | start | product | offset | halt deriving DecidableEq
instance : Fintype Control := Fintype.ofList [.start,.product,.offset,.halt]
  (by intro k;cases k <;> simp)
/-- Every control/return tag is static; Product requires only Fintype. -/
abbrev Label := Control ⊕ ((Bool×Fin 9) ⊕ P.Label)
/-- Literal real Copy/Product/Copy control, independent of all original dimensions. -/
def program : Label→C.Instruction Stack Label
  | .inr (.inl (offset,pc)) => Link.instruction (copyStack offset) (fun p=>.inr (.inl (offset,p))) (SemiprimeD1StackCopy.code pc)
  | .inr (.inr pc) => Link.instruction productStack (fun p=>.inr (.inr p)) (P.code pc)
  | .inl .start => .call (.inr (.inl (false,0))) (.inl .product)
  | .inl .product => .call (.inr (.inr P.entry)) (.inl .offset)
  | .inl .offset => .call (.inr (.inl (true,0))) (.inl .halt)
  | .inl .halt => .base .halt
/-- Literal physical data-store view; no numeric computation is executed here. -/
def data (a b c m s scratch out:List Bool) : Stack→List Bool :=
  Sum.elim (fun k=>match k with | .a=>a | .b=>b | .c=>c)
    (fun k=>match k with | .multiplier=>m | .productScratch=>s | .copyScratch=>scratch | .output=>out)
/-- All real Copy operands are distinct. -/
theorem copyStack_injective (offset:Bool) : Function.Injective (copyStack offset) := by cases offset <;> decide
/-- All actual product operands are distinct, with source b retained. -/
theorem productStack_injective : Function.Injective productStack := by decide
/-- One fixed finite internal machine; the parent supplies ONLY physically acquired words. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine (.inl .a) (.inr .output) (.inl .start) program
/-- Every stack alphabet is finite, with no number/list hidden in a control symbol. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite (.inl .a) (.inr .output) (.inl .start) program
end RiemannGaussian.SemiprimeD1StackPortOwnerMadd
