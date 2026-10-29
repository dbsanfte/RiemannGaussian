/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BooleanTreeStreamOriginal
import RiemannGaussian.SemiprimeD1StackPublicZeroOriginal
import RiemannGaussian.SemiprimeD1StackProcedureInclusion
/-! # Actual N-only whole zero-boundary tensor acquisition
Public acquisition runs once. ONE literal true bit seeds the actual tree writer;
EOF supplies all other false entries. The physical modulus word is shared as
depth markers and restored EXACTLY by the real recursive writer. No arity,
entry stream, table, evaluator, predicate, width or clock answer is input.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 8192
namespace RiemannGaussian.SemiprimeD1StackZeroBoundaryTable
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace P
export SemiprimeD1BinaryPublicAcquisition (Stack Label program input initial mainLabel digitStack fermatStack)
end P
namespace T
export SemiprimeD1StackBooleanTree (Stack Label program initial store)
end T
/-- Thirty-two fixed Boolean roles, including one unused private depth shadow. -/
abbrev Stack := P.Stack⊕T.Stack
/-- Actual original public input role. -/
def original : Stack := .inl (P.digitStack (SemiprimeD1BinaryPublicAcquisition.Digits.metaStack .input))
/-- The ACTUALLY acquired binary modulus word; its length is carry arity R+1. -/
def depthKey : P.Stack := P.fermatStack (.inr false)
/-- Tree depth directly shares that physical word. Every marker bit is restored. -/
def treeStack : T.Stack→Stack
  | .depth=>.inl depthKey
  | k=>.inr k
/-- Actual emitted whole tagged tree, not an entry or encoded answer input. -/
def output : Stack := treeStack .output
/-- Literal finite pipeline control plus the actual component labels. -/
inductive Control where | start | seed | write | done
  deriving DecidableEq
instance : Fintype Control := Fintype.ofList [.start,.seed,.write,.done] (by intro k;cases k <;> simp)
/-- All labels and the program are fixed before N. -/
abbrev Label := Control⊕(P.Label⊕T.Label)
/-- Literal public source inclusion. -/
def publicLabel (pc : P.Label) : Label := .inr (.inl pc)
/-- Literal real recursive tree inclusion. -/
def treeLabel (pc : T.Label) : Label := .inr (.inr pc)
/-- One fixed N-only program; one source call, ONE true push, one tree call. -/
def program : Label→C.Instruction Stack Label
  | .inl .start=>.call (publicLabel (P.mainLabel .start)) (.inl .seed)
  | .inl .seed=>.base (.push (treeStack .input) true (.inl .write))
  | .inl .write=>.call (treeLabel .start) (.inl .done)
  | .inl .done=>.base .halt
  | .inr (.inl pc)=>SemiprimeD1StackValidationLink.instruction Sum.inl publicLabel (P.program pc)
  | .inr (.inr pc)=>SemiprimeD1StackValidationLink.instruction treeStack treeLabel (T.program pc)
/-- Public cache view after the actual source call; proof-side only. -/
def context (bits : List Bool) : P.Stack→List Bool := SemiprimeD1BinaryPublicAcquisitionComponents.result bits
/-- Actual depth bytes, NOT a count/cardinality/template input. -/
def cached (bits : List Bool) : List Bool := context bits depthKey
/-- Complete caller payload; unused private depth and all writer history are empty. -/
def store (p : P.Stack→List Bool) (input bytes : List Bool) : Stack→List Bool :=
  Sum.elim p (T.store input [] [] bytes)
/-- Original N ONLY, before every source/table operation. -/
def initial (bits : List Bool) : C.State Stack Label :=
  ⟨some (.inl .start),none,none,store (P.input bits) [] [],[]⟩
/-- The actual public metadata survive, while the acquired tree occupies output. -/
def done (bits : List Bool) : C.State Stack Label :=
  ⟨none,none,none,store (context bits) []
    (SemiprimeD1BooleanTreeStream.bytes (cached bits).length [true]),[]⟩
/-- Fixed finite machine, original N as the only initially supplied data. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine original output (.inl .start) program
/-- Real source and depth/output roles do not alias each other. -/
theorem tree_injective : Function.Injective treeStack := by decide
/-- Actual stack inventory includes every metadata/private shadow role. -/
theorem stack_card : Fintype.card Stack=32 := by decide
/-- Exact actual public marker word equals the frozen acquired carry width word. -/
theorem cached_eq (bits : List Bool) : cached bits=SemiprimeD1StackPublicZeroExecution.cached bits := rfl
end RiemannGaussian.SemiprimeD1StackZeroBoundaryTable
