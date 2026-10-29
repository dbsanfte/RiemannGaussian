/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BinaryPublicAcquisitionBounds
import RiemannGaussian.SemiprimeD1StackWordBlockBounds
import RiemannGaussian.SemiprimeD1StackWordEqualBounds

/-! # Original-input zero-word public checker
Original public preprocessing acquires the true word width from binary N.
An actual preserving copy and WordBlock obtain the raw assignment word; the
real numeric comparator consumes it against empty zero. No modulus/width,
parsed word, zero/nonzero bit or elapsed answer is initial input.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPublicZero
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace P
export SemiprimeD1BinaryPublicAcquisition (Stack Label program input initial digitStack fermatStack)
end P
namespace B
export SemiprimeD1StackWordBlock (Stack Label program initial)
end B
namespace E
export SemiprimeD1StackAdder (Stack)
export SemiprimeD1StackWordEqual (Label code)
end E
/-- All38 physical Boolean roles, including every unused private shadow. -/
abbrev Stack := P.Stack⊕(B.Stack⊕(E.Stack⊕Unit))
/-- Actual acquired binary modulus gives the exact original word-width template. -/
def modulusKey : P.Stack := P.fermatStack (.inr false)
/-- The assignment is actual raw bits, retained by a real preserving copy. -/
def assignment : Stack := .inr (.inr (.inr ()))
/-- Public word-block cache shares actual acquired modulus bytes directly. -/
def blockStack (k : B.Stack) : Stack := if k=1 then .inl modulusKey else .inr (.inl k)
/-- Private comparison output/right roles; left/scratch shadows remain counted. -/
def equalPrivate (k : E.Stack) : Stack := .inr (.inr (.inl k))
/-- The acquired word directly feeds the real numeric comparator. -/
def equalStack : E.Stack→Stack
  | .left=>blockStack 4
  | .scratch=>blockStack 3
  | k=>equalPrivate k
/-- Copy and parser share actual empty restoration scratch. -/
def copyStack (k : Fin 3) : Stack := if k=0 then assignment else if k=1 then blockStack 0 else blockStack 3
/-- Real singleton zero-word verdict, not a predicate opcode. -/
def output : Stack := equalPrivate .output
/-- Original binary N input designation. -/
def original : Stack := .inl (P.digitStack (SemiprimeD1BinaryPublicAcquisition.Digits.metaStack .input))
/-- Fixed finite pipeline/component labels before all source inputs. -/
inductive Label where
  | start | copyRaw | block | compare | done
  | acquire (pc : P.Label) | copy (pc : Fin 9) | extract (pc : B.Label) | equality (pc : E.Label)
  deriving Fintype
/-- ONE literal source program, with every public/preparation/checking step. -/
def program : Label→C.Instruction Stack Label
  | .start=>.call (.acquire (SemiprimeD1BinaryPublicAcquisition.mainLabel .start)) .copyRaw
  | .copyRaw=>.call (.copy 0) .block
  | .block=>.call (.extract .start) .compare
  | .compare=>.call (.equality .loop) .done
  | .done=>.base .halt
  | .acquire pc=>SemiprimeD1StackValidationLink.instruction Sum.inl Label.acquire (P.program pc)
  | .copy pc=>SemiprimeD1StackMultiplierLink.instruction copyStack Label.copy (SemiprimeD1StackCopy.code pc)
  | .extract pc=>SemiprimeD1StackValidationLink.instruction blockStack Label.extract (B.program pc)
  | .equality pc=>SemiprimeD1StackMultiplierLink.instruction equalStack Label.equality (E.code pc)
/-- Physical reached-state view, not an executing word/result supplier. -/
def store (preprocess : P.Stack→List Bool) (raw reader word out : List Bool) : Stack→List Bool :=
  Sum.elim preprocess (Sum.elim (fun k=>if k=0 then reader else if k=4 then word else [])
    (Sum.elim (fun k=>if k=.output then out else []) (fun _=>raw)))
/-- Only original binary N and the actual raw assignment are initially present. -/
def initial (bits raw : List Bool) : C.State Stack Label := ⟨some .start,none,none,store (P.input bits) raw [] [] [],[]⟩
/-- Every actual WordBlock register stays distinct under public modulus sharing. -/
theorem block_injective : Function.Injective blockStack := by decide
/-- All actual comparator registers stay distinct under direct word sharing. -/
theorem equal_injective : Function.Injective equalStack := by decide
/-- All real preserving-copy registers are physically distinct. -/
theorem copy_injective : Function.Injective copyStack := by decide
/-- Genuine fixed finite machine; assignment generation remains table-caller work. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine original output .start program
/-- All data/return alphabets are fixed and finite before all binary inputs. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) := SemiprimeD1StackCalls.all_alphabets_finite original output Label.start program
/-- No unbounded width, word, predicate or elapsed counter occurs in control. -/
theorem control_finite : Finite machine.σ := SemiprimeD1StackCalls.control_finite original output Label.start program
/-- Complete physical data inventory, with all duplicate shadows retained. -/
theorem stack_card : Fintype.card Stack=38 := by decide
end RiemannGaussian.SemiprimeD1StackPublicZero
