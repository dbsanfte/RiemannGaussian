/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetMulBounds
import RiemannGaussian.SemiprimeD1StackUnaryCounterExecution
/-! # Physical jet context-cache acquisition
The original encoded positive unary axes are preserved while the actual suffix
producer computes rank. Binary precision is preserved while the actual unary
counter acquires precision markers. Generated suffix records are physically
cleared, not silently projected away. No rank/precision-count answer is supplied.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 8192
set_option maxRecDepth 8192
namespace RiemannGaussian.SemiprimeD1StackJetContext
namespace C
export SemiprimeD1StackCalls (Instruction State run)
end C
namespace S
export SemiprimeD1StackJetSuffix (Stack Label code control data)
end S
namespace U
export SemiprimeD1StackUnaryCounter (Label code state)
end U

/-- Eight suffix registers, four precision-decoder registers and three fixed caches. -/
abbrev Stack := S.Stack ⊕ (SemiprimeD1StackAdder.Stack ⊕ Fin 3)
/-- Retained original axis-vector tape. -/
def axesCache : Stack := .inr (.inr 0)
/-- Retained original binary precision word. -/
def precisionBits : Stack := .inr (.inr 1)
/-- Cleared copy work. -/
def copyWork : Stack := .inr (.inr 2)
/-- Physically acquired unary rank; no extra rank cache copy is needed. -/
def rankCache : Stack := .inl .radix
/-- Physically acquired unary precision markers. -/
def widthCache : Stack := .inr (.inl .output)
/-- Literal precision decoder inclusion. -/
def unaryStack (k : SemiprimeD1StackAdder.Stack) : Stack := .inr (.inl k)
/-- Two actual source copies preserve both original context inputs. -/
def copyStack (precision : Bool) (k : Fin 3) : Stack :=
  if k=0 then (if precision then precisionBits else axesCache)
  else if k=1 then (if precision then unaryStack .left else .inl .axes) else copyWork

/-- Fixed finite caller/component labels, before all context values. -/
inductive Label where
  | start | callSuffix | suffixDone | clearRecords | copyPrecision | callUnary | done | reject
  | copy (precision : Bool) (pc : Fin 9)
  | suffix (pc : S.Label)
  | unary (pc : U.Label)
  deriving DecidableEq,Fintype

/-- Actual context supplier: no native rank, big-integer precision decoding or
record-discard operation occurs in the executed instruction table. -/
def program : Label → C.Instruction Stack Label
  | .start => .call (.copy false 0) .callSuffix
  | .callSuffix => .call (.suffix (S.control .vector)) .suffixDone
  | .suffixDone => .base (.pop (.inl .valid) .reject .reject .clearRecords)
  | .clearRecords => .base (.pop (.inl .records) .copyPrecision .clearRecords .clearRecords)
  | .copyPrecision => .call (.copy true 0) .callUnary
  | .callUnary => .call (.unary .reverse) .done
  | .done | .reject => .base .halt
  | .copy precision pc => SemiprimeD1StackMultiplierLink.instruction (copyStack precision) (Label.copy precision)
      (SemiprimeD1StackCopy.code pc)
  | .suffix pc => SemiprimeD1StackValidationLink.instruction Sum.inl Label.suffix (S.code pc)
  | .unary pc => SemiprimeD1StackMultiplierLink.instruction unaryStack Label.unary (U.code pc)

/-- Literal retained original input tapes and empty copy workspace. -/
def cached (axes precision : List Bool) (k : Fin 3) : List Bool :=
  if k=0 then axes else if k=1 then precision else []
/-- Declarative component-state bank; its functions are refinement invariants,
not callbacks accepted by the executed supplier. -/
def bank (axes precision : List Bool) (suffix : S.Stack → List Bool)
    (unary : SemiprimeD1StackAdder.Stack → List Bool) : Stack → List Bool :=
  Sum.elim suffix (Sum.elim unary (cached axes precision))
/-- Actual entry takes only encoded original axes and binary precision. -/
def initial (axes precision : List Bool) : C.State Stack Label :=
  ⟨some .start,none,none,bank axes precision (fun _=>[]) (fun _=>[]),[]⟩
/-- Actual fixed finite-stack context-cache machine. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine axesCache rankCache Label.start program

/-- Both original-source copy inclusions have distinct data registers. -/
theorem copyStack_injective (precision : Bool) : Function.Injective (copyStack precision) := by
  cases precision <;> decide
/-- Unary precision decoding uses distinct actual registers. -/
theorem unaryStack_injective : Function.Injective unaryStack := by
  intro a b h
  simpa only [unaryStack,Sum.inr.injEq,Sum.inl.injEq] using h

end RiemannGaussian.SemiprimeD1StackJetContext
