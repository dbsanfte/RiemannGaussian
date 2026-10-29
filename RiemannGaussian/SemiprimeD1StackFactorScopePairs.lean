/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortScopeBounds
import RiemannGaussian.SemiprimeD1StackOwnerFibreBounds
/-! # Original-N factor-key/scope-ID pair acquisition
One real original-N source call acquires the nine-field scoped-port stream.
The preserving reader copy parses every field, frames factor slot2 and scope
slot0, clears all nine cached payloads physically, and finally reverses once.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackFactorScopePairs
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace S
export SemiprimeD1StackPortScopeRecords (Stack Label program input initial originalInput)
end S
namespace F
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end F
/-- Eight fixed reader/framing/output work roles. -/
inductive Aux where
  | reader | copyScratch | fieldScratch | valid | frameBuffer | frameScratch | reversed | output
  deriving DecidableEq
instance : Fintype Aux := Fintype.ofList
  [.reader,.copyScratch,.fieldScratch,.valid,.frameBuffer,.frameScratch,.reversed,.output]
  (by intro k;cases k <;> simp)
/-- All122 physical Boolean roles, including all retained source caches. -/
abbrev Stack := S.Stack⊕(Fin 9⊕Aux)
/-- Complete included original-N source inventory. -/
def sourceStack : S.Stack→Stack := Sum.inl
/-- One actual parsed-field cache. -/
def cache (part : Fin 9) : Stack := .inr (.inl part)
/-- One private physical work role. -/
def aux (role : Aux) : Stack := .inr (.inr role)
/-- Original binary N is the only initial input. -/
def originalInput : Stack := sourceStack S.originalInput
/-- Physically acquired and retained nine-field port stream. -/
def sourceOutput : Stack := sourceStack (SemiprimeD1StackPortScopeRecords.aux .output)
/-- Real preserving source-to-reader copy, with its own scratch. -/
def copyStack (k : Fin 3) : Stack :=
  if k=0 then sourceOutput else if k=1 then aux .reader else aux .copyScratch
/-- Every one of nine actual framed input fields uses this parser. -/
def fieldStack (part : Fin 9) : F.Stack→Stack
  | .inl .input => aux .reader
  | .inl .scratch => aux .fieldScratch
  | .inl .output => cache part
  | .inr _ => aux .valid
/-- Key first, then scope: original factor ordinal is cache2, scope ID cache0. -/
def frameSource (scope : Bool) : Stack := cache (if scope then 0 else 2)
/-- Literal preserving Frame operands. -/
def frameStack (scope : Bool) (k : Fin 3) : Stack :=
  if k=0 then frameSource scope else if k=1 then aux .frameBuffer else aux .frameScratch
/-- Per-field and final real reversal operands. -/
def reverseStack (finish : Bool) (k : Fin 2) : Stack :=
  if k=0 then (if finish then aux .reversed else aux .frameBuffer)
  else if finish then aux .output else aux .reversed
/-- Fixed field loops and actual EOF termination, independent of N or row count. -/
inductive Control where
  | main | copy | loop | field (part : Fin 9) | valid (part : Fin 9)
  | tag | frame (scope : Bool) | reverse (scope : Bool) | clear (part : Fin 9)
  | finish | finalReverse | done | abort
  deriving DecidableEq, Fintype
/-- Actual included procedures and finite caller labels. -/
inductive Label where
  | local (pc : Control) | source (pc : S.Label) | copy (pc : Fin 9)
  | field (part : Fin 9) (pc : F.Label) | frame (scope : Bool) (pc : Fin 11)
  | reverse (finish : Bool) (pc : Fin 4)
  deriving Fintype
/-- Next fixed input field, followed by emission of the two-field row. -/
def nextField (part : Fin 9) : Label :=
  if h : part.val<8 then .local (.field ⟨part.val+1,by omega⟩) else .local .tag
/-- Next fixed payload erasure, then the physical EOF loop. -/
def nextClear (part : Fin 9) : Label :=
  if h : part.val<8 then .local (.clear ⟨part.val+1,by omega⟩) else .local .loop
/-- The whole literal source/copy/parse/frame/erase/reverse program. -/
def program : Label→C.Instruction Stack Label
  | .local .main => .call (.source (.local .main)) (.local .copy)
  | .local .copy => .call (.copy 0) (.local .loop)
  | .local .loop => .base (.peek (aux .reader) (.local .finish) (.local (.field 0)) (.local (.field 0)))
  | .local (.field part) => .call (.field part (F.active .tagPop (none,false))) (.local (.valid part))
  | .local (.valid part) => .base (.pop (aux .valid) (.local .abort) (.local .abort) (nextField part))
  | .local .tag => .base (.push (aux .reversed) true (.local (.frame false)))
  | .local (.frame scope) => .call (.frame scope 0) (.local (.reverse scope))
  | .local (.reverse scope) => .call (.reverse false 0)
      (if scope then .local (.clear 0) else .local (.frame true))
  | .local (.clear part) => .base (.pop (cache part) (nextClear part) (.local (.clear part)) (.local (.clear part)))
  | .local .finish => .base (.push (aux .reversed) false (.local .finalReverse))
  | .local .finalReverse => .call (.reverse true 0) (.local .done)
  | .local .done | .local .abort => .base .halt
  | .source pc => SemiprimeD1StackValidationLink.instruction sourceStack Label.source (S.program pc)
  | .copy pc => SemiprimeD1StackMultiplierLink.instruction copyStack Label.copy (SemiprimeD1StackCopy.code pc)
  | .field part pc => SemiprimeD1StackMultiplierLink.instruction (fieldStack part) (Label.field part) (F.code pc)
  | .frame scope pc => SemiprimeD1StackMultiplierLink.instruction (frameStack scope) (Label.frame scope) (SemiprimeD1StackFrame.code pc)
  | .reverse finish pc => SemiprimeD1StackMultiplierLink.instruction (reverseStack finish) (Label.reverse finish) (SemiprimeD1StackReverseWord.code pc)
/-- N-only store, with every projection cache and workspace empty. -/
def input (bits : List Bool) : Stack→List Bool := Sum.elim (S.input bits) (fun _=>[])
/-- Literal original-N source entry. -/
def initial (bits : List Bool) : C.State Stack Label := ⟨some (.local .main),none,none,input bits,[]⟩
/-- One fixed finite-alphabet machine before every original N. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine originalInput (aux .output) (.local .main) program
/-- Complete fixed physical register inventory. -/
theorem stack_card : Fintype.card Stack=122 := by decide
/-- All fields use disjoint reader/cache/scratch/validity registers. -/
theorem field_injective (part : Fin 9) : Function.Injective (fieldStack part) := by fin_cases part <;> decide
/-- Both real Frame procedures use distinct operands. -/
theorem frame_injective (scope : Bool) : Function.Injective (frameStack scope) := by cases scope <;> decide
/-- Both real reversal operand pairs are disjoint. -/
theorem reverse_injective (finish : Bool) : Function.Injective (reverseStack finish) := by cases finish <;> decide
/-- Actual source-preserving copy operands are disjoint. -/
theorem copy_injective : Function.Injective copyStack := by decide
end RiemannGaussian.SemiprimeD1StackFactorScopePairs
