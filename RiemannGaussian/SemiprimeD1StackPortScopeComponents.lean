/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortScopeRecords
/-! # Literal disjoint component maps of the physical port/ID stream join -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPortScopeComponents
open SemiprimeD1StackPortScopeRecords
/-- Every original data/cache role is retained literally. -/
theorem sourceStack_injective : Function.Injective sourceStack := Sum.inl_injective
/-- Actual copy source, destination and scratch are pairwise distinct. -/
theorem copyStack_injective (ids:Bool) : Function.Injective (copyStack ids) := by cases ids <;> decide
/-- Actual physical input reader of the selected static field parser. -/
def fieldInput (part:Fin 9) : Stack := if part.val=8 then aux .readerIds else aux .readerPorts
/-- The real reader and the selected cache do not alias. -/
theorem fieldInput_cache (part:Fin 9) : fieldInput part≠cache part := by
  unfold fieldInput
  split <;> simp [aux,cache]
/-- Parsing validity is a separate Boolean cell. -/
theorem fieldInput_valid (part:Fin 9) : fieldInput part≠aux .valid := by
  unfold fieldInput
  split <;> simp [aux]
/-- Parser scratch is not either input reader. -/
theorem fieldScratch_input (part:Fin 9) : aux .fieldScratch≠fieldInput part := by
  unfold fieldInput
  split <;> simp [aux]
/-- All four field-parser roles remain physically distinct. -/
theorem fieldStack_injective (part:Fin 9) : Function.Injective (fieldStack part) := by
  intro a b h
  rcases a with a|a <;> rcases b with b|b
  · cases a <;> cases b <;> by_cases hp:part.val=8 <;> simp_all [fieldStack,aux,cache]
  · cases a <;> cases b <;> by_cases hp:part.val=8 <;> simp_all [fieldStack,aux,cache]
  · cases a;cases b <;> by_cases hp:part.val=8 <;> simp_all [fieldStack,aux,cache]
  · cases a;cases b;rfl
/-- All sources are cached fields, separate from physical framing output. -/
theorem frameSource_buffer (part:Fin 9) : frameSource part≠aux .frameBuffer := by
  unfold frameSource
  split <;> simp [aux,cache]
/-- Physical framing scratch is never a source word. -/
theorem frameSource_scratch (part:Fin 9) : frameSource part≠aux .frameScratch := by
  unfold frameSource
  split <;> simp [aux,cache]
/-- All real framing operands are distinct. -/
theorem frameStack_injective (part:Fin 9) : Function.Injective (frameStack part) := by
  have h0:=frameSource_buffer part
  have h1:=frameSource_scratch part
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [frameStack,aux]
/-- Actual frame/final reverse operands are distinct in each fixed mode. -/
theorem reverseStack_injective (finish:Bool) : Function.Injective (reverseStack finish) := by cases finish <;> decide
end RiemannGaussian.SemiprimeD1StackPortScopeComponents
