/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTransformGuards
/-! # Actual loop cache invariants, with physical frequency/remaining counters
Every Nat below indexes a correctness specification of unary stack data; no Nat,
word-list, source AST or callback is a register or executing loop argument.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformLoopState
open SemiprimeD1StackPublicTransform SemiprimeD1StackPublicTransformState
open SemiprimeD1StackPublicTransformWords SemiprimeD1StackPublicTransformGuards
open SemiprimeD1StackPublicTransformMetadata
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Actual retained dot arguments, populated by original acquisition/copies.
Frequency here is a proof-side unary counter specification, not native control. -/
def queryCache (bits raw : List Bool) (second inverse : Bool) (frequency : ℕ) : SemiprimeD1StackExprDot.Cache :=
  ⟨baseCode bits inverse,stride bits second,unary frequency,count bits second,
    vectorBits (inputs (rootData bits) raw second)⟩
/-- Actual reached accepted-frontend cache image, before output iteration. -/
def baseParts (bits raw : List Bool) (second inverse : Bool) : Parts := loopReady (rootData bits) raw second inverse
/-- Literal remaining/frequency counter values in an otherwise retained cache.
Only a proof view; the executed loop manipulates these markers by pop/copy. -/
def steady (bits raw : List Bool) (second inverse : Bool) (remaining frequency : ℕ) : Parts :=
  set (set (baseParts bits raw second inverse) (.dot (.inl .frequency)) (unary frequency)) (.aux .remaining) (unary remaining)
/-- Exact two physical updates defining the loop-state image. -/
theorem steady_data (bits raw : List Bool) (second inverse : Bool) (remaining frequency : ℕ) :
    data (steady bits raw second inverse remaining frequency)=
      Function.update (Function.update (data (baseParts bits raw second inverse)) (.dot (.inl .frequency)) (unary frequency))
        (.aux .remaining) (unary remaining) := by rw [steady,data_set,data_set]
/-- Actual output counter is exactly its physically acquired/copied unary cache. -/
theorem remaining_value (bits raw : List Bool) (second inverse : Bool) (remaining frequency : ℕ) :
    data (steady bits raw second inverse remaining frequency) (.aux .remaining)=unary remaining := by
  rw [steady_data,Function.update_same]
/-- Actual frequency markers are physically stored, not a native index getter. -/
theorem frequency_value (bits raw : List Bool) (second inverse : Bool) (remaining frequency : ℕ) :
    data (steady bits raw second inverse remaining frequency) (.dot (.inl .frequency))=unary frequency := by
  rw [steady_data,Function.update_of_ne (by decide : Stack.dot (.inl .frequency)≠.aux .remaining),Function.update_same]
/-- Replacing an actual remaining counter preserves all cache/source bytes. -/
theorem remaining_update (bits raw : List Bool) (second inverse : Bool) (remaining frequency next : ℕ) :
    Function.update (data (steady bits raw second inverse remaining frequency)) (.aux .remaining) (unary next)=
      data (steady bits raw second inverse next frequency) := by
  rw [steady_data,Function.update_idem,steady_data]
/-- Replacing actual frequency markers preserves every other physical role. -/
theorem frequency_update (bits raw : List Bool) (second inverse : Bool) (remaining frequency next : ℕ) :
    Function.update (data (steady bits raw second inverse remaining frequency)) (.dot (.inl .frequency)) (unary next)=
      data (steady bits raw second inverse remaining next) := by
  rw [steady_data,steady_data]
  rw [Function.update_comm (by decide : Stack.aux .remaining≠.dot (.inl .frequency)),Function.update_idem]
/-- The ACTUAL ready frontend is exactly the initial loop image with acquired n
and zero frequency, without a supplied count/stride answer. -/
theorem loop_initial (bits raw : List Bool) (second inverse : Bool) :
    data (steady bits raw second inverse (size bits second) 0)=data (baseParts bits raw second inverse) := by
  rw [steady_data]
  have hf : data (baseParts bits raw second inverse) (.dot (.inl .frequency))=[] := rfl
  have hr : data (baseParts bits raw second inverse) (.aux .remaining)=unary (size bits second) := count_unary bits second
  change Function.update (Function.update (data (baseParts bits raw second inverse)) (.dot (.inl .frequency)) [])
    (.aux .remaining) (unary (size bits second))=_
  rw [←hf,Function.update_eq_self,←hr,Function.update_eq_self]
/-- Actual dot input/cache/modulus state at each physical frequency. -/
theorem steady_dot (bits raw : List Bool) (second inverse : Bool) (remaining frequency : ℕ) :
    (steady bits raw second inverse remaining frequency).dot=
      (D.initial (queryCache bits raw second inverse frequency) (cached bits) []).data := by
  funext k;rcases k with k|k <;> cases k <;> rfl
/-- Actual multiplier remains fresh between queries with acquired M preserved. -/
theorem steady_multiply (bits raw : List Bool) (second inverse : Bool) (remaining frequency : ℕ) :
    (steady bits raw second inverse remaining frequency).multiplication=(M.initial [] [] (cached bits)).data := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> rfl
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
/-- Output reader cache contains the actual produced vector, all query/work empty. -/
theorem steady_reader (bits raw : List Bool) (second inverse : Bool) (remaining frequency : ℕ) :
    (steady bits raw second inverse remaining frequency).reader=
      SemiprimeD1StackJetRead.store (vectorBits (outputs (rootData bits) raw second)) [] [] [] [] [] [] [] := by
  funext k;cases k <;> rfl
/-- Streaming equality has no stale operand or returned truth between queries. -/
theorem steady_equal (bits raw : List Bool) (second inverse : Bool) (remaining frequency : ℕ) :
    (steady bits raw second inverse remaining frequency).equality=SemiprimeD1StackAdder.store [] [] [] [] := by
  funext k;cases k <;> rfl
/-- The original normalizer copy is retained at every actual loop state. -/
theorem steady_normalizer (bits raw : List Bool) (second inverse : Bool) (remaining frequency : ℕ) :
    data (steady bits raw second inverse remaining frequency) (.aux .normalizer)=normalizer bits second inverse := rfl
/-- Actual inter-component copy scratch is empty between queries. -/
theorem steady_scratch (bits raw : List Bool) (second inverse : Bool) (remaining frequency : ℕ) :
    data (steady bits raw second inverse remaining frequency) (.aux .scratch)=[] := rfl
end RiemannGaussian.SemiprimeD1StackPublicTransformLoopState
