/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedPublicInputCompactExecution
/-! # Exact compact coefficients and the wrapper's own quadratic allowance -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 262144
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackMarkedPublicInputCompactBounds
open SemiprimeD1StackMarkedPublicInputCompact SemiprimeD1StackMarkedPublicInputCompactExecution
open SemiprimeD1StackMarkedPublicInputCost (inputSize)
open SemiprimeBitArithmetic
/-- Physically removing high zero padding never enlarges the actual word. -/
theorem trim_length (xs : List Bool) :
    (SemiprimeD1StackReduceExecution.trimReverse xs).length ≤ xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases b <;> simp only [SemiprimeD1StackReduceExecution.trimReverse,List.length_cons,List.length_reverse]
    · omega
    · rfl
/-- Actual wrapper coefficient is compact, including zero as the empty word. -/
theorem coefficient_compact (bits raw indexWord : List Bool) (side : Bool) :
    SemiprimeSourceCompactBits.Compact (coefficient bits raw indexWord side) :=
  SemiprimeD1StackReduceExecution.trimReverse_compact _
/-- The paid trim preserves the entire original NONNEGATIVE integer value. -/
theorem coefficient_value (bits raw indexWord : List Bool) (side : Bool) :
    bitValue (coefficient bits raw indexWord side)=
      bitValue (SemiprimeD1StackMarkedPublicInputEncoding.coefficient bits raw indexWord side) := by
  rw [coefficient,SemiprimeD1StackReduceExecution.trimReverse_value,List.reverse_reverse]
/-- Compact words fit the actually acquired root precision without any lost integer information. -/
theorem coefficient_length (bits raw indexWord : List Bool) (side : Bool) :
    (coefficient bits raw indexWord side).length ≤ 2*bits.length := by
  have h := trim_length (SemiprimeD1StackMarkedPublicInputEncoding.coefficient bits raw indexWord side).reverse
  simpa only [coefficient,List.length_reverse,SemiprimeD1StackMarkedPublicInputMetadata.coefficient_length] using h
/-- Own fixed wrapper allowance, including real66 source, reverse, trim and all returns. -/
def polynomial (bits raw indexWord : List Bool) : Nat :=
  10000000000000000*(inputSize bits raw indexWord)^2
/-- This wrapper's whole bound is derived from actual executed component caps. -/
theorem runBound_le (bits raw indexWord : List Bool) (side : Bool) :
    runBound bits raw indexWord side ≤ polynomial bits raw indexWord := by
  have ht := SemiprimeD1StackReduceExecution.trimTime_le
    (SemiprimeD1StackMarkedPublicInputEncoding.coefficient bits raw indexWord side).reverse
  rw [List.length_reverse,SemiprimeD1StackMarkedPublicInputMetadata.coefficient_length] at ht
  have hs : 2 ≤ inputSize bits raw indexWord := by unfold inputSize;omega
  have he : bits.length ≤ inputSize bits raw indexWord := by unfold inputSize;omega
  unfold runBound polynomial SemiprimeD1StackMarkedPublicInputCost.polynomial
  rw [SemiprimeD1StackMarkedPublicInputMetadata.coefficient_length]
  nlinarith
/-- Actual compact word-source trace, with no decoded coefficient or clock supplier. -/
theorem source_run_bounded (bits raw indexWord : List Bool) (side : Bool) (hb : bits≠[]) :
    ∃ t ≤ polynomial bits raw indexWord,
      C.run program t (initial bits raw indexWord side)=some (done bits raw indexWord side) := by
  obtain ⟨t,ht,hr⟩ := source_run bits raw indexWord side hb
  exact ⟨t,ht.trans (runBound_le bits raw indexWord side),hr⟩
end RiemannGaussian.SemiprimeD1StackMarkedPublicInputCompactBounds

