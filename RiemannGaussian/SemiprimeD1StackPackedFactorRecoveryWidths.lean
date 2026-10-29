/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryExecution
/-! # Semantic-free byte widths of the actual binary recovery operands
Only physical input lengths and actual component output-size lemmas are used.
There is no elapsed-runtime recurrence, numeric-unary discriminant, or assumed
factor bit-size in these bounds. All input padding remains charged.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryWidths
open SemiprimeD1StackPackedFactorRecoveryEncoding SemiprimeD1StackPackedFactorRecoveryExecution
open SemiprimeBitArithmetic SemiprimeBitDivision
/-- Both physical input words, including every padding bit. -/
def inputSize (bits scalar : List Bool) : ℕ := bits.length+scalar.length+1
/-- One fixed common linear width envelope for every actual arithmetic operand. -/
def limit (bits scalar : List Bool) : ℕ := 32*inputSize bits scalar
/-- Actual reverse stripping never increases its physical input width. -/
theorem trim_length (xs : List Bool) : (SemiprimeD1StackReduceExecution.trimReverse xs).length≤xs.length := by
  induction xs with
  | nil=>rfl
  | cons b xs ih=>
    cases b <;> simp only [SemiprimeD1StackReduceExecution.trimReverse,List.length_cons,List.length_reverse]
    · omega
    · omega
/-- Readout obtains at most the physically acquired N width. -/
theorem sum_length (bits scalar : List Bool) : (sumWord bits scalar).length≤bits.length :=
  SemiprimeD1StackPackedMomentReadoutEncoding.moment_length bits scalar true
/-- Actual raw square has linear physical width despite a potentially large numeric value. -/
theorem square_length (bits scalar : List Bool) : (squareWord (sumWord bits scalar)).length≤3*bits.length := by
  have h:=mulBits_length (sumWord bits scalar) (sumWord bits scalar)
  have hs:=sum_length bits scalar
  change (mulBits (sumWord bits scalar) (sumWord bits scalar)).bits.length≤_
  omega
/-- Actual ripple difference width equals its longer physical source operand. -/
theorem discriminant_length (bits scalar : List Bool) : (discriminant bits (sumWord bits scalar)).length≤3*bits.length+2 := by
  have h:=(subBits_counts (squareWord (sumWord bits scalar)) (fourWord bits) false).2.2.2.2
  have hs:=square_length bits scalar
  have hf : (fourWord bits).length=bits.length+2 := by simp only [fourWord,List.length_cons]
  change (subBits (squareWord (sumWord bits scalar)) (fourWord bits) false).result.bits.length≤_
  rw [h]
  exact max_le (by omega) (by omega)
/-- Full SQ output width is bounded by actual D bytes, not the numeric value of D. -/
theorem root_length (bits scalar : List Bool) : (rootWord bits (sumWord bits scalar)).length≤6*bits.length+6 := by
  let d:=discriminant bits (sumWord bits scalar)
  have h0:=SemiprimeD1StackBinarySquareRootArithmetic.original_word_length d
  have h1:=trim_length (SemiprimeD1StackBinarySquareRootArithmetic.wordLoop d d.length []).reverse
  rw [List.length_reverse] at h1
  have hd:=discriminant_length bits scalar
  change (SemiprimeD1StackReduceExecution.trimReverse
    (SemiprimeD1StackBinarySquareRootArithmetic.wordLoop d d.length []).reverse).length≤_
  dsimp only [d] at h0 h1 ⊢
  omega
/-- Both physically popped half tails have a linear byte bound, including all zero padding. -/
theorem half_lengths (bits scalar lo hi : List Bool)
    (hlo : (minusReport (sumWord bits scalar) (rootWord bits (sumWord bits scalar))).result.bits=false::lo)
    (hhi : plusWord (sumWord bits scalar) (rootWord bits (sumWord bits scalar))=false::hi) :
    lo.length≤6*bits.length+6 ∧ hi.length≤6*bits.length+7 := by
  have hs:=sum_length bits scalar
  have hr:=root_length bits scalar
  have hm : max (sumWord bits scalar).length (rootWord bits (sumWord bits scalar)).length≤6*bits.length+6 :=
    max_le (by omega) hr
  have h0:=(subBits_counts (sumWord bits scalar) (rootWord bits (sumWord bits scalar)) false).2.2.2.2
  have h1:=(addBits_counts (sumWord bits scalar) (rootWord bits (sumWord bits scalar)) false).2.2.2.2
  have h2:=congrArg List.length hlo
  have h3:=congrArg List.length hhi
  change (subBits _ _ false).result.bits.length=(false::lo).length at h2
  change (addBits _ _ false).bits.length=(false::hi).length at h3
  simp only [List.length_cons] at h2 h3
  omega
/-- One common fixed envelope bounds EVERY actual operand used by the whole accepted distinct path. -/
theorem all_widths_of_lengths (bits scalar lo hi : List Bool)
    (hlo' : lo.length≤6*bits.length+6) (hhi' : hi.length≤6*bits.length+7) :
    bits.length≤limit bits scalar ∧ (sumWord bits scalar).length≤limit bits scalar ∧
      (squareWord (sumWord bits scalar)).length≤limit bits scalar ∧ (fourWord bits).length≤limit bits scalar ∧
      (discriminant bits (sumWord bits scalar)).length≤limit bits scalar ∧
      (rootWord bits (sumWord bits scalar)).length≤limit bits scalar ∧
      lo.length≤limit bits scalar ∧ hi.length≤limit bits scalar ∧
      (SemiprimeD1StackReduceExecution.trimReverse lo.reverse).length≤limit bits scalar ∧
      (SemiprimeD1StackReduceExecution.trimReverse hi.reverse).length≤limit bits scalar ∧
      (SemiprimeD1StackPackedFactorRecoveryValidation.productWord
        (SemiprimeD1StackReduceExecution.trimReverse lo.reverse)
        (SemiprimeD1StackReduceExecution.trimReverse hi.reverse)).length≤limit bits scalar := by
  have hs:=sum_length bits scalar
  have hsq:=square_length bits scalar
  have hd:=discriminant_length bits scalar
  have hr:=root_length bits scalar
  have hl:=trim_length lo.reverse
  have hh:=trim_length hi.reverse
  rw [List.length_reverse] at hl hh
  have hp:=mulBits_length (SemiprimeD1StackReduceExecution.trimReverse lo.reverse)
    (SemiprimeD1StackReduceExecution.trimReverse hi.reverse)
  have hf : (fourWord bits).length=bits.length+2 := by simp only [fourWord,List.length_cons]
  unfold limit inputSize
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧
    (mulBits (SemiprimeD1StackReduceExecution.trimReverse lo.reverse)
      (SemiprimeD1StackReduceExecution.trimReverse hi.reverse)).bits.length≤_
  omega
end RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryWidths
