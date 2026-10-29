/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackDigitBank
import RiemannGaussian.SemiprimeD1StackRadixDigitExecution

/-! # Mathematical specification of the actual streaming bank
Fuel and indexed values below are proof parameters only. The fixed machine
instead tests the physical reader for EOF and invokes its literal block code.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackDigitBankSpec
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeBitArithmetic

/-- Raw concatenation of encoded vector entries, before the final false terminator. -/
def entries : List (List Bool)→List Bool
  | [] => []
  | word::words => (true::frame word [])++entries words

/-- Appending after an actually framed word has the expected byte order. -/
theorem frame_append (word tail : List Bool) : frame word tail=frame word []++tail := by
  induction word with
  | nil => rfl
  | cons b word ih => simp only [frame,ih,List.cons_append]

/-- The final physical log reversal plus terminator is the frozen vector layout. -/
theorem entries_vectorBits (words : List (List Bool)) :
    entries words++[false]=SemiprimeD1TensorTapeCodec.vectorBits words := by
  induction words with
  | nil => rfl
  | cons word words ih =>
    simp only [entries,SemiprimeD1TensorTapeCodec.vectorBits,List.append_assoc,List.cons_append,ih]
    rw [frame_append word (SemiprimeD1TensorTapeCodec.vectorBits words)]

/-- Proof-side bounded description of the same successive block acquisitions.
There is no fuel input or evaluator instruction in the real EOF-driven machine. -/
def blocks (width : List Bool) : ℕ→List Bool→List (List Bool)
  | 0,_ => []
  | _+1,[] => []
  | n+1,word@(_::_) => SemiprimeD1StackDigitBlockExecution.result word width::blocks width n (word.drop width.length)

/-- Every actual canonical block has intrinsically bounded byte width. -/
theorem block_length (word width : List Bool) :
    (SemiprimeD1StackDigitBlockExecution.result word width).length ≤ width.length :=
  SemiprimeD1JetScalarBits.reduce_length _ _

/-- The reverse log cannot hide unbounded storage growth. -/
theorem entries_blocks_length (width : List Bool) (n : ℕ) (word : List Bool) :
    (entries (blocks width n word)).length ≤ n*(2*width.length+2) := by
  induction n generalizing word with
  | zero => simp [blocks,entries]
  | succ n ih =>
    cases word with
    | nil => simp only [blocks,entries,List.length_nil];omega
    | cons b word =>
      have hh:=ih ((b::word).drop width.length)
      have hb:=block_length (b::word) width
      simp only [blocks,entries,List.length_append,List.length_cons,
        SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil,Nat.add_mul,Nat.one_mul]
      omega

/-- One positive-sized physical block strictly shortens a nonempty reader. -/
theorem drop_progress (width : List Bool) (hw : width≠[]) (b : Bool) (word : List Bool) :
    ((b::word).drop width.length).length < (b::word).length := by
  have hp : 0<width.length := List.length_pos_iff.mpr hw
  simp only [List.length_drop,List.length_cons]
  omega

/-- Exact arithmetic recurrence for the number of positive-width input blocks. -/
theorem ceil_step (n B : ℕ) (hn : 0<n) (hB : 0<B) :
    (n+B-1)/B=1+(n-B+B-1)/B := by
  have he : n+B-1=(n-1)+B := by omega
  rw [he,Nat.add_div_right _ hB]
  by_cases hb : B ≤ n
  · have hs : n-B+B-1=n-1 := by omega
    rw [hs]
    omega
  · have hz : n-B=0 := by omega
    rw [hz,Nat.zero_add,Nat.div_eq_of_lt (by omega : B-1<B),
      Nat.div_eq_of_lt (by omega : n-1<B)]

/-- With enough proof-side fuel, the EOF loop emits EXACTLY the actual ceiling count. -/
theorem blocks_length (width : List Bool) (hw : width≠[]) (n : ℕ) (word : List Bool)
    (hf : word.length ≤ n) :
    (blocks width n word).length=(word.length+width.length-1)/width.length := by
  have hB : 0<width.length := List.length_pos_iff.mpr hw
  induction n generalizing word with
  | zero =>
    have he : word=[] := List.length_eq_zero_iff.mp (by omega)
    subst word
    simp only [blocks,List.length_nil,Nat.zero_add]
    exact (Nat.div_eq_of_lt (by omega : width.length-1<width.length)).symm
  | succ n ih =>
    cases word with
    | nil =>
      simp only [blocks,List.length_nil,Nat.zero_add]
      exact (Nat.div_eq_of_lt (by omega : width.length-1<width.length)).symm
    | cons b word =>
      have hs:=drop_progress width hw b word
      have htail : ((b::word).drop width.length).length ≤ n := by omega
      have hh:=ih _ htail
      simp only [blocks,List.length_cons]
      rw [hh,List.length_drop]
      have hc:=ceil_step (b::word).length width.length (by simp) hB
      simpa only [List.length_cons,Nat.add_comm] using hc.symm

/-- Every emitted word is exactly the corresponding canonical low digit of
the original binary input; no separately supplied index/digit value appears. -/
theorem blocks_get (width : List Bool) (n : ℕ) (word : List Bool) (i : ℕ)
    (hi : i<(blocks width n word).length) :
    (blocks width n word)[i]?=some (SemiprimeD1StackDigitBlockExecution.result
      (word.drop (width.length*i)) width) := by
  induction n generalizing word i with
  | zero => simp only [blocks,List.length_nil] at hi;omega
  | succ n ih =>
    cases word with
    | nil => simp only [blocks,List.length_nil] at hi;omega
    | cons b word =>
      cases i with
      | zero => simp only [blocks,List.getElem?_cons_zero,Nat.mul_zero,List.drop_zero]
      | succ i =>
        have htail : i<(blocks width n ((b::word).drop width.length)).length := by
          simp only [blocks,List.length_cons] at hi
          omega
        have hh:=ih _ i htail
        simp only [blocks,List.getElem?_cons_succ]
        rw [hh,List.drop_drop]
        have he : width.length+width.length*i=width.length*(i+1) := by
          rw [Nat.mul_add,Nat.mul_one]
          omega
        rw [he]

/-- The real bank's number of words is the exact original public digitCount. -/
theorem original_count (ell : ℕ) (hell : 0<ell) (word width : List Bool)
    (hn : word.length=ell) (hw : width.length=SemiprimeMacroParameters.radixBits ell) :
    (blocks width word.length word).length=SemiprimeMacroParameters.digitCount ell := by
  have hp : width≠[] := by
    have hB : 0<width.length := hw ▸ SemiprimeMacroParameters.radixBits_pos hell
    exact List.ne_nil_of_length_pos hB
  rw [blocks_length width hp word.length word le_rfl,hn,hw]
  rfl

/-- Every original target digit is acquired, including intervening zero digits. -/
theorem original_digit (ell : ℕ) (word width : List Bool)
    (hw : width.length=SemiprimeMacroParameters.radixBits ell) (i : ℕ)
    (hi : i<(blocks width word.length word).length) :
    ∃ digit,(blocks width word.length word)[i]?=some digit ∧
      bitValue digit=SemiprimeMacroParameters.targetDigit ell (bitValue word) i := by
  refine ⟨SemiprimeD1StackDigitBlockExecution.result (word.drop (width.length*i)) width,
    blocks_get width word.length word i hi,?_⟩
  rw [SemiprimeD1StackDigitBlockExecution.result,SemiprimeD1JetScalarBits.reduce_value,
    SemiprimeD1StackRadixDigitExecution.bitValue_drop,hw]
  simp only [SemiprimeMacroParameters.targetDigit,←pow_mul]

end RiemannGaussian.SemiprimeD1StackDigitBankSpec
