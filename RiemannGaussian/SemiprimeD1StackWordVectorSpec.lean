/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWordVector
import RiemannGaussian.SemiprimeD1StackDigitBankSpec

/-! # Exact physical assignment-word grouping specification
Block count is proof-side cache length; every raw prefix/padding occurrence is
the output of a real block call. The finite program carries no native list.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWordVectorSpec
open SemiprimeD1StackDigitBankSpec (entries entries_vectorBits)

/-- Exact successive raw word blocks, including physically generated EOF padding. -/
def blocks (width : List Bool) : ℕ→List Bool→List (List Bool)
  | 0,_ => []
  | n+1,word => SemiprimeD1StackWordBlockExecution.result word width::blocks width n (word.drop width.length)
/-- Every emitted field has the full literal physical word width. -/
theorem blocks_length (width : List Bool) (n : ℕ) (word : List Bool) : (blocks width n word).length=n := by
  induction n generalizing word with
  | zero => rfl
  | succ n ih => simp only [blocks,List.length_cons,ih]
/-- All actual framing and raw zero padding is retained in the output size. -/
theorem entries_length (width : List Bool) (n : ℕ) (word : List Bool) :
    (entries (blocks width n word)).length=n*(2*width.length+2) := by
  induction n generalizing word with
  | zero => simp only [blocks,entries,List.length_nil,Nat.zero_mul]
  | succ n ih =>
    simp only [blocks,entries,List.length_append,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length,
      List.length_nil,SemiprimeD1StackWordBlockExecution.result_length,ih,Nat.add_mul,Nat.one_mul]
    omega
/-- Repeated actual block calls retain exactly the original suffix after n words. -/
theorem drop_next (word width : List Bool) (n : ℕ) :
    (word.drop width.length).drop (n*width.length)=word.drop ((n+1)*width.length) := by
  rw [List.drop_drop]
  congr 1
  ring

/-- Every emitted indexed word comes from its exact original assignment block,
with no native selected-word read in the executing finite program. -/
theorem blocks_get (width : List Bool) (n : ℕ) (word : List Bool) (j : ℕ) (hj : j<n) :
    (blocks width n word)[j]?=some (SemiprimeD1StackWordBlockExecution.result (word.drop (j*width.length)) width) := by
  induction n generalizing word j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero => simp only [blocks,List.getElem?_cons_zero,Nat.zero_mul,List.drop_zero]
    | succ j =>
      have h:=ih (word.drop width.length) j (by omega)
      simp only [blocks,List.getElem?_cons_succ]
      rw [drop_next] at h
      exact h

/-- A complete original assignment yields every original fixed-width block
byte for byte, including high zeros, in increasing word order. -/
theorem blocks_get_take (width : List Bool) (n : ℕ) (word : List Bool) (j : ℕ)
    (hj : j<n) (hlen : n*width.length ≤ word.length) :
    (blocks width n word)[j]?=some ((word.drop (j*width.length)).take width.length) := by
  rw [blocks_get width n word j hj]
  congr 1
  apply SemiprimeD1StackWordBlockExecution.result_take
  have h:=Nat.mul_le_mul_right width.length (show j+1 ≤ n by omega)
  rw [Nat.add_mul,Nat.one_mul] at h
  simp only [List.length_drop]
  omega

end RiemannGaussian.SemiprimeD1StackWordVectorSpec
