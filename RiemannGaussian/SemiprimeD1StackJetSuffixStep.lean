/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetSuffixPass
/-! # Actual acquisition of one suffix-product record -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackJetSuffixStep
open SemiprimeD1StackJetSuffix SemiprimeD1StackJetSuffixCalls SemiprimeD1StackJetSuffixPass
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl" => SemiprimeD1StackJetSuffix.control

/-- A framed field is nonempty, including the zero-width counter case. -/
theorem peek_field (word tail radix records : List Bool) :
    Trace.Runs code 1 (ctl .suffixPeek) (data [] (frame word tail) [] radix [] records [] [])
      (ctl .readReverse) (data [] (frame word tail) [] radix [] records [] []) := by
  apply Trace.one_base code (ctl .suffixPeek) (ctl .readReverse)
    (.peek .reverseAxes (ctl .success) (ctl .readReverse) (ctl .readReverse)) _ _ rfl
  · cases word <;> simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose,frame]
  · rfl

/-- One original reverse-axis field produces an acquired q,d record and actual q*d.
The product body and every call/copy/clear operation are retained in this trace. -/
theorem one_suffix (q d : ℕ) (tail records : List Bool) :
    ∃m≤12*(q*d)+29*q+7*d+27,Trace.Runs code m (ctl .suffixPeek)
      (data [] (frame (unary q) tail) [] (unary d) [] records [] [])
      (ctl .suffixPeek) (data [] tail [] (unary (q*d)) []
        (frame (unary q) (frame (unary d) records)) [] []) := by
  have h1 := peek_field (unary q) tail (unary d) records
  have h2 := reverse_read (unary q) tail [] (unary d) [] records
  have h3 := reverse_flag [] tail (unary q) (unary d) [] records
  have h4 := radix_frame [] tail (unary q) (unary d) [] records
  have h5 := axis_frame [] tail (unary q) (unary d) [] (frame (unary d) records)
  obtain ⟨m,hm,h6⟩ := product_call q d [] tail (frame (unary q) (frame (unary d) records))
  have h7 := clear_radix (unary d) [] tail (unary (q*d))
    (frame (unary q) (frame (unary d) records))
  have h8 := move_product (q*d) [] tail [] (frame (unary q) (frame (unary d) records))
  simp only [List.append_nil] at h8
  have h := compose h1 (compose h2 (compose h3 (compose h4 (compose h5
    (compose h6 (compose h7 h8))))))
  simp only [unary_length] at h
  refine ⟨_,?_,h⟩
  nlinarith

end RiemannGaussian.SemiprimeD1StackJetSuffixStep
