/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceWordAcquisition

/-! # Original-input width for the native physical source/port join
The width is computed from original integer dimensions, not from a template or
an output bound. These numeric inequalities do not charge parameter extraction.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeNativeInputBits
open SemiprimeSourceWordAcquisition SemiprimeSourceRowHeight

/-- Actual shared width chosen by the native source/port frontend. -/
def inputBits (n B Q R J : ℕ) : ℕ := sourceBits B Q R+n+Q+R+J+1

/-- The physical source's full emitted width is covered. -/
theorem sourceWidth_le (n B Q R J : ℕ) : sourceBits B Q R+1≤ inputBits n B Q R J := by
  unfold inputBits
  omega

/-- This width is positive even at zero dimensions. -/
theorem positive (n B Q R J : ℕ) : 0< inputBits n B Q R J := by
  unfold inputBits
  omega

/-- Every ordinary scalar port dimension is covered by the shared dyadic input bound. -/
theorem dimensions_le (n B Q R J : ℕ) :
    n≤2^(inputBits n B Q R J) ∧ Q≤2^(inputBits n B Q R J) ∧
      J≤2^(inputBits n B Q R J) ∧ R≤2^(inputBits n B Q R J) := by
  have hp : inputBits n B Q R J≤2^(inputBits n B Q R J) := Nat.le_of_lt Nat.lt_two_pow_self
  unfold inputBits at hp ⊢
  omega

/-- The actual common source denominator has the shared dyadic input bound. -/
theorem denominator_le (n B Q R J : ℕ) : rowDenominator Q R≤2^(inputBits n B Q R J) := by
  exact (SemiprimeSourceWordAcquisition.denominator_le B Q R).trans
    (Nat.pow_le_pow_right (by decide) ((Nat.le_succ _).trans (sourceWidth_le n B Q R J)))

/-- The actual common source numerator bound has the same shared dyadic input bound. -/
theorem numerator_le (n B Q R J : ℕ) :
    B*2^rowNumeratorExponent Q R≤2^(inputBits n B Q R J) := by
  exact (SemiprimeSourceWordAcquisition.numerator_le B Q R).trans
    (Nat.pow_le_pow_right (by decide) ((Nat.le_succ _).trans (sourceWidth_le n B Q R J)))

/-- A deliberately coarse literal fixed polynomial for the actual width. -/
def polynomial (n B Q R J : ℕ) : ℕ :=
  B+2*(R+Q*Q*(Q+1))+(1+8*(Q+1)*(1+2*R+Q))+n+Q+R+J+1

/-- Logarithmic terms in the computed width are bounded from the original dimensions. -/
theorem inputBits_le_polynomial (n B Q R J : ℕ) : inputBits n B Q R J≤polynomial n B Q R J := by
  have hQ : Nat.clog 2 Q≤Q := Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)
  have h8 : Nat.clog 2 (8*(Q+1))≤8*(Q+1) :=
    Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)
  unfold inputBits sourceBits denominatorBits rowNumeratorExponent rowCoefficientExponent polynomial
  calc
    _ ≤ B+(R+Q*Q*(Q+1))+(R+Q*Q*(Q+1)+(1+8*(Q+1)*(1+2*R+Q)))+n+Q+R+J+1 := by gcongr
    _ = _ := by ring

end RiemannGaussian.SemiprimeNativeInputBits
