/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1OriginalScalarResources

/-! # Bit widths of the actual remaining native arithmetic opcodes
These are output-size bounds for subsequent finite-machine refinement. Power
and left shift explicitly depend on the exponent or shift VALUE, never merely
its input bit width. They are not primitive execution-time theorems.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1NativeWordWidths

/-- A bounded natural fits a unary-sized binary word; zero is included. -/
theorem size_le_value (n : ℕ) : n.size ≤ n+1 :=
  Nat.size_le.mpr (Nat.lt_two_pow_self (n:=n+1) |>.trans' (by omega))

/-- Native addition grows the larger actual operand word by at most one bit. -/
theorem add_size (a b : ℕ) : (a+b).size ≤ max a.size b.size+1 := by
  have ha: a<2^(max a.size b.size):=(Nat.lt_size_self a).trans_le
    (Nat.pow_le_pow_right (by decide:0<(2:ℕ)) (le_max_left _ _))
  have hb: b<2^(max a.size b.size):=(Nat.lt_size_self b).trans_le
    (Nat.pow_le_pow_right (by decide:0<(2:ℕ)) (le_max_right _ _))
  apply Nat.size_le.mpr
  rw [pow_succ]
  omega

/-- Product size depends on the two operand words, with a one-bit reserve. -/
theorem mul_size (a b : ℕ) : (a*b).size ≤ a.size+b.size+1 := by
  have ha:=Nat.lt_size_self a
  have hb:=Nat.lt_size_self b
  have hp:a*b ≤ 2^(a.size+b.size):=by
    rw [pow_add]
    exact Nat.mul_le_mul ha.le hb.le
  apply Nat.size_le.mpr
  rw [pow_succ]
  have hpos:0<2^(a.size+b.size):=by positivity
  omega

/-- Pow output width pays the original exponent VALUE. In particular this does
not assert that arbitrary powering is polynomial in its input bit lengths. -/
theorem pow_size (base exponent : ℕ) :
    (base^exponent).size ≤ base.size*exponent+1 := by
  have hb:=Nat.lt_size_self base
  have hp:base^exponent ≤ 2^(base.size*exponent):=by
    simpa only [pow_mul] using Nat.pow_le_pow_left hb.le exponent
  apply Nat.size_le.mpr
  rw [pow_succ]
  have hpos:0<2^(base.size*exponent):=by positivity
  omega

/-- Every left-shifted payload bit, including a long zero extension, is paid. -/
theorem shiftLeft_size (base shift : ℕ) : (base<<<shift).size ≤ base.size+shift := by
  by_cases hb:base=0
  · simp [hb]
  · exact (Nat.size_shiftLeft hb shift).le

/-- Right shift never enlarges the actual operand word. -/
theorem shiftRight_size (base shift : ℕ) : (base>>>shift).size ≤ base.size :=
  Nat.size_le_size (Nat.shiftRight_le _ _)

/-- Restoring or native division cannot enlarge the numerator, even at zero. -/
theorem div_size (a b : ℕ) : (a/b).size ≤ a.size := Nat.size_le_size (Nat.div_le_self _ _)

/-- Modulo at a zero denominator returns the numerator and obeys the same cap. -/
theorem mod_size (a b : ℕ) : (a%b).size ≤ a.size := Nat.size_le_size (Nat.mod_le _ _)

/-- Truncated subtraction never enlarges its actual minuend. -/
theorem sub_size (a b : ℕ) : (a-b).size ≤ a.size := Nat.size_le_size (Nat.sub_le _ _)

/-- The square-root schedule primitive has no hidden large output. -/
theorem sqrt_size (a : ℕ) : (Nat.sqrt a).size ≤ a.size := Nat.size_le_size (Nat.sqrt_le_self _)

/-- The value of the ceiling binary logarithm fits the original word width. -/
theorem clog_le_size (a : ℕ) : Nat.clog 2 a ≤ a.size :=
  Nat.clog_le_of_le_pow (Nat.lt_size_self a).le

/-- Signed addition pays the actual two magnitude words. -/
theorem int_add_size (a b : ℤ) : (a+b).natAbs.size ≤ max a.natAbs.size b.natAbs.size+1 :=
  (Nat.size_le_size (Int.natAbs_add_le a b)).trans (add_size _ _)

/-- Signed subtraction has the same magnitude-word bound. -/
theorem int_sub_size (a b : ℤ) : (a-b).natAbs.size ≤ max a.natAbs.size b.natAbs.size+1 := by
  simpa only [sub_eq_add_neg,Int.natAbs_neg] using int_add_size a (-b)

/-- Signed multiplication pays both actual magnitude words. -/
theorem int_mul_size (a b : ℤ) : (a*b).natAbs.size ≤ a.natAbs.size+b.natAbs.size+1 := by
  rw [Int.natAbs_mul]
  exact mul_size _ _

/-- Signed powers retain exponent VALUE in their bit-size bound too. -/
theorem int_pow_size (a : ℤ) (n : ℕ) : (a^n).natAbs.size ≤ a.natAbs.size*n+1 := by
  rw [Int.natAbs_pow]
  exact pow_size _ _

end RiemannGaussian.SemiprimeD1NativeWordWidths
