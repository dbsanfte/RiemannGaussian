/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceCompactBits
import RiemannGaussian.SemiprimeMacroParameters

/-! # Original physical input length and the goal's binary size
Canonical binary inputs have exactly the size used in the requested exponent.
Normalization of a supplied physical word is itself the existing paid Boolean
trim, and its linear input-scan cost is retained rather than silently erased.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1CanonicalInput
open SemiprimeBitArithmetic SemiprimeSourceCompactBits

/-- The literal goal size equals the original public macro size, also at zero. -/
theorem size_eq_clog (N : ℕ) : SemiprimeMacroParameters.bitLength N=Nat.clog 2 (N+1) := by
  apply Nat.le_antisymm
  · apply Nat.size_le.mpr
    have hp := Nat.le_pow_clog (by decide : 1 < (2:ℕ)) (N+1)
    omega
  · apply Nat.clog_le_of_le_pow
    exact Nat.succ_le_of_lt (Nat.lt_size_self N)

/-- Every canonical original binary word has precisely the theorem's size. -/
theorem compact_length (input : List Bool) (h : Compact input) :
    input.length=SemiprimeMacroParameters.bitLength (bitValue input) := by
  apply Nat.le_antisymm
  · rw [size_eq_clog]
    exact compact_length_clog input h
  · exact Nat.size_le.mpr (bitValue_lt_width input)

/-- Paid physical normalization preserves the original integer. -/
theorem trim_original (input : List Bool) :
    bitValue (trim input).bits=bitValue input ∧ Compact (trim input).bits := by
  exact ⟨trim_value input,trim_compact input⟩

/-- The actual normalized word has exact original goal size; reading any supplied
padding remains the explicit trim_clock cost below. -/
theorem trim_goal_length (input : List Bool) :
    (trim input).bits.length=Nat.clog 2 (bitValue input+1) := by
  rw [compact_length (trim input).bits (trim_compact input),size_eq_clog,trim_value]

/-- The normalization scan is linear in the actual supplied physical word. -/
theorem trim_work (input : List Bool) : (trim input).clock=6*input.length+1 := trim_clock input

end RiemannGaussian.SemiprimeD1CanonicalInput
