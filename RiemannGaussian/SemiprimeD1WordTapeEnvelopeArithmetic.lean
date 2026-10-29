/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1OriginalEnvelopeRate

/-! # Fixed local envelope absorbs actual active and tape-leaf components
All constants are chosen before the input. This module is pure arithmetic;
actual program reports are bound to its premises by the counter theorem.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1WordTapeEnvelopeArithmetic
open SemiprimeD1OriginalEnvelopeRate SemiprimeD1PackingReady SemiprimeD1Schedule

/-- Active fixed coefficients fit the single uniform local envelope. -/
theorem active_raise (A ka B kb s : ℕ) :
    A*(scalar s+1)^ka*2^(A*degreeCap s) ≤ localEnvelope (A+B+16) (ka+kb+1) s := by
  unfold localEnvelope
  apply Nat.mul_le_mul
  · exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
  · apply Nat.pow_le_pow_right (by decide)
    have h:=Nat.mul_le_mul_right (degreeCap s) (show A ≤ A+B+16 by omega)
    omega

/-- An executed tape leaf plus every actual native frame control fits the same
fixed envelope. No desired intermediate width or output value is assumed. -/
theorem leaf_control_le (A ka B kb s leaf control : ℕ)
    (hleaf : leaf ≤ B*(scalar s+1)^kb*2^(B*degreeCap s)*2^leafSize s (logarithm s))
    (hcontrol : control ≤ 4*scalar s+8) :
    leaf+control ≤ localEnvelope (A+B+16) (ka+kb+1) s := by
  let K:=ka+kb+1
  let C:=A+B+16
  let base:=(scalar s+1)^K
  let factor:=2^(C*degreeCap s+leafSize s (logarithm s))
  have hp : (scalar s+1)^kb ≤ base := Nat.pow_le_pow_right (by omega) (by dsimp only [K];omega)
  have he : 2^(B*degreeCap s+leafSize s (logarithm s)) ≤ factor := by
    apply Nat.pow_le_pow_right (by decide)
    dsimp only [C]
    have h:=Nat.mul_le_mul_right (degreeCap s) (show B ≤ A+B+16 by omega)
    omega
  have hl : leaf ≤ B*base*factor := by
    calc
      _ ≤ B*(scalar s+1)^kb*2^(B*degreeCap s)*2^leafSize s (logarithm s) := hleaf
      _ = B*(scalar s+1)^kb*2^(B*degreeCap s+leafSize s (logarithm s)) := by rw [Nat.mul_assoc,←pow_add]
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left B hp) he
  have hbase : scalar s+1 ≤ base := Nat.le_self_pow (by dsimp only [K];omega) _
  have hfactor : 1 ≤ factor := Nat.one_le_two_pow
  have hc : control ≤ 8*base*factor := by
    have h8 : control ≤ 8*(scalar s+1) := by omega
    calc
      _ ≤ 8*base := h8.trans (Nat.mul_le_mul_left _ hbase)
      _ ≤ _ := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (8*base) hfactor
  change _ ≤ C*base*factor
  calc
    _ ≤ B*base*factor+8*base*factor := Nat.add_le_add hl hc
    _ = (B+8)*base*factor := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by dsimp only [C];omega))

end RiemannGaussian.SemiprimeD1WordTapeEnvelopeArithmetic
