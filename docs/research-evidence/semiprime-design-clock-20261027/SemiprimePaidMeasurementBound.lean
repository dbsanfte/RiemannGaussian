/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeAcquiredSourceCounter

/-! # Explicit binary envelope for original integer measurement rows
This bounds the actual source constraint height. It is not a clock for encoding
those integers or for acquiring the source parameters.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimePaidMeasurementBound

/-- A parameter-only bit envelope, valid also at zero parameters. -/
def bits (B Q R : ℕ) : ℕ := B+2+2*R*(Q+3)

/-- The public measurement height fits the explicit dyadic envelope. -/
theorem bound_le (B Q R : ℕ) :
    SemiprimeAcquiredSourceCounter.measurementBound B Q R ≤ 2^(bits B Q R) := by
  have hB : B ≤ 2^B := Nat.le_of_lt Nat.lt_two_pow_self
  have hQ : Q ≤ 2^Q := Nat.le_of_lt Nat.lt_two_pow_self
  have hbase : 8*Q ≤ 2^(Q+3) := by
    calc
      8*Q ≤ 8*2^Q := Nat.mul_le_mul_left 8 hQ
      _ = 2^(Q+3) := by rw [pow_add]; ring
  have hp := Nat.pow_le_pow_left hbase (2*R)
  have hm : B*2*(8*Q)^(2*R) ≤ (2^B)*2*(2^(Q+3))^(2*R) :=
    Nat.mul_le_mul (Nat.mul_le_mul_right 2 hB) hp
  have he : (2^B)*2*(2^(Q+3))^(2*R)=2^(B+1+2*R*(Q+3)) := by
    rw [← pow_mul,← pow_succ,← pow_add]
    congr 1
    ring
  rw [he] at hm
  exact hm.trans (Nat.pow_le_pow_right (by decide : 0<2) (by dsimp [bits]; omega))

/-- Integer absolute bounds can be enlarged without any coefficient advice. -/
theorem integer_bound {z : ℤ} (B Q R : ℕ)
    (hz : z.natAbs ≤ SemiprimeAcquiredSourceCounter.measurementBound B Q R) :
    z.natAbs ≤ 2^(bits B Q R) := hz.trans (bound_le B Q R)

end RiemannGaussian.SemiprimePaidMeasurementBound
