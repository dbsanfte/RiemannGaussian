/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Tactic

/-!
# Arithmetic core of the sparse-residue weighted Gauss construction

These are exact certificate and collision identities. They do not construct a
reduced basis or assert a polynomial-arithmetic or factoring bit bound.
-/

namespace RiemannGaussian.SemiprimeSparseResidueGauss

/-- The two-dimensional reduction certificate bounds the first squared norm. -/
theorem weighted_gauss_certificate {F₁ F₂ dot N W : ℤ}
    (h₁ : 0 ≤ F₁) (horder : F₁ ≤ F₂) (hred : |2 * dot| ≤ F₁)
    (hgram : F₁ * F₂ - dot ^ 2 = N ^ 2 * W) :
    3 * F₁ ^ 2 ≤ 4 * N ^ 2 * W := by
  have hlo := neg_abs_le (2 * dot)
  have hhi := le_abs_self (2 * dot)
  have hprod : 0 ≤ (F₁ - 2 * dot) * (F₁ + 2 * dot) :=
    mul_nonneg (by omega) (by omega)
  have hnorm := mul_nonneg h₁ (sub_nonneg.mpr horder)
  nlinarith

/-- A quotient-lattice vector gives an exact hidden-factor polynomial hit. -/
theorem quotient_lattice_hit {H s a b c u P Q x : ℤ}
    (hu : u = H * c - s * b) (hlattice : P * Q ∣ H * u + s ^ 2 * a)
    (hP : P = H * x + s) (hcoprime : IsCoprime P H) :
    P ∣ c + b * x + a * x ^ 2 := by
  have hbase : P ∣ H * u + s ^ 2 * a := dvd_trans (dvd_mul_right P Q) hlattice
  have hclear : H ^ 2 * (c + b * x + a * x ^ 2) =
      H * u + s ^ 2 * a + P * (H * b + a * (P - 2 * s)) := by
    rw [hu, hP]
    ring
  have hd : P ∣ H ^ 2 * (c + b * x + a * x ^ 2) := by
    rw [hclear]
    exact dvd_add hbase (dvd_mul_right P _)
  have hd' : P ∣ H * (H * (c + b * x + a * x ^ 2)) := by
    simpa only [pow_two, mul_assoc] using hd
  exact hcoprime.dvd_of_dvd_mul_left (hcoprime.dvd_of_dvd_mul_left hd')

/-- The anchor exponent differs from the quotient exponent by an explicit
multiple of `P-1`; the sign is `1-P` in the displayed factorization. -/
theorem anchor_identity {H s a b c P x σ : ℤ}
    (hP : P = H * x + s) (hquotient : c + b * x + a * x ^ 2 = σ * P) :
    c * H ^ 2 + b * H * (1 - s) + a * (1 - s) ^ 2 - H ^ 2 * σ =
      (1 - P) * (a * (P + 1 - 2 * s) + b * H - H ^ 2 * σ) := by
  have hzero : H ^ 2 * (c + b * x + a * x ^ 2 - σ * P) = 0 := by
    rw [hquotient]
    ring
  rw [hP] at *
  nlinarith [hzero]

/-- The exact anchor identity supplies the multiplicative-order congruence. -/
theorem anchor_divisibility {H s a b c P x σ : ℤ}
    (hP : P = H * x + s) (hquotient : c + b * x + a * x ^ 2 = σ * P) :
    P - 1 ∣ c * H ^ 2 + b * H * (1 - s) + a * (1 - s) ^ 2 - H ^ 2 * σ := by
  rw [anchor_identity hP hquotient]
  refine ⟨-(a * (P + 1 - 2 * s) + b * H - H ^ 2 * σ), ?_⟩
  ring

end RiemannGaussian.SemiprimeSparseResidueGauss
