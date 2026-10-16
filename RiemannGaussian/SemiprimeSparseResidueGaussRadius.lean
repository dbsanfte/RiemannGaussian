/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSparseResidueGauss
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Floor.Div

/-! Exact producer-certificate closure for the quadratic quotient radius.
No reduced basis, residue acquisition, or bit-complexity theorem is asserted. -/

namespace RiemannGaussian.SemiprimeSparseResidueGaussRadius

/-- Real form of the exact reduced-Gram certificate. -/
theorem gram_bound {F F₂ dot N W : ℝ} (hF : 0 ≤ F) (ho : F ≤ F₂)
    (hr : |2 * dot| ≤ F) (hg : F * F₂ - dot ^ 2 = N ^ 2 * W) :
    3 * F ^ 2 ≤ 4 * N ^ 2 * W := by
  have hl := neg_abs_le (2 * dot)
  have hu := le_abs_self (2 * dot)
  have hp : 0 ≤ (F - 2 * dot) * (F + 2 * dot) :=
    mul_nonneg (by linarith) (by linarith)
  have hm := mul_nonneg hF (sub_nonneg.mpr ho)
  nlinarith

/-- The lifted norm bound follows from the Gram and nearest-line certificates. -/
theorem lifted_norm_bound {N H s X F T : ℝ} (hN : 0 < N) (hH : 0 < H)
    (hX : 1 ≤ X) (hs : 0 ≤ s) (hsH : s < H) (hscale : H ^ 3 ≤ N)
    (hgram : 3 * F ^ 2 ≤ 4 * N ^ 2 * (X ^ 2 * (s ^ 2 + H ^ 2 * X ^ 2)))
    (hlift : 4 * (s ^ 2 + H ^ 2 * X ^ 2) * T ≤
      4 * X ^ 2 * F + (s ^ 2 + H ^ 2 * X ^ 2) ^ 2) :
    2 * H * T ≤ 5 * N * X ^ 2 := by
  let D := s ^ 2 + H ^ 2 * X ^ 2
  have hXp : 0 < X := by linarith
  have hDp : 0 < D := by dsimp [D]; positivity
  have hs2 : s ^ 2 ≤ H ^ 2 := by nlinarith
  have hX2 : 1 ≤ X ^ 2 := by nlinarith
  have hDlo : H ^ 2 * X ^ 2 ≤ D := by dsimp [D]; nlinarith [sq_nonneg s]
  have hDhi : D ≤ 2 * H ^ 2 * X ^ 2 := by
    dsimp [D]
    nlinarith [mul_nonneg (sq_nonneg H) (sub_nonneg.mpr hX2)]
  have hHF : H * F ≤ 2 * N * D := by
    have hm := mul_nonneg (sq_nonneg H) (sub_nonneg.mpr hgram)
    have hn := mul_nonneg (by positivity : 0 ≤ 4 * N ^ 2 * D) (sub_nonneg.mpr hDlo)
    have hpos : 0 ≤ 2 * N * D := by positivity
    change 3 * F ^ 2 ≤ 4 * N ^ 2 * (X ^ 2 * D) at hgram
    nlinarith [sq_nonneg (H * F + 2 * N * D)]
  have hHD : H * D ≤ 2 * N * X ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hDhi hH.le
    have h2 := mul_le_mul_of_nonneg_right hscale (by positivity : 0 ≤ 2 * X ^ 2)
    nlinarith
  change 4 * D * T ≤ 4 * X ^ 2 * F + D ^ 2 at hlift
  have h1 := mul_le_mul_of_nonneg_left hlift hH.le
  have h2 := mul_le_mul_of_nonneg_left hHF (by positivity : 0 ≤ 4 * X ^ 2)
  have h3 := mul_le_mul_of_nonneg_right hHD hDp.le
  nlinarith

/-- Three-term evaluation is controlled by the weighted coefficient norm. -/
theorem evaluation_bound {a b c x X : ℝ} (hx : 0 ≤ x) (hxX : x ≤ X) :
    (c + b * x + a * x ^ 2) ^ 2 ≤
      3 * (c ^ 2 + X ^ 2 * b ^ 2 + X ^ 4 * a ^ 2) := by
  have hX : 0 ≤ X := le_trans hx hxX
  have hx2 : x ^ 2 ≤ X ^ 2 := by nlinarith
  have hx4 : x ^ 4 ≤ X ^ 4 := by nlinarith [sq_nonneg (X ^ 2 - x ^ 2)]
  have hb := mul_le_mul_of_nonneg_right hx2 (sq_nonneg b)
  have ha := mul_le_mul_of_nonneg_right hx4 (sq_nonneg a)
  nlinarith [sq_nonneg (c - b * x), sq_nonneg (c - a * x ^ 2),
    sq_nonneg (b * x - a * x ^ 2)]

/-- Squared quotient radius, with every target norm discharged by certificates. -/
theorem quotient_radius_squared {N H s X F F₂ dot a b c x P σ : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hX : 1 ≤ X) (hs : 0 ≤ s) (hsH : s < H)
    (hscale : H ^ 3 ≤ N) (hF : 0 ≤ F) (ho : F ≤ F₂)
    (hr : |2 * dot| ≤ F)
    (hg : F * F₂ - dot ^ 2 = N ^ 2 * (X ^ 2 * (s ^ 2 + H ^ 2 * X ^ 2)))
    (hlift : 4 * (s ^ 2 + H ^ 2 * X ^ 2) *
      (c ^ 2 + X ^ 2 * b ^ 2 + X ^ 4 * a ^ 2) ≤
      4 * X ^ 2 * F + (s ^ 2 + H ^ 2 * X ^ 2) ^ 2)
    (hx : 0 ≤ x) (hxX : x ≤ X) (hP : H * X ≤ 2 * P)
    (heval : c + b * x + a * x ^ 2 = σ * P) :
    H ^ 3 * σ ^ 2 ≤ 30 * N := by
  have hn := lifted_norm_bound hN hH hX hs hsH hscale (gram_bound hF ho hr hg) hlift
  have he := evaluation_bound (a := a) (b := b) (c := c) hx hxX
  rw [heval] at he
  have hXp : 0 < X := by linarith
  have hPp : 0 < P := by nlinarith
  have hP2 : H ^ 2 * X ^ 2 ≤ 4 * P ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hP) (by positivity : 0 ≤ 2 * P + H * X)
    nlinarith
  have h1 := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2 * H)
  have h2 := mul_le_mul_of_nonneg_left hP2 (by positivity : 0 ≤ H * σ ^ 2)
  have hc : X ^ 2 * (H ^ 3 * σ ^ 2) ≤ X ^ 2 * (30 * N) := by nlinarith
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hXp)).mp hc

/-- The squared bound gives the strict advertised real radius. -/
theorem radius_of_squared {N H σ : ℝ} (hN : 0 < N) (hH : 0 < H)
    (hbound : H ^ 3 * σ ^ 2 ≤ 30 * N) :
    |σ| < 6 * Real.sqrt (N / H ^ 3) := by
  have hp : 0 < N / H ^ 3 := div_pos hN (pow_pos hH 3)
  have hs := Real.sq_sqrt hp.le
  have hb : σ ^ 2 ≤ 30 * N / H ^ 3 := by
    apply (le_div_iff₀ (pow_pos hH 3)).mpr
    nlinarith
  have he : 30 * N / H ^ 3 = 30 * (N / H ^ 3) := by ring
  rw [he] at hb
  apply (sq_lt_sq₀ (abs_nonneg σ) (by positivity : 0 ≤ 6 * Real.sqrt (N / H ^ 3))).mp
  nlinarith [sq_abs σ]

/-- Full strict radius closure directly from the exact producer certificates. -/
theorem quotient_radius {N H s X F F₂ dot a b c x P σ : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hX : 1 ≤ X) (hs : 0 ≤ s) (hsH : s < H)
    (hscale : H ^ 3 ≤ N) (hF : 0 ≤ F) (ho : F ≤ F₂)
    (hr : |2 * dot| ≤ F)
    (hg : F * F₂ - dot ^ 2 = N ^ 2 * (X ^ 2 * (s ^ 2 + H ^ 2 * X ^ 2)))
    (hlift : 4 * (s ^ 2 + H ^ 2 * X ^ 2) *
      (c ^ 2 + X ^ 2 * b ^ 2 + X ^ 4 * a ^ 2) ≤
      4 * X ^ 2 * F + (s ^ 2 + H ^ 2 * X ^ 2) ^ 2)
    (hx : 0 ≤ x) (hxX : x ≤ X) (hP : H * X ≤ 2 * P)
    (heval : c + b * x + a * x ^ 2 = σ * P) :
    |σ| < 6 * Real.sqrt (N / H ^ 3) := by
  exact radius_of_squared hN hH
    (quotient_radius_squared hN hH hX hs hsH hscale hF ho hr hg hlift hx hxX hP heval)

/-- The implemented integer interval follows from a certified ceiling radius.
The caller still constructs `R` and proves `N ≤ H^3*R^2` (for example by
`R = ceil_sqrt (ceil (N/H^3))`); no ceiling algorithm is assumed here. -/
theorem integer_cap {N H R σ : ℤ} (hH : 0 < H) (hR : 1 ≤ R)
    (hsigma : H ^ 3 * σ ^ 2 ≤ 30 * N) (hceil : N ≤ H ^ 3 * R ^ 2) :
    |σ| ≤ 8 * R := by
  have hc : H ^ 3 * σ ^ 2 ≤ H ^ 3 * (30 * R ^ 2) := by nlinarith
  have hs : σ ^ 2 ≤ 30 * R ^ 2 :=
    (mul_le_mul_iff_right₀ (pow_pos hH 3)).mp hc
  have hstrict : |σ| < 8 * R := by
    apply (sq_lt_sq₀ (abs_nonneg σ) (by omega : 0 ≤ 8 * R)).mp
    nlinarith [sq_abs σ]
  exact hstrict.le

/-- The explicit integer radius used by the executable cap. -/
def publicRadius (N H : ℕ) : ℕ := Nat.sqrt (((N + H ^ 3 - 1) / H ^ 3) - 1) + 1

/-- The public radius is positive without any input promise. -/
theorem publicRadius_pos (N H : ℕ) : 1 ≤ publicRadius N H := by
  unfold publicRadius
  omega

/-- The explicit ceiling-square-root formula certifies the required interval. -/
theorem publicRadius_covers {N H : ℕ} (hN : 0 < N) (hH : 0 < H) :
    N ≤ H ^ 3 * publicRadius N H ^ 2 := by
  let t := (N + H ^ 3 - 1) / H ^ 3
  have hn : N ≤ H ^ 3 * t := by
    exact (ceilDiv_le_iff_le_mul (pow_pos hH 3)).mp (le_refl (N ⌈/⌉ H ^ 3))
  have ht : 1 ≤ t := by
    by_contra h
    have hz : t = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, mul_zero] at hn
    omega
  have hs := Nat.lt_succ_sqrt' (t - 1)
  have hs' : t ≤ (Nat.sqrt (t - 1) + 1) ^ 2 := by
    change t - 1 < (Nat.sqrt (t - 1) + 1) ^ 2 at hs
    omega
  exact hn.trans (Nat.mul_le_mul_left (H ^ 3) hs')

/-- The squared Gauss radius reaches the implemented, input-derived cap. -/
theorem public_integer_cap {N H : ℕ} {σ : ℤ} (hN : 0 < N) (hH : 0 < H)
    (hsigma : (H : ℤ) ^ 3 * σ ^ 2 ≤ 30 * (N : ℤ)) :
    |σ| ≤ 8 * (publicRadius N H : ℤ) := by
  apply integer_cap (by exact_mod_cast hH) (by exact_mod_cast publicRadius_pos N H) hsigma
  exact_mod_cast publicRadius_covers hN hH

end RiemannGaussian.SemiprimeSparseResidueGaussRadius
