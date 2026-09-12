/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaEulerOscillation

/-!
# A uniform direct zeta truncation remainder

The exact endpoint expansion and the complete oscillatory Bernoulli bound
give an absolute constant times `A^(-Re(s))` when `A=N+1` exceeds the
imaginary height and `0<Re(s)<=1`. No eta denominator or height factor
remains. This is a direct-truncation input for the near-one growth chain,
not a claim to Yang's optimized numerical constant or zero-free region.
-/

namespace RiemannGaussian.ZetaEulerUniformRemainder
noncomputable section
open Complex Set ZetaEulerCell ZetaEulerTruncation ZetaEulerBernoulli

private theorem norm_bounds {s : ℂ} (hs : 0 < s.re) (hs1 : s.re ≤ 1)
    {a : ℝ} (ha : 1 ≤ a) (ht : |s.im| ≤ a) :
    ‖s‖ ≤ 2 * a ∧ ‖s + 1‖ ≤ 3 * a ∧ ‖s + 2‖ ≤ 4 * a := by
  have hn := Complex.norm_le_abs_re_add_abs_im s
  rw [abs_of_pos hs] at hn
  have hn1 := norm_add_le s 1
  have hn2 := norm_add_le s 2
  norm_num at hn1 hn2
  constructor
  · linarith
  constructor <;> linarith

/-- On the actual positive strip and height-sized cutoff, the full
Bernoulli tail has a uniform two-power gain with an exact rational constant. -/
theorem norm_tail_le_scaled {s : ℂ} (hs : 0 < s.re) (hs1 : s.re ≤ 1)
    (N : ℕ) (ht : |s.im| ≤ N + 1) :
    ‖tail N s‖ ≤ (13 / 162 : ℝ) * (N + 1 : ℝ) ^ (-s.re) / (N + 1 : ℝ) ^ 2 := by
  let a : ℝ := N + 1
  have ha1 : 1 ≤ a := by dsimp [a]; have hN := Nat.cast_nonneg (α := ℝ) N; linarith
  have ha : 0 < a := by positivity
  have hn := (norm_bounds hs hs1 ha1 ht).2.2
  have hp : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
  have hpi : 1 / Real.pi ≤ (1 / 3 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp
  have hc : ‖s + 2‖ / Real.pi ^ 2 ≤ 4 * a / 9 := by
    calc
      _ ≤ ‖s + 2‖ / 9 := div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) (by nlinarith)
      _ ≤ _ := div_le_div_of_nonneg_right hn (by norm_num)
  have hfirst := mul_le_mul_of_nonneg_right hpi (Real.rpow_nonneg ha.le (-s.re - 2))
  have hsecond : ‖s + 2‖ / Real.pi ^ 2 * a ^ (-s.re - 3) / (s.re + 3) ≤
      (4 * a / 9) * a ^ (-s.re - 3) / 3 := by
    calc
      _ ≤ (‖s + 2‖ / Real.pi ^ 2 * a ^ (-s.re - 3)) / 3 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg ha.le _)) (by norm_num)
  have h := (ZetaEulerOscillation.norm_tail_le hs N ht).trans
    (div_le_div_of_nonneg_right (add_le_add hfirst hsecond) (by norm_num))
  change ‖tail N s‖ ≤ (13 / 162 : ℝ) * a ^ (-s.re) / a ^ 2
  apply h.trans_eq
  rw [Real.rpow_sub ha, Real.rpow_sub ha]
  norm_num
  field_simp
  ring

/-- The full original complex Euler remainder is bounded uniformly
by one cutoff power throughout `0<Re(s)<=1` once `N+1>=abs(Im(s))`. -/
theorem norm_remainder_le_power {s : ℂ} (hs : 0 < s.re) (hs1 : s.re ≤ 1)
    (N : ℕ) (ht : |s.im| ≤ N + 1) :
    ‖remainder N s‖ ≤ (N + 1 : ℝ) ^ (-s.re) := by
  let a : ℝ := N + 1
  have ha1 : 1 ≤ a := by dsimp [a]; have hN := Nat.cast_nonneg (α := ℝ) N; linarith
  have ha : 0 < a := by positivity
  obtain ⟨hn, hn1, _⟩ := norm_bounds hs hs1 ha1 ht
  have hp (r : ℂ) : ‖(N + 1 : ℂ) ^ r‖ = a ^ r.re := by
    rw [show (N + 1 : ℂ) = (a : ℂ) by simp [a], norm_cpow_eq_rpow_re_of_pos ha]
  have ht' := norm_tail_le_scaled hs hs1 N ht
  change ‖tail N s‖ ≤ (13 / 162 : ℝ) * a ^ (-s.re) / a ^ 2 at ht'
  have hprod : ‖s‖ * ‖s + 1‖ / 2 ≤ 3 * a ^ 2 := by
    have h := mul_le_mul hn hn1 (norm_nonneg _) (by positivity)
    nlinarith
  have hsecond : ‖s‖ / 12 * a ^ (-s.re - 1) ≤ 2 * a / 12 * a ^ (-s.re - 1) :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hn (by norm_num)) (by positivity)
  have hthird := mul_le_mul hprod ht' (norm_nonneg _) (by positivity : 0 ≤ 3 * a ^ 2)
  rw [remainder_eq hs]
  have htri := (norm_sub_le
    ((N + 1 : ℂ) ^ (-s) / 2 + s / 12 * (N + 1 : ℂ) ^ (-s - 1))
    (s * (s + 1) / 2 * tail N s)).trans
      (add_le_add_left (norm_add_le _ _) _)
  simp only [norm_div, norm_mul, hp] at htri
  norm_num only [norm_ofNat] at htri
  change _ ≤ a ^ (-s.re) / 2 + ‖s‖ / 12 * a ^ (-s.re - 1) +
    ‖s‖ * ‖s + 1‖ / 2 * ‖tail N s‖ at htri
  apply htri.trans
  apply ((add_le_add (add_le_add_right hsecond _) hthird)).trans
  have he : a ^ (-s.re) / 2 + 2 * a / 12 * a ^ (-s.re - 1) +
      3 * a ^ 2 * ((13 / 162 : ℝ) * a ^ (-s.re) / a ^ 2) =
        (49 / 54 : ℝ) * a ^ (-s.re) := by
    rw [Real.rpow_sub ha, Real.rpow_one]
    field_simp
    ring
  rw [he]
  change (49 / 54 : ℝ) * a ^ (-s.re) ≤ a ^ (-s.re)
  nlinarith [Real.rpow_nonneg ha.le (-s.re)]

/-- Actual zeta admits a direct ordinary Dirichlet truncation with its
exact pole-endpoint norm and a height-uniform remainder, with no eta loss. -/
theorem norm_zeta_sub_partialSum_le {s : ℂ} (hs : 0 < s.re) (hs1 : s.re ≤ 1)
    (hsne : s ≠ 1) (N : ℕ) (ht : |s.im| ≤ N + 1) :
    ‖riemannZeta s - partialSum N s‖ ≤
      (N + 1 : ℝ) ^ (1 - s.re) / ‖s - 1‖ + (N + 1 : ℝ) ^ (-s.re) := by
  rw [zeta_eq_partialSum_add_endpoint_add_remainder hs hsne N]
  rw [show partialSum N s + (N + 1 : ℂ) ^ (1 - s) / (s - 1) + remainder N s - partialSum N s =
    (N + 1 : ℂ) ^ (1 - s) / (s - 1) + remainder N s by ring]
  apply (norm_add_le _ _).trans
  have hp : ‖(N + 1 : ℂ) ^ (1 - s) / (s - 1)‖ =
      (N + 1 : ℝ) ^ (1 - s.re) / ‖s - 1‖ := by
    rw [norm_div]
    congr 1
    have h := norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < N + 1) (1 - s)
    simpa only [ofReal_add, ofReal_natCast, ofReal_one, sub_re, one_re] using h
  rw [hp]
  exact add_le_add_right (norm_remainder_le_power hs hs1 N ht) _

end
end RiemannGaussian.ZetaEulerUniformRemainder
