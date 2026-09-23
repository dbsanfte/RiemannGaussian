/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovFordQuantitativeScale
import RiemannGaussian.VinogradovFordSelectedIteration

/-!
# Quantitative decrease with Ford's published parameters

This applies the numerical first-scale estimate to the actual selected
defect recurrence. Constants are those of Ford's Lemma 3.6. The scalar
estimates here are unconditional; bounds for actual moments retain the
separate short-prime supply in `selected_moment_bound`.
-/

namespace RiemannGaussian.VinogradovFordDefectRate
noncomputable section
open VinogradovFordScales VinogradovFordSchedule VinogradovFordRank
open VinogradovFordQuantitativeScale VinogradovFordSelectedIteration

/-- The coefficient multiplying the scale error uses the rank-rounding
information before any upper bound is taken. -/
theorem scale_coefficient_bounds {k : ℕ} {delta : ℝ} (hk : 26 ≤ k)
    (hlower : (k : ℝ) ≤ delta) (hupper : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2) :
    0 ≤ 2 * (k : ℝ) * rank k delta - depthReserve k (rank k delta) delta ∧
      2 * (k : ℝ) * rank k delta - depthReserve k (rank k delta) delta ≤
        2 * (rank k delta : ℝ) * ((k : ℝ) - delta / k) := by
  obtain ⟨_, _, hrlo, hrhi⟩ := rank_bounds hk hlower hupper
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have ha : 1 ≤ delta / k := (le_div_iff₀ hkpos).mpr (by simpa using hlower)
  have he : delta / k * k = delta := div_mul_cancel₀ _ hkpos.ne'
  have hp := mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ (rank k delta : ℝ) - k + delta / k by linarith)
    (show (rank k delta : ℝ) - k + delta / k - 1 ≤ 0 by linarith)
  have hq := mul_nonneg (by linarith : 0 ≤ delta / k) (by linarith : 0 ≤ delta / k - 1)
  unfold depthReserve
  constructor
  · nlinarith [depth_nonneg (rank k delta), Nat.cast_nonneg (α := ℝ) k]
  · nlinarith

/-- Ford's (3.16), applied to the literal chosen step. The last term is
`16*(1 - Delta/k^2)/(7*k)`, written without a nested quotient. -/
theorem selectedStep_le_stationary {k : ℕ} {delta : ℝ} (hk : 1000 ≤ k)
    (hlower : (k : ℝ) ≤ delta) (hupper : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2) :
    selectedStep k delta ≤ delta - 2 * k +
      4 * (k : ℝ) ^ 2 * rank k delta /
        (2 * (rank k delta : ℝ) * k + depthReserve k (rank k delta) delta) +
      16 * ((k : ℝ) - delta / k) / (7 * (k : ℝ) ^ 2) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hr4 := (rank_bounds (by omega : 26 ≤ k) hlower hupper).1
  have hrpos : (0 : ℝ) < rank k delta := by exact_mod_cast (show 0 < rank k delta by omega)
  have herr := first_scale_error_le hk hlower hupper
  obtain ⟨ha, hb⟩ := scale_coefficient_bounds (by omega : 26 ≤ k) hlower hupper
  have hm := mul_le_mul_of_nonneg_right herr ha
  have hden : 0 < 2 * (rank k delta : ℝ) * k + depthReserve k (rank k delta) delta :=
    lt_of_lt_of_le (by positivity) (stationary_denominator_ge (by omega) hlower hupper)
  have he : selectedStep k delta = delta - 2 * k +
      4 * (k : ℝ) ^ 2 * rank k delta /
        (2 * (rank k delta : ℝ) * k + depthReserve k (rank k delta) delta) +
      (schedule k (rank k delta) (maximalDepth k (rank k delta) delta) delta 0 -
        stationaryScale k (rank k delta) delta) *
        (2 * (k : ℝ) * rank k delta - depthReserve k (rank k delta) delta) / 2 := by
    unfold selectedStep nextDefect stationaryScale
    have hd : (k : ℝ) * rank k delta * 2 + depthReserve k (rank k delta) delta ≠ 0 := by
      nlinarith
    field_simp [hd]
    unfold depthReserve
    ring
  have hcost : 16 / (7 * (k : ℝ) ^ 2 * rank k delta) *
      (2 * (k : ℝ) * rank k delta - depthReserve k (rank k delta) delta) / 2 ≤
        16 * ((k : ℝ) - delta / k) / (7 * (k : ℝ) ^ 2) := by
    calc
      _ ≤ 16 / (7 * (k : ℝ) ^ 2 * rank k delta) *
          (2 * (rank k delta : ℝ) * ((k : ℝ) - delta / k)) / 2 := by gcongr
      _ = _ := by field_simp
  rw [he]
  linarith

/-- Concavity of the quadratic denominator reduces this particular ratio
bound to its two endpoints, retaining the rank-rounding reserve. -/
theorem quadratic_ratio_le {a b c r U : ℝ} (hU : 0 ≤ U)
    (hrlo : b ≤ r) (hrhi : r ≤ b + 1) (hden : 0 < c * r - r ^ 2 + a)
    (hleft : b ≤ U * (c * b - b ^ 2 + a))
    (hright : b + 1 ≤ U * (c * (b + 1) - (b + 1) ^ 2 + a)) :
    r / (c * r - r ^ 2 + a) ≤ U := by
  apply (div_le_iff₀ hden).mpr
  have hl := mul_nonneg (show 0 ≤ 1 - (r - b) by linarith) (sub_nonneg.mpr hleft)
  have hh := mul_nonneg (show 0 ≤ r - b by linarith) (sub_nonneg.mpr hright)
  have hm := mul_nonneg (mul_nonneg hU (show 0 ≤ r - b by linarith))
    (show 0 ≤ 1 - (r - b) by linarith)
  nlinarith only [hl, hh, hm]

/-- The upper half of Ford's (3.17). Its endpoint margins factor as
`d^2*((2-d^2)*k-1)` and `d*(2+d)`, respectively. -/
theorem ratio_upper {k d r : ℝ} (hk : 26 ≤ k) (hd0 : 0 ≤ d) (hd : d ≤ 1 / 2)
    (hrlo : k * (1 - d) ≤ r) (hrhi : r ≤ k * (1 - d) + 1)
    (hden : 0 < 2 * r * k + 2 * d * k ^ 2 - (k - r) * (k - r + 1)) :
    r / (2 * r * k + 2 * d * k ^ 2 - (k - r) * (k - r + 1)) ≤
      (1 - d) / ((2 - d ^ 2) * k) + d / ((2 - d ^ 2) ^ 2 * k ^ 2) := by
  have hkpos : 0 < k := by linarith
  have hd2 : d ^ 2 ≤ 1 / 4 := by nlinarith
  have hB : 0 < 2 - d ^ 2 := by linarith
  let U := (1 - d) / ((2 - d ^ 2) * k) + d / ((2 - d ^ 2) ^ 2 * k ^ 2)
  have hU : 0 ≤ U := add_nonneg (div_nonneg (by linarith) (by positivity)) (by positivity)
  have hl : k * (1 - d) ≤ U *
      ((4 * k + 1) * (k * (1 - d)) - (k * (1 - d)) ^ 2 - k ^ 2 - k + 2 * d * k ^ 2) := by
    have he : U *
        ((4 * k + 1) * (k * (1 - d)) - (k * (1 - d)) ^ 2 - k ^ 2 - k + 2 * d * k ^ 2) -
        k * (1 - d) = d ^ 2 * ((2 - d ^ 2) * k - 1) / ((2 - d ^ 2) ^ 2 * k) := by
      dsimp [U]
      field_simp
      ring
    have hb : 0 ≤ (2 - d ^ 2) * k - 1 := by
      have hm := mul_le_mul_of_nonneg_right hd2 hkpos.le
      nlinarith
    have hp : 0 ≤ d ^ 2 * ((2 - d ^ 2) * k - 1) / ((2 - d ^ 2) ^ 2 * k) := by positivity
    linarith
  have hh : k * (1 - d) + 1 ≤ U *
      ((4 * k + 1) * (k * (1 - d) + 1) - (k * (1 - d) + 1) ^ 2 - k ^ 2 - k + 2 * d * k ^ 2) := by
    have he : U *
        ((4 * k + 1) * (k * (1 - d) + 1) - (k * (1 - d) + 1) ^ 2 - k ^ 2 - k + 2 * d * k ^ 2) -
        (k * (1 - d) + 1) = d * (2 + d) / ((2 - d ^ 2) ^ 2 * k) := by
      dsimp [U]
      field_simp
      ring
    have hp : 0 ≤ d * (2 + d) / ((2 - d ^ 2) ^ 2 * k) := by positivity
    linarith
  have he (v : ℝ) : (4 * k + 1) * v - v ^ 2 + (-k ^ 2 - k + 2 * d * k ^ 2) =
      2 * v * k + 2 * d * k ^ 2 - (k - v) * (k - v + 1) := by ring
  have hq := quadratic_ratio_le (a := -k ^ 2 - k + 2 * d * k ^ 2)
    (b := k * (1 - d)) (c := 4 * k + 1) hU hrlo hrhi
    (by rwa [he]) (by nlinarith only [hl]) (by nlinarith only [hh])
  simpa only [he] using hq

/-- The two elementary numerical relaxations in the last line of Ford's
proof of (3.14), with `32/21` and `16/7` unchanged. -/
theorem rational_rate_bound {k d : ℝ} (hk : 0 < k) (hd0 : 0 < d) (hd : d ≤ 1 / 2) :
    d - 2 / k + 4 * (1 - d) / ((2 - d ^ 2) * k) +
        4 * d / ((2 - d ^ 2) ^ 2 * k ^ 2) + 16 * (1 - d) / (7 * k ^ 3) ≤
      d * (1 - (2 - d) / (2 - d ^ 2) *
        (2 / k - 32 / (21 * k ^ 2) - 16 / (7 * d * k ^ 3))) := by
  have hd2 : d ^ 2 ≤ 1 / 4 := by nlinarith
  have hB : 0 < 2 - d ^ 2 := by linarith
  have hfirst : 1 - d ≤ (2 - d) / (2 - d ^ 2) := by
    apply (le_div_iff₀ hB).mpr
    have hh := mul_nonneg hd0.le (show 0 ≤ 1 + d - d ^ 2 by nlinarith)
    nlinarith
  have hprod : 21 / 8 ≤ (2 - d) * (2 - d ^ 2) := by
    have hh := mul_le_mul (show (3 : ℝ) / 2 ≤ 2 - d by linarith)
      (show (7 : ℝ) / 4 ≤ 2 - d ^ 2 by linarith) (by norm_num : (0 : ℝ) ≤ 7 / 4)
      (by linarith : 0 ≤ 2 - d)
    nlinarith
  have hsecond : 4 / (2 - d ^ 2) ^ 2 ≤ 32 * (2 - d) / (21 * (2 - d ^ 2)) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hB) (by positivity : 0 < 21 * (2 - d ^ 2))).mpr
    have hh := mul_nonneg hB.le (show 0 ≤ 32 * (2 - d) * (2 - d ^ 2) - 84 by linarith)
    nlinarith only [hh]
  have hs := mul_le_mul_of_nonneg_left hsecond (show 0 ≤ d / k ^ 2 by positivity)
  have hf := mul_le_mul_of_nonneg_left hfirst (show 0 ≤ 16 / (7 * k ^ 3) by positivity)
  have he : 4 * d / ((2 - d ^ 2) ^ 2 * k ^ 2) = (d / k ^ 2) * (4 / (2 - d ^ 2) ^ 2) := by
    field_simp
  have he' : 16 * (1 - d) / (7 * k ^ 3) = (16 / (7 * k ^ 3)) * (1 - d) := by ring
  rw [he, he']
  calc
    _ ≤ d - 2 / k + 4 * (1 - d) / ((2 - d ^ 2) * k) +
        (d / k ^ 2) * (32 * (2 - d) / (21 * (2 - d ^ 2))) +
        (16 / (7 * k ^ 3)) * ((2 - d) / (2 - d ^ 2)) := by linarith
    _ = _ := by field_simp; ring

/-- Ford's exact normalized defect-decrease estimate (3.14), for the
concrete rounded rank and actual maximal depth. -/
theorem normalized_defect_rate {k : ℕ} {delta : ℝ} (hk : 1000 ≤ k)
    (hlower : (k : ℝ) ≤ delta) (hupper : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2) :
    let d := delta / (k : ℝ) ^ 2
    selectedStep k delta / (k : ℝ) ^ 2 ≤
      d * (1 - (2 - d) / (2 - d ^ 2) *
        (2 / k - 32 / (21 * (k : ℝ) ^ 2) - 16 / (7 * d * (k : ℝ) ^ 3))) := by
  let d := delta / (k : ℝ) ^ 2
  change selectedStep k delta / (k : ℝ) ^ 2 ≤
    d * (1 - (2 - d) / (2 - d ^ 2) *
      (2 / k - 32 / (21 * (k : ℝ) ^ 2) - 16 / (7 * d * (k : ℝ) ^ 3)))
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hd0 : 0 < d := div_pos (by linarith) (sq_pos_of_pos hkpos)
  have hd : d ≤ 1 / 2 := (div_le_iff₀ (sq_pos_of_pos hkpos)).mpr (by nlinarith)
  have he : d * (k : ℝ) ^ 2 = delta := div_mul_cancel₀ _ (pow_ne_zero _ hkpos.ne')
  have hquot : delta / k = d * k := by dsimp [d]; field_simp
  obtain ⟨_, _, hrlo, hrhi⟩ := rank_bounds (by omega : 26 ≤ k) hlower hupper
  have hden : 0 < 2 * (rank k delta : ℝ) * k + depthReserve k (rank k delta) delta :=
    lt_of_lt_of_le (by positivity) (stationary_denominator_ge (by omega) hlower hupper)
  have hD : 2 * (rank k delta : ℝ) * k + 2 * d * (k : ℝ) ^ 2 -
      ((k : ℝ) - rank k delta) * ((k : ℝ) - rank k delta + 1) =
        2 * (rank k delta : ℝ) * k + depthReserve k (rank k delta) delta := by
    unfold depthReserve
    nlinarith only [he]
  have hr := ratio_upper (by linarith : (26 : ℝ) ≤ k) hd0.le hd
    (show (k : ℝ) * (1 - d) ≤ rank k delta by rw [hquot] at hrlo; nlinarith)
    (show (rank k delta : ℝ) ≤ (k : ℝ) * (1 - d) + 1 by rw [hquot] at hrhi; nlinarith)
    (by rwa [hD])
  rw [hD] at hr
  have hs := div_le_div_of_nonneg_right (selectedStep_le_stationary hk hlower hupper)
    (sq_nonneg (k : ℝ))
  have hnormalize : (delta - 2 * k + 4 * (k : ℝ) ^ 2 * rank k delta /
      (2 * (rank k delta : ℝ) * k + depthReserve k (rank k delta) delta) +
      16 * ((k : ℝ) - delta / k) / (7 * (k : ℝ) ^ 2)) / (k : ℝ) ^ 2 =
    d - 2 / k + 4 * ((rank k delta : ℝ) /
      (2 * (rank k delta : ℝ) * k + depthReserve k (rank k delta) delta)) +
      16 * (1 - d) / (7 * (k : ℝ) ^ 3) := by
    dsimp [d]
    field_simp
  rw [hnormalize] at hs
  calc
    _ ≤ d - 2 / k + 4 * (1 - d) / ((2 - d ^ 2) * k) +
        4 * d / ((2 - d ^ 2) ^ 2 * (k : ℝ) ^ 2) + 16 * (1 - d) / (7 * (k : ℝ) ^ 3) := by
      have hh := mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 4)
      simp only [div_eq_mul_inv] at hs hh ⊢
      nlinarith only [hs, hh]
    _ ≤ _ := rational_rate_bound hkpos hd0 hd

/-- Every active step of the literal selected moment sequence satisfies
the published quantitative recurrence, without a supplied scale estimate. -/
theorem selectedDefect_rate {k j : ℕ} (hk : 1000 ≤ k)
    (hactive : (k : ℝ) < selectedDefect k j) :
    let d := selectedDefect k j / (k : ℝ) ^ 2
    selectedDefect k (j + 1) / (k : ℝ) ^ 2 ≤
      d * (1 - (2 - d) / (2 - d ^ 2) *
        (2 / k - 32 / (21 * (k : ℝ) ^ 2) - 16 / (7 * d * (k : ℝ) ^ 3))) := by
  have hcontinue : (k : ℝ) - 1 < selectedDefect k j := by linarith
  simpa only [selectedDefect, if_pos hcontinue] using
    normalized_defect_rate hk hactive.le (selectedDefect_bounds (by omega) j).2

end
end RiemannGaussian.VinogradovFordDefectRate
