/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovFordRank
import RiemannGaussian.VinogradovFordScaleError
import Mathlib.Data.Nat.Sqrt

/-!
# Ford's numerical first-scale error

The maximal depth pays the terminal geometric error with the original
`0.071/k^4` allowance for every `k ≥ 1000`. Together with the stationary
scale estimate this is the quantitative scalar input to (3.16), without
weakening the constants in Ford's proof.
-/

namespace RiemannGaussian.VinogradovFordQuantitativeScale
noncomputable section
open VinogradovFordScales VinogradovFordSchedule VinogradovFordRank
open VinogradovFordScaleError

/-- A floor square root of the uniform reserve is an admissible candidate
for the actual maximal depth. -/
theorem sqrt_le_depth {k : ℕ} {delta : ℝ} (hk : 26 ≤ k)
    (hlower : (k : ℝ) ≤ delta) (hupper : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2) :
    Nat.sqrt (2 * k - 2) ≤ maximalDepth k (rank k delta) delta := by
  have hs := Nat.sqrt_le' (2 * k - 2)
  have hsn : Nat.sqrt (2 * k - 2) ^ 2 + 2 ≤ 2 * k := by omega
  have hsq : (Nat.sqrt (2 * k - 2) : ℝ) ^ 2 + 2 ≤ 2 * (k : ℝ) := by exact_mod_cast hsn
  have hkR : (26 : ℝ) ≤ k := by exact_mod_cast hk
  have hr := half_degree_lt_rank hk hlower hupper
  have hs0 := Nat.cast_nonneg (α := ℝ) (Nat.sqrt (2 * k - 2))
  have hthird : 3 * (Nat.sqrt (2 * k - 2) : ℝ) ≤ k := by
    nlinarith [sq_nonneg ((k : ℝ) - 9),
      sq_nonneg (3 * (Nat.sqrt (2 * k - 2) : ℝ) - k)]
  have hnk : Nat.sqrt (2 * k - 2) ≤ k := by
    have hh : (Nat.sqrt (2 * k - 2) : ℝ) ≤ k := by linarith
    exact_mod_cast hh
  have hcap : 10 * (Nat.sqrt (2 * k - 2) + 1) ≤ 9 * rank k delta := by
    have hh : (10 : ℝ) * (Nat.sqrt (2 * k - 2) + 1) ≤ 9 * rank k delta := by linarith
    exact_mod_cast hh
  apply le_maximalDepth hnk hcap
  have hy := reserve_ge hk hlower hupper
  nlinarith

/-- The elementary exponential domination used for the terminal error.
The base case is checked exactly, and the polynomial ratio is bounded
uniformly at every subsequent integer. -/
theorem terminal_polynomial_bound {n : ℕ} (hn : 44 ≤ n) :
    1000 * (((n : ℝ) + 1) ^ 2 + 1) ^ 4 ≤ 1136 * (2 : ℝ) ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hnR : (44 : ℝ) ≤ n := by exact_mod_cast hn
    have hratio : 10 * (((n : ℝ) + 2) ^ 2 + 1) ≤
        11 * (((n : ℝ) + 1) ^ 2 + 1) := by nlinarith [sq_nonneg ((n : ℝ) - 44)]
    have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 10 * (((n : ℝ) + 2) ^ 2 + 1)) hratio 4
    have hpoly : (((n : ℝ) + 2) ^ 2 + 1) ^ 4 ≤ 2 * (((n : ℝ) + 1) ^ 2 + 1) ^ 4 := by
      nlinarith only [hpow, pow_nonneg (show 0 ≤ ((n : ℝ) + 1) ^ 2 + 1 by positivity) 4]
    push_cast
    rw [pow_succ (2 : ℝ) n]
    nlinarith only [ih, hpoly]

/-- The original `0.071/k^4` terminal allowance holds at the actual
maximal depth, uniformly over the whole active defect range. -/
theorem terminal_error_le {k : ℕ} {delta : ℝ} (hk : 1000 ≤ k)
    (hlower : (k : ℝ) ≤ delta) (hupper : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2) :
    (1 / 2 : ℝ) ^ maximalDepth k (rank k delta) delta ≤ 71 / (1000 * (k : ℝ) ^ 4) := by
  let m := Nat.sqrt (2 * k - 2)
  have hm44 : 44 ≤ m := Nat.le_sqrt'.mpr (by omega)
  have hmax := sqrt_le_depth (by omega : 26 ≤ k) hlower hupper
  have hgeo : (1 / 2 : ℝ) ^ maximalDepth k (rank k delta) delta ≤ (1 / 2 : ℝ) ^ m :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hmax
  have hs := Nat.lt_succ_sqrt' (2 * k - 2)
  simp only [Nat.succ_eq_add_one] at hs
  have hkn : 2 * k ≤ (m + 1) ^ 2 + 1 := by dsimp [m]; omega
  have hkR : 2 * (k : ℝ) ≤ ((m : ℝ) + 1) ^ 2 + 1 := by exact_mod_cast hkn
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 * k) hkR 4
  have hpoly := terminal_polynomial_bound hm44
  have hmain : 1000 * (k : ℝ) ^ 4 ≤ 71 * (2 : ℝ) ^ m := by
    nlinarith only [hpow, hpoly]
  refine hgeo.trans ?_
  rw [div_pow, one_pow]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ m)
    (by positivity : (0 : ℝ) < 1000 * (k : ℝ) ^ 4)).mpr
  simpa using hmain

/-- The stationary denominator retains the small positive `1/4` term
which pays the finite terminal error in Ford's constants. -/
theorem stationary_denominator_ge {k : ℕ} {delta : ℝ} (hk : 26 ≤ k)
    (hlower : (k : ℝ) ≤ delta) (hupper : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2) :
    (7 * (k : ℝ) ^ 2 + 1) / 4 ≤ 2 * (rank k delta : ℝ) * k + depthReserve k (rank k delta) delta := by
  have hkR : (26 : ℝ) ≤ k := by exact_mod_cast hk
  have ha : 1 ≤ delta / k := (le_div_iff₀ (by linarith : (0 : ℝ) < k)).mpr (by simpa using hlower)
  have hb : delta / k ≤ ((k : ℝ) - 1) / 2 :=
    (div_le_iff₀ (by linarith : (0 : ℝ) < k)).mpr (by nlinarith)
  have hrlo := (rank_bounds hk hlower hupper).2.2.1
  have hy := (reserve_bounds hk hlower hupper).1
  have he : delta / k * k = delta := div_mul_cancel₀ _ (by positivity)
  have hp := mul_le_mul hb (show delta / k + 1 ≤ ((k : ℝ) + 1) / 2 by linarith)
    (by linarith : 0 ≤ delta / k + 1) (by linarith : 0 ≤ ((k : ℝ) - 1) / 2)
  have hm := mul_le_mul_of_nonneg_right hrlo.le (show (0 : ℝ) ≤ k by positivity)
  nlinarith

/-- The exact stationary estimate with the paper's `0.16/k^3` reserve. -/
theorem stationary_upper {k : ℕ} {delta : ℝ} (hk : 26 ≤ k)
    (hlower : (k : ℝ) ≤ delta) (hupper : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2) :
    stationaryScale k (rank k delta) delta ≤ 8 / (7 * (k : ℝ)) - 4 / (25 * (k : ℝ) ^ 3) := by
  have hkR : (26 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hd := stationary_denominator_ge hk hlower hupper
  have hden : 0 < 2 * (rank k delta : ℝ) * k + depthReserve k (rank k delta) delta :=
    lt_of_lt_of_le (by positivity) hd
  have hs : stationaryScale k (rank k delta) delta ≤ 8 * k / (7 * (k : ℝ) ^ 2 + 1) := by
    unfold stationaryScale
    apply (div_le_div_iff₀ hden (by positivity : (0 : ℝ) < 7 * (k : ℝ) ^ 2 + 1)).mpr
    have hh := mul_le_mul_of_nonneg_left hd (show (0 : ℝ) ≤ 8 * k by positivity)
    nlinarith
  refine hs.trans ?_
  field_simp
  nlinarith [sq_nonneg ((k : ℝ) - 26)]

/-- Ford's first-scale excess with the original numerical constant.
This is the scalar estimate immediately preceding (3.16). -/
theorem first_scale_error_le {k : ℕ} {delta : ℝ} (hk : 1000 ≤ k)
    (hlower : (k : ℝ) ≤ delta) (hupper : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2) :
    schedule k (rank k delta) (maximalDepth k (rank k delta) delta) delta 0 -
        stationaryScale k (rank k delta) delta ≤
      16 / (7 * (k : ℝ) ^ 2 * rank k delta) := by
  obtain ⟨hr4, _, _, _, hdepth, _⟩ := admissible (by omega : 26 ≤ k) hlower hupper
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hrpos : (0 : ℝ) < rank k delta := by exact_mod_cast (show 0 < rank k delta by omega)
  have hh := first_scale_le (by omega : 0 < k) (by omega : 0 < rank k delta) hupper hdepth
  have ht := terminal_error_le hk hlower hupper
  have hs := stationary_upper (by omega : 26 ≤ k) hlower hupper
  have htd := div_le_div_of_nonneg_right ht hrpos.le
  have hsd := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 2))
    (mul_nonneg hkpos.le hrpos.le)
  have hbudget : 71 / (1000 * (k : ℝ) ^ 4) / rank k delta +
      2 * (8 / (7 * (k : ℝ)) - 4 / (25 * (k : ℝ) ^ 3)) / (k * rank k delta) ≤
        16 / (7 * (k : ℝ) ^ 2 * rank k delta) := by
    field_simp
    ring_nf
    linarith
  linarith

end
end RiemannGaussian.VinogradovFordQuantitativeScale
