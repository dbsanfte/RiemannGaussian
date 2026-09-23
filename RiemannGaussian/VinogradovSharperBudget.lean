/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovShortDyadic
import RiemannGaussian.VinogradovNearOneBudget
import RiemannGaussian.VinogradovLongBlocks
import RiemannGaussian.ZetaNearOneLineBudget

/-!
# Complete near-one coverage with the shorter-moment saving

The actual displacement is sixteen times the earlier one at the same
index. Both the low- and high-degree moment regimes are paid uniformly;
all original blocks, damping weights and derivative-profile boundaries
remain covered. The unchanged physical height threshold still suffices.
-/

namespace RiemannGaussian.VinogradovSharperBudget
noncomputable section
open DirichletDyadicBlocks VinogradovScaleSelection

/-- The near-one displacement paid by every selected middle-block degree. -/
def delta (n : ℕ) : ℝ := 1 / (4096 * (2 * (n : ℝ) + 1) ^ 2)

/-- The real line on which the original dyadic estimates are assembled. -/
def line (n : ℕ) : ℝ := 1 - delta n

/-- The resulting height exponent, with cubic decay in the target index. -/
def growth (n : ℕ) : ℝ := 2 * delta n / (n : ℝ)

/-- The displacement is strictly positive at every index. -/
theorem delta_pos (n : ℕ) : 0 < delta n := by unfold delta; positivity

/-- Every displacement lies within the paid long-block range. -/
theorem delta_le (n : ℕ) : delta n ≤ 1 / 4096 := by
  have h : (0 : ℝ) ≤ n := by positivity
  unfold delta
  apply (div_le_iff₀ (by positivity : 0 < 4096 * (2 * (n : ℝ) + 1) ^ 2)).mpr
  nlinarith [sq_nonneg (2 * (n : ℝ))]

/-- Each line stays in the open unit strip, to the right of one half. -/
theorem line_bounds (n : ℕ) : 1 / 2 ≤ line n ∧ line n < 1 := by
  have h := delta_le n
  have h' := delta_pos n
  unfold line
  constructor <;> linarith

/-- The height exponent is positive at every index used by the estimate. -/
theorem growth_pos {n : ℕ} (hn : 1 ≤ n) : 0 < growth n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold growth
  exact div_pos (mul_pos (by norm_num) (delta_pos n)) hn'

/-- The exponent has the Vinogradov displacement power, with a uniform
explicit coefficient and no asymptotic interpretation required. -/
theorem growth_le_displacement_power {n : ℕ} (hn : 1 ≤ n) :
    growth n ≤ 384 * delta n ^ (3 / 2 : ℝ) := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hKpos : 0 < 2 * (n : ℝ) + 1 := by positivity
  have hsqrt : Real.sqrt (delta n) = 1 / (64 * (2 * (n : ℝ) + 1)) := by
    apply (Real.sqrt_eq_iff_eq_sq (delta_pos n).le (by positivity)).mpr
    unfold delta
    field_simp
    ring
  have hpow : delta n ^ (3 / 2 : ℝ) = delta n / (64 * (2 * (n : ℝ) + 1)) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (delta_pos n),
      Real.rpow_one, ← Real.sqrt_eq_rpow, hsqrt]
    ring
  rw [hpow, growth, show 384 * (delta n / (64 * (2 * (n : ℝ) + 1))) =
    (6 * delta n) / (2 * (n : ℝ) + 1) by field_simp; ring]
  apply (div_le_div_iff₀ hnpos hKpos).mpr
  have hm := mul_le_mul_of_nonneg_left (show 2 * (n : ℝ) + 1 ≤ 3 * n by linarith)
    (delta_pos n).le
  nlinarith

/-- Adjacent near-one lines have comparable displacements, paying the
continuous interval between them with an absolute factor. -/
theorem delta_le_four_succ {n : ℕ} (hn : 1 ≤ n) : delta n ≤ 4 * delta (n + 1) := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [delta, Nat.cast_add, Nat.cast_one]
  rw [← mul_div_assoc, mul_one]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

/-- Both moment orders pay the enlarged displacement. The finitely many
smaller degrees use the four-block saving, and all larger degrees use
three blocks; no gap between those regimes is omitted. -/
theorem saving_ge {n k : ℕ} (hn : 48 ≤ n) (hk : 12 ≤ k) (hkn : k ≤ 2 * n + 1) :
    2 * delta n ≤ VinogradovShortResonance.saving k / 4 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hnr : (48 : ℝ) ≤ n := by exact_mod_cast hn
  have he : 2 * delta n = 1 / (2048 * (2 * (n : ℝ) + 1) ^ 2) := by
    unfold delta
    field_simp
    ring
  rw [he]
  unfold VinogradovShortResonance.saving
  split_ifs with hk48
  · have hkr : (k : ℝ) ≤ 2 * (n : ℝ) + 1 := by exact_mod_cast hkn
    have hsq : (k : ℝ) ^ 2 ≤ (2 * (n : ℝ) + 1) ^ 2 := by nlinarith
    have h := one_div_le_one_div_of_le
      (by positivity : 0 < 2048 * (k : ℝ) ^ 2)
      (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 2048))
    calc
      _ ≤ 1 / (2048 * (k : ℝ) ^ 2) := h
      _ = 1 / (512 * (k : ℝ) ^ 2) / 4 := by field_simp; norm_num
  · have hkr : (k : ℝ) ≤ 48 := by exact_mod_cast (show k ≤ 48 by omega)
    have hsq : (k : ℝ) ^ 2 ≤ (48 : ℝ) ^ 2 := by nlinarith
    have hden : 6400 * (k : ℝ) ^ 2 ≤ 2048 * (2 * (n : ℝ) + 1) ^ 2 := by nlinarith
    have h := one_div_le_one_div_of_le (by positivity : 0 < 6400 * (k : ℝ) ^ 2) hden
    calc
      _ ≤ 1 / (6400 * (k : ℝ) ^ 2) := h
      _ = 1 / (1600 * (k : ℝ) ^ 2) / 4 := by field_simp; norm_num

/-- Every actual middle block is bounded by eight, without supplied
moment, degree or fourth-root hypotheses. -/
theorem middle_block_bound (n j : ℕ) (hn : 48 ≤ n) {s : ℂ}
    (hline : line n ≤ s.re) (ht : (heightThreshold n : ℝ) ≤ s.im)
    (hlo : s.im ^ (2 / (n : ℝ)) ≤ ((2 ^ j : ℕ) : ℝ))
    (hhi : ((2 ^ j : ℕ) : ℝ) ≤ s.im ^ (2 / 11 : ℝ)) : ‖block s j‖ ≤ 8 := by
  obtain ⟨k, M, hk, hkn, hkr, hMX, hXM, hkt, htk⟩ :=
    exists_window_parameters n (2 ^ j) (by omega) ht hlo hhi
  have hσ := (line_bounds n).1.trans hline
  have h := VinogradovShortDyadic.dyadic_block_bound k M j hk (by nlinarith) hMX hXM s
    (by linarith) hkt htk
  have hsaving := saving_ge hn hk hkn
  have hdelta := delta_pos n
  have hlead : 1 - s.re - VinogradovShortResonance.saving k / 4 ≤ 0 := by
    dsimp only [line] at hline
    linarith
  have hX : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    exact_mod_cast one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))
  have hp := Real.rpow_le_one_of_one_le_of_nonpos hX hlead
  have hp' := Real.rpow_le_one_of_one_le_of_nonpos hX (show 1 / 2 - s.re ≤ 0 by linarith)
  linarith

/-- All original dyadic blocks through 4t satisfy one explicit bound.
The four scale cases exhaust the range and retain both analytic errors. -/
theorem block_bound (n j : ℕ) (hn : 48 ≤ n) {s : ℂ} (hline : line n ≤ s.re)
    (ht : (heightThreshold n : ℝ) ≤ s.im)
    (hX : ((2 ^ j : ℕ) : ℝ) ≤ 4 * s.im) :
    ‖block s j‖ ≤ 512 * s.im ^ growth n := by
  have hbT : (rootBase n : ℝ) ≤ heightThreshold n := by
    exact_mod_cast rootBase_le_heightThreshold (show 1 ≤ n by omega)
  have hb : (16 : ℝ) ≤ rootBase n := by exact_mod_cast rootBase_ge_sixteen n
  have ht1 : 1 ≤ s.im := by linarith
  have htpos : 0 < s.im := by linarith
  have hσ : 0 ≤ s.re := by linarith [(line_bounds n).1]
  have hXone : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    exact_mod_cast one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))
  have hg : 1 ≤ s.im ^ growth n := Real.one_le_rpow ht1 (growth_pos (by omega : 1 ≤ n)).le
  by_cases hx : ((2 ^ j : ℕ) : ℝ) ≤ s.im ^ (2 / (n : ℝ))
  · have h := ZetaDyadicPowerBound.trivial_block_bound hσ j
    have he : ((2 ^ j : ℕ) : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ (-s.re) =
        ((2 ^ j : ℕ) : ℝ) ^ (1 - s.re) := by
      rw [sub_eq_add_neg, Real.rpow_add (by positivity), Real.rpow_one]
    rw [he] at h
    have hdelta : 1 - s.re ≤ delta n := by dsimp only [line] at hline; linarith
    have hdamp := Real.rpow_le_rpow_of_exponent_le hXone hdelta
    have hp := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ))
      hx (delta_pos n).le
    rw [← Real.rpow_mul htpos.le, show 2 / (n : ℝ) * delta n = growth n by
      unfold growth; ring] at hp
    exact ((h.trans hdamp).trans hp).trans (by nlinarith)
  · by_cases hx' : ((2 ^ j : ℕ) : ℝ) ≤ s.im ^ (2 / 11 : ℝ)
    · exact (middle_block_bound n j hn hline ht (lt_of_not_ge hx).le hx').trans (by nlinarith)
    · by_cases hx'' : ((2 ^ j : ℕ) : ℝ) ≤ s.im ^ (1 / 3 : ℝ)
      · have h := DirichletBlockPowerProfile.bound 4 j hσ htpos
        have hp := VinogradovLongBlocks.sixth_profile_le (delta_pos n).le (delta_le n)
          ht1 (lt_of_not_ge hx').le hx''
        have hm := VinogradovLongBlocks.profile_antitone_sigma 4 htpos.le hXone hline
        exact ((h.trans hm).trans hp).trans (by nlinarith)
      · have h := DirichletBlockPowerProfile.bound 2 j hσ htpos
        have hp := VinogradovLongBlocks.fourth_profile_le (delta_pos n).le (delta_le n)
          ht1 (lt_of_not_ge hx'').le hX
        have hm := VinogradovLongBlocks.profile_antitone_sigma 2 htpos.le hXone hline
        exact ((h.trans hm).trans hp).trans (by nlinarith)

/-- Every block in the literal canonical zeta reconstruction is paid;
its scale condition follows from the existing cutoff theorem. -/
theorem canonical_block_bound (n : ℕ) (hn : 48 ≤ n) {s : ℂ}
    (hline : line n ≤ s.re) (hσ1 : s.re ≤ 1)
    (ht : (heightThreshold n : ℝ) ≤ s.im) {j : ℕ} (hj : j ≤ ZetaDyadicTruncation.depth s) :
    ‖block s j‖ ≤ 512 * s.im ^ growth n := by
  have hσ := (line_bounds n).1.trans hline
  have hbT : (rootBase n : ℝ) ≤ heightThreshold n := by
    exact_mod_cast rootBase_le_heightThreshold (show 1 ≤ n by omega)
  have hb : (16 : ℝ) ≤ rootBase n := by exact_mod_cast rootBase_ge_sixteen n
  exact block_bound n j hn hline ht
    (ZetaNearOneLineBudget.canonical_scale_le (by linarith) hσ1 (by linarith) hj)

end
end RiemannGaussian.VinogradovSharperBudget
