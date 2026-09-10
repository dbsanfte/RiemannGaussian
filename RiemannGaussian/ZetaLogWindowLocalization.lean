/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaLogMomentTilt

/-!
# Uniform arithmetic localization in a smaller logarithmic window

Every dominated complex coefficient family can be restricted to
`2*N/5 <= log n <= 8*N`, with two explicitly decaying errors. This includes
arbitrarily moving Möbius cutoffs and arithmetic sieves. The complete
polynomial kernel and the signs inside the retained window are unchanged.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian
noncomputable section

/-- The retained logarithmic window, before any integer rounding. -/
def zetaLogWindow (N : ℕ) : Set ℕ :=
  {n | (2 / 5 : ℝ) * N ≤ Real.log n ∧ Real.log n ≤ (8 : ℝ) * N}

/-- Restriction preserves each complete complex coefficient inside
the window. All original coefficient signs and phases remain available. -/
def zetaLogWindowCoefficient (a : ℕ → ℂ) (N n : ℕ) : ℂ :=
  if n ∈ zetaLogWindow N then a n else 0

/-- Window restriction preserves the original arithmetic majorant. -/
theorem norm_zetaLogWindowCoefficient_le (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ zetaMoebiusLogMajorant n) (N n : ℕ) :
    ‖zetaLogWindowCoefficient a N n‖ ≤ zetaMoebiusLogMajorant n := by
  unfold zetaLogWindowCoefficient
  split_ifs
  · exact ha n
  · simpa using zetaMoebiusLogMajorant_nonneg n

/-- Real arithmetic coefficients remain real after exact restriction. -/
theorem zetaLogWindowCoefficient_im (a : ℕ → ℂ) (ha : ∀ n, (a n).im = 0)
    (N n : ℕ) : (zetaLogWindowCoefficient a N n).im = 0 := by
  unfold zetaLogWindowCoefficient
  split_ifs <;> simp [ha]

private theorem norm_removed_atom_le (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ zetaMoebiusLogMajorant n) (N k n : ℕ) (y : ℝ) :
    ‖a n * zetaPrimeLogKernel (N + k) (3 / 2 + I * y) n -
      zetaLogWindowCoefficient a N n * zetaPrimeLogKernel (N + k) (3 / 2 + I * y) n‖ ≤
      ((15 / 16 : ℝ) ^ N * (1 / 2 : ℝ) ^ k + (3 / 4 : ℝ) ^ N * (8 : ℝ) ^ k) *
        (zetaMoebiusLogMajorant n * zetaPrimeExpWeight (17 / 16) n) := by
  have hw : 0 ≤ zetaMoebiusLogMajorant n * zetaPrimeExpWeight (17 / 16) n :=
    mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (Real.exp_pos _).le
  by_cases hn : n ∈ zetaLogWindow N
  · simp only [zetaLogWindowCoefficient, if_pos hn, sub_self, norm_zero]
    exact mul_nonneg (by positivity) hw
  · simp only [zetaLogWindowCoefficient, if_neg hn, zero_mul, sub_zero, norm_mul]
    by_cases hl : Real.log n ≤ (2 / 5 : ℝ) * N
    · have hb := mul_le_mul (ha n)
        (norm_zetaPrimeLogKernel_le_lower_window N k n y hl)
        (norm_nonneg _) (zetaMoebiusLogMajorant_nonneg n)
      have hpos := mul_nonneg (show 0 ≤ (3 / 4 : ℝ) ^ N * (8 : ℝ) ^ k by positivity) hw
      nlinarith only [hb, hpos]
    · have hu : (8 : ℝ) * N ≤ Real.log n := by
        have hn' : ¬((2 / 5 : ℝ) * N ≤ Real.log n ∧ Real.log n ≤ (8 : ℝ) * N) := hn
        by_contra! h
        exact hn' ⟨(lt_of_not_ge hl).le, h.le⟩
      have hb := mul_le_mul (ha n)
        (norm_zetaPrimeLogKernel_le_upper_window N k n y hu)
        (norm_nonneg _) (zetaMoebiusLogMajorant_nonneg n)
      have hpos := mul_nonneg (show 0 ≤ (15 / 16 : ℝ) ^ N * (1 / 2 : ℝ) ^ k by positivity) hw
      nlinarith only [hb, hpos]

/-- Both omitted arithmetic shells have one explicit bound, uniformly
over every dominated complex coefficient family and every ordinate. -/
theorem norm_zetaArithmeticMoment_sub_window_le (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ zetaMoebiusLogMajorant n) (N k : ℕ) (y : ℝ) :
    ‖zetaArithmeticMoment a (N + k) (3 / 2 + I * y) -
      zetaArithmeticMoment (zetaLogWindowCoefficient a N) (N + k) (3 / 2 + I * y)‖ ≤
      ((15 / 16 : ℝ) ^ N * (1 / 2 : ℝ) ^ k + (3 / 4 : ℝ) ^ N * (8 : ℝ) ^ k) *
        zetaMoebiusLogMajorantMass (17 / 16) := by
  have h1 := summable_zetaDominatedMoment a ha (N + k) (s := 3 / 2 + I * y) (by norm_num)
  have h2 := summable_zetaDominatedMoment (zetaLogWindowCoefficient a N)
    (norm_zetaLogWindowCoefficient_le a ha N) (N + k) (s := 3 / 2 + I * y) (by norm_num)
  have hm := (summable_zetaMoebiusLogMajorant (by norm_num : (1 : ℝ) < 17 / 16)).mul_left
    ((15 / 16 : ℝ) ^ N * (1 / 2 : ℝ) ^ k + (3 / 4 : ℝ) ^ N * (8 : ℝ) ^ k)
  unfold zetaArithmeticMoment
  rw [← h1.tsum_sub h2]
  calc
    _ ≤ ∑' n, ((15 / 16 : ℝ) ^ N * (1 / 2 : ℝ) ^ k + (3 / 4 : ℝ) ^ N * (8 : ℝ) ^ k) *
        (zetaMoebiusLogMajorant n * zetaPrimeExpWeight (17 / 16) n) :=
      (norm_tsum_le_tsum_norm (h1.sub h2).norm).trans
        ((h1.sub h2).norm.tsum_le_tsum (fun n ↦ norm_removed_atom_le a ha N k n y) hm)
    _ = _ := by rw [tsum_mul_left]; rfl

/-- The complete independently controlled error from the two omitted
shells, including every polynomial coefficient and offset moment. -/
def zetaLogWindowError (p : Polynomial ℂ) (N : ℕ) : ℝ :=
  ∑ k ∈ p.support, ‖p.coeff k‖ *
    (((15 / 16 : ℝ) ^ N * (1 / 2 : ℝ) ^ k + (3 / 4 : ℝ) ^ N * (8 : ℝ) ^ k) *
      zetaMoebiusLogMajorantMass (17 / 16))

/-- The full discarded-shell allowance is nonnegative. -/
theorem zetaLogWindowError_nonneg (p : Polynomial ℂ) (N : ℕ) :
    0 ≤ zetaLogWindowError p N := by
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (norm_nonneg _) (mul_nonneg (by positivity) (zetaMoebiusLogMajorantMass_nonneg _))

/-- The whole original complex polynomial filter is localized with
its full signed coefficients unchanged on the smaller window. -/
theorem norm_zetaArithmeticFilter_sub_window_le (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ zetaMoebiusLogMajorant n) (p : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    ‖zetaArithmeticFilter a p N (3 / 2 + I * y) -
      zetaArithmeticFilter (zetaLogWindowCoefficient a N) p N (3 / 2 + I * y)‖ ≤
      zetaLogWindowError p N := by
  unfold zetaArithmeticFilter
  rw [(hasSum_zetaDominatedFilter a ha p N (by norm_num)).tsum_eq,
    (hasSum_zetaDominatedFilter (zetaLogWindowCoefficient a N)
      (norm_zetaLogWindowCoefficient_le a ha N) p N (by norm_num)).tsum_eq]
  simp only [← Finset.sum_sub_distrib, ← mul_sub]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_zetaArithmeticMoment_sub_window_le a ha N k y) (norm_nonneg _)

/-- The complete error tends to zero without any normalization by a
hypothetical zero source. Both geometric rates are strictly below one. -/
theorem tendsto_zetaLogWindowError (p : Polynomial ℂ) :
    Tendsto (zetaLogWindowError p) atTop (𝓝 0) := by
  unfold zetaLogWindowError
  have h1 := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 15 / 16) (by norm_num : (15 / 16 : ℝ) < 1)
  have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)
  have h := tendsto_finsetSum p.support (fun k _ ↦
    (((h1.mul_const ((1 / 2 : ℝ) ^ k)).add (h2.mul_const ((8 : ℝ) ^ k))).mul_const
      (zetaMoebiusLogMajorantMass (17 / 16))).const_mul ‖p.coeff k‖)
  simpa only [zero_mul, zero_add, mul_zero, Finset.sum_const_zero] using h

/-- Arbitrarily moving dominated families share the same vanishing
shell error; no condition on the cutoff or sieve schedule is needed. -/
theorem tendsto_zetaArithmeticFilter_sub_window (a : ℕ → ℕ → ℂ)
    (ha : ∀ N n, ‖a N n‖ ≤ zetaMoebiusLogMajorant n) (p : Polynomial ℂ) (y : ℝ) :
    Tendsto (fun N ↦ zetaArithmeticFilter (a N) p N (3 / 2 + I * y) -
      zetaArithmeticFilter (zetaLogWindowCoefficient (a N) N) p N (3 / 2 + I * y))
      atTop (𝓝 0) :=
  squeeze_zero_norm (fun N ↦ norm_zetaArithmeticFilter_sub_window_le (a N) (ha N) p N y)
    (tendsto_zetaLogWindowError p)

/-- At positive orders the smaller logarithmic window lies inside the
old finite band. This proves the retained arithmetic is genuinely finite. -/
theorem zetaLogWindow_subset_band {N : ℕ} (hN : 1 ≤ N) :
    zetaLogWindow N ⊆ (zetaPrimeLogBand N : Set ℕ) := by
  intro n hn
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hn0 : n ≠ 0 := by
    intro he
    subst n
    have h := hn.1
    norm_num at h
    nlinarith
  have hlog : (N : ℝ) * Real.log 2 / 4 < Real.log n := by
    have h := mul_lt_mul_of_pos_right Real.log_two_lt_d9 hNr
    nlinarith [hn.1]
  have hu : n ≤ 2 ^ (32 * N) := by
    have hx : Real.log (n : ℝ) ≤ Real.log ((2 : ℝ) ^ (32 * N)) := by
      rw [Real.log_pow]
      push_cast
      have h := mul_le_mul_of_nonneg_right Real.log_two_gt_d9.le hNr.le
      nlinarith [hn.2]
    have he := Real.exp_le_exp.mpr hx
    rw [Real.exp_log (by exact_mod_cast Nat.pos_of_ne_zero hn0 : (0 : ℝ) < n),
      Real.exp_log (by positivity : (0 : ℝ) < 2 ^ (32 * N))] at he
    exact_mod_cast he
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hu⟩, hlog⟩

/-- The retained infinite notation equals its actual finite band sum;
the support restriction is exact and incurs no further tail error. -/
theorem zetaArithmeticFilter_window_eq_band (a : ℕ → ℂ) (p : Polynomial ℂ)
    (N : ℕ) (y : ℝ) (hN : 1 ≤ N) :
    zetaArithmeticFilter (zetaLogWindowCoefficient a N) p N (3 / 2 + I * y) =
      zetaArithmeticBand (zetaLogWindowCoefficient a N) p N y := by
  unfold zetaArithmeticFilter zetaArithmeticBand
  apply tsum_eq_sum
  intro n hn
  have hw : n ∉ zetaLogWindow N := fun h ↦ hn (zetaLogWindow_subset_band hN h)
  simp [zetaLogWindowCoefficient, hw]

end
end RiemannGaussian
