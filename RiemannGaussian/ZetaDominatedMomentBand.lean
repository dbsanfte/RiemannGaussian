/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusMomentBand

/-!
# Uniform logarithmic-band control for dominated arithmetic coefficients

Every complex coefficient family bounded by the original divisor majorant
has genuinely summable filtered moments and the same geometric band-tail
estimate. This allows arithmetic support restrictions to pass through
the finite-band reduction without losing their signs or phases.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The genuine arithmetic moment of an arbitrary complex coefficient sequence. -/
def zetaArithmeticMoment (a : ℕ → ℂ) (k : ℕ) (s : ℂ) : ℂ :=
  ∑' n, a n * zetaPrimeLogKernel k s n

/-- The whole arithmetic sum with its original polynomial kernel. -/
def zetaArithmeticFilter (a : ℕ → ℂ) (p : Polynomial ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑' n, a n * zetaPrimeFilterKernel p N s n

/-- The same signed arithmetic sum restricted to the original logarithmic band. -/
def zetaArithmeticBand (a : ℕ → ℂ) (p : Polynomial ℂ) (N : ℕ) (y : ℝ) : ℂ :=
  ∑ n ∈ zetaPrimeLogBand N, a n * zetaPrimeFilterKernel p N (3 / 2 + I * y) n

/-- Domination by the literal divisor majorant gives genuine summability
of every logarithmic moment throughout the Euler half-plane. -/
theorem summable_zetaDominatedMoment (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ zetaMoebiusLogMajorant n) (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n ↦ a n * zetaPrimeLogKernel k s n) := by
  let q := (s.re - 1) / 2
  have hq : 0 < q := by dsimp [q]; linarith
  have hσ : 1 < s.re - q := by dsimp [q]; linarith
  apply ((summable_zetaMoebiusLogMajorant hσ).mul_left (q⁻¹ ^ k)).of_norm_bounded
  intro n
  rw [norm_mul]
  exact (mul_le_mul (ha n) (norm_zetaPrimeLogKernel_le k s n hq)
    (norm_nonneg _) (zetaMoebiusLogMajorant_nonneg n)).trans_eq (by ring)

/-- All finite polynomial channels combine into one genuinely convergent
arithmetic series, without interchanging any unproved infinite limits. -/
theorem hasSum_zetaDominatedFilter (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ zetaMoebiusLogMajorant n) (p : Polynomial ℂ) (N : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ a n * zetaPrimeFilterKernel p N s n)
      (∑ k ∈ p.support, p.coeff k * zetaArithmeticMoment a (N + k) s) := by
  have h := hasSum_sum (s := p.support) (fun k _ ↦
    (summable_zetaDominatedMoment a ha (N + k) hs).hasSum.mul_left (p.coeff k))
  apply h.congr_fun
  intro n
  rw [zetaPrimeFilterKernel_nat, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  unfold zetaPrimeLogKernel
  ring

private theorem norm_atom_le_outside (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ zetaMoebiusLogMajorant n) (N k n : ℕ) (y : ℝ)
    (hn : n ∉ zetaPrimeLogBand N) :
    ‖a n * zetaPrimeLogKernel (N + k) (3 / 2 + I * y) n‖ ≤
      (1 / 2 : ℝ) ^ N *
        ((1 / 4 : ℝ) ^ k * (zetaMoebiusLogMajorant n * zetaPrimeExpWeight (3 / 2) n) +
          (8 : ℝ) ^ k * (zetaMoebiusLogMajorant n * zetaPrimeExpWeight (5 / 4) n)) := by
  have hw (σ : ℝ) : 0 ≤ zetaMoebiusLogMajorant n * zetaPrimeExpWeight σ n :=
    mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (Real.exp_pos _).le
  by_cases hn0 : n = 0
  · subst n
    have ha0 : a 0 = 0 := norm_eq_zero.mp (le_antisymm (by simpa [zetaMoebiusLogMajorant] using ha 0)
      (norm_nonneg _))
    simp [ha0, zetaMoebiusLogMajorant]
  rw [norm_mul]
  rcases zetaPrimeLogBand_complement N hn0 hn with hl | hu
  · have hb := norm_zetaPrimeLogKernel_le_lower_band N k n (3 / 2 + I * y) hl
    have hs : (3 / 2 + I * (y : ℂ)).re = (3 / 2 : ℝ) := by norm_num
    rw [hs] at hb
    have h := mul_le_mul (ha n) hb (norm_nonneg _) (zetaMoebiusLogMajorant_nonneg n)
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (1 / 2) ^ N * 8 ^ k by positivity) (hw (5 / 4))]
  · have h := mul_le_mul (ha n) (norm_zetaPrimeLogKernel_le_upper_band N k n y hu)
      (norm_nonneg _) (zetaMoebiusLogMajorant_nonneg n)
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (1 / 2) ^ N * (1 / 4) ^ k by positivity) (hw (3 / 2))]

private theorem tsum_sub_sum_eq_complement {f : ℕ → ℂ} (hf : Summable f) (S : Finset ℕ) :
    (∑' n, f n) - ∑ n ∈ S, f n = ∑' n, if n ∈ S then 0 else f n := by
  have h := hf.sum_add_tsum_compl (s := S)
  rw [tsum_subtype] at h
  have he : ((S : Set ℕ)ᶜ).indicator f = (fun n ↦ if n ∈ S then 0 else f n) := by
    funext n
    by_cases hn : n ∈ S <;> simp [hn]
  rw [he] at h
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using h.symm)

/-- Both omitted tails obey one geometric bound, uniformly over every
complex coefficient family with the original arithmetic majorant. -/
theorem norm_zetaDominatedMoment_sub_band_le (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ zetaMoebiusLogMajorant n) (N k : ℕ) (y : ℝ) :
    ‖zetaArithmeticMoment a (N + k) (3 / 2 + I * y) -
      ∑ n ∈ zetaPrimeLogBand N, a n * zetaPrimeLogKernel (N + k) (3 / 2 + I * y) n‖ ≤
      (1 / 2 : ℝ) ^ N *
        ((1 / 4 : ℝ) ^ k * zetaMoebiusLogMajorantMass (3 / 2) +
          (8 : ℝ) ^ k * zetaMoebiusLogMajorantMass (5 / 4)) := by
  let f (n : ℕ) : ℂ := a n * zetaPrimeLogKernel (N + k) (3 / 2 + I * y) n
  have hsum : Summable f := summable_zetaDominatedMoment a ha (N + k) (by norm_num)
  have ht : Summable (fun n ↦ if n ∈ zetaPrimeLogBand N then 0 else f n) := by
    apply (hsum.indicator ((zetaPrimeLogBand N : Set ℕ)ᶜ)).congr
    intro n
    by_cases hn : n ∈ zetaPrimeLogBand N <;> simp [hn]
  have h1 := summable_zetaMoebiusLogMajorant (by norm_num : (1 : ℝ) < 3 / 2)
  have h2 := summable_zetaMoebiusLogMajorant (by norm_num : (1 : ℝ) < 5 / 4)
  have hmajor := ((h1.mul_left ((1 / 4 : ℝ) ^ k)).add
    (h2.mul_left ((8 : ℝ) ^ k))).mul_left ((1 / 2 : ℝ) ^ N)
  change ‖(∑' n, f n) - ∑ n ∈ zetaPrimeLogBand N, f n‖ ≤ _
  rw [tsum_sub_sum_eq_complement hsum]
  calc
    _ ≤ ∑' n, (1 / 2 : ℝ) ^ N *
        ((1 / 4 : ℝ) ^ k * (zetaMoebiusLogMajorant n * zetaPrimeExpWeight (3 / 2) n) +
          (8 : ℝ) ^ k * (zetaMoebiusLogMajorant n * zetaPrimeExpWeight (5 / 4) n)) := by
      apply (norm_tsum_le_tsum_norm ht.norm).trans
      apply Summable.tsum_le_tsum _ ht.norm hmajor
      intro n
      by_cases hn : n ∈ zetaPrimeLogBand N
      · rw [if_pos hn, norm_zero]
        exact mul_nonneg (by positivity) (add_nonneg
          (mul_nonneg (by positivity) (mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (Real.exp_pos _).le))
          (mul_nonneg (by positivity) (mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (Real.exp_pos _).le)))
      · rw [if_neg hn]
        exact norm_atom_le_outside a ha N k n y hn
    _ = _ := by
      rw [tsum_mul_left, (h1.mul_left _).tsum_add (h2.mul_left _), tsum_mul_left, tsum_mul_left]
      rfl

/-- The entire original polynomial kernel is retained in the finite
band, with the same independent tail allowance for all dominated families. -/
theorem norm_zetaDominatedFilter_sub_band_le (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ zetaMoebiusLogMajorant n) (p : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    ‖zetaArithmeticFilter a p N (3 / 2 + I * y) - zetaArithmeticBand a p N y‖ ≤
      (1 / 2 : ℝ) ^ N * zetaMoebiusBandTailConstant p := by
  have hb : zetaArithmeticBand a p N y = ∑ k ∈ p.support, p.coeff k *
      ∑ n ∈ zetaPrimeLogBand N, a n * zetaPrimeLogKernel (N + k) (3 / 2 + I * y) n := by
    simp only [zetaArithmeticBand, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n _
    rw [zetaPrimeFilterKernel_nat, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    unfold zetaPrimeLogKernel
    ring
  rw [zetaArithmeticFilter, (hasSum_zetaDominatedFilter a ha p N (by norm_num)).tsum_eq, hb]
  simp only [← Finset.sum_sub_distrib, ← mul_sub]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k ∈ p.support, ‖p.coeff k‖ * ((1 / 2 : ℝ) ^ N *
        ((1 / 4 : ℝ) ^ k * zetaMoebiusLogMajorantMass (3 / 2) +
          (8 : ℝ) ^ k * zetaMoebiusLogMajorantMass (5 / 4))) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_zetaDominatedMoment_sub_band_le a ha N k y) (norm_nonneg _)
    _ = _ := by
      rw [zetaMoebiusBandTailConstant, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- Arbitrarily changing dominated coefficient families share the same
vanishing band error; no arithmetic support restriction is discarded. -/
theorem tendsto_zetaDominatedFilter_sub_band (a : ℕ → ℕ → ℂ)
    (ha : ∀ N n, ‖a N n‖ ≤ zetaMoebiusLogMajorant n) (p : Polynomial ℂ) (y : ℝ) :
    Tendsto (fun N ↦ zetaArithmeticFilter (a N) p N (3 / 2 + I * y) -
      zetaArithmeticBand (a N) p N y) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun N ↦ norm_zetaDominatedFilter_sub_band_le (a N) (ha N) p N y)
  simpa only [zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (zetaMoebiusBandTailConstant p)

end
end RiemannGaussian
