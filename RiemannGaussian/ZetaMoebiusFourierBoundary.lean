/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusFourierResonance

/-!
# Decay of the Fourier boundary cost with its full arithmetic energy

The upper endpoint estimate absorbs the complete finite arithmetic
majorant, uniformly in the moving divisor cutoff and ordinate. Thus the
cyclic endpoint contributes a geometrically vanishing squared budget even
after multiplication by the arithmetic energy. This does not estimate
the interior difference energy or the resonant interaction.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The complete coefficient allowance for the upper band endpoint. -/
def zetaMoebiusFourierBoundaryConstant (p : Polynomial ℂ) : ℝ :=
  (∑ k ∈ p.support, ‖p.coeff k‖ * (8 : ℝ) ^ k) * zetaMoebiusLogMajorantMass (5 / 4)

private theorem kernel_upper_bound (p : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    ‖zetaPrimeFilterKernel p N (3 / 2 + I * y) (2 ^ (32 * N) : ℕ)‖ ≤
      (1 / 2 : ℝ) ^ N * (∑ k ∈ p.support, ‖p.coeff k‖ * (8 : ℝ) ^ k) *
        zetaPrimeExpWeight (5 / 4) (2 ^ (32 * N)) := by
  have hl : 32 * (N : ℝ) * Real.log 2 ≤ Real.log ((2 ^ (32 * N) : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    push_cast
    exact le_rfl
  have he : zetaPrimeFilterKernel p N (3 / 2 + I * y) (2 ^ (32 * N) : ℕ) =
      ∑ k ∈ p.support, p.coeff k * zetaPrimeLogKernel (N + k) (3 / 2 + I * y) (2 ^ (32 * N)) := by
    rw [zetaPrimeFilterKernel_nat]
    simp only [zetaPrimeLogKernel, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k ∈ p.support, ‖p.coeff k‖ * ((1 / 2 : ℝ) ^ N * 8 ^ k *
        zetaPrimeExpWeight (5 / 4) (2 ^ (32 * N))) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_zetaPrimeLogKernel_le_upper_band N k _ y hl)
        (norm_nonneg _)
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- The endpoint absorbs the entire positive arithmetic first mass,
not just one coefficient or a fixed divisor cutoff. -/
theorem sum_zetaMoebiusLogMajorant_mul_norm_upper_le (p : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    (∑ n ∈ zetaPrimeLogBand N, zetaMoebiusLogMajorant n) *
        ‖zetaPrimeFilterKernel p N (3 / 2 + I * y) (2 ^ (32 * N) : ℕ)‖ ≤
      (1 / 2 : ℝ) ^ N * zetaMoebiusFourierBoundaryConstant p := by
  have hc : 0 ≤ (∑ k ∈ p.support, ‖p.coeff k‖ * (8 : ℝ) ^ k) :=
    Finset.sum_nonneg (fun _ _ ↦ by positivity)
  have hs : (∑ n ∈ zetaPrimeLogBand N,
      zetaMoebiusLogMajorant n * zetaPrimeExpWeight (5 / 4) n) ≤
        zetaMoebiusLogMajorantMass (5 / 4) :=
    Summable.sum_le_tsum (zetaPrimeLogBand N)
      (fun n _ ↦ mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (Real.exp_pos _).le)
      (summable_zetaMoebiusLogMajorant (by norm_num))
  calc
    _ = ∑ n ∈ zetaPrimeLogBand N, zetaMoebiusLogMajorant n *
        ‖zetaPrimeFilterKernel p N (3 / 2 + I * y) (2 ^ (32 * N) : ℕ)‖ := by rw [Finset.sum_mul]
    _ ≤ ∑ n ∈ zetaPrimeLogBand N, zetaMoebiusLogMajorant n *
        ((1 / 2 : ℝ) ^ N * (∑ k ∈ p.support, ‖p.coeff k‖ * (8 : ℝ) ^ k) *
          zetaPrimeExpWeight (5 / 4) n) := by
      apply Finset.sum_le_sum
      intro n hn
      have hni := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hl := Real.log_le_log hn0
        (by exact_mod_cast hni.2 : (n : ℝ) ≤ ((2 ^ (32 * N) : ℕ) : ℝ))
      have hw : zetaPrimeExpWeight (5 / 4) (2 ^ (32 * N)) ≤ zetaPrimeExpWeight (5 / 4) n := by
        apply Real.exp_le_exp.mpr
        linarith
      apply mul_le_mul_of_nonneg_left _ (zetaMoebiusLogMajorant_nonneg n)
      exact (kernel_upper_bound p N y).trans (mul_le_mul_of_nonneg_left hw (by positivity))
    _ = (1 / 2 : ℝ) ^ N * (∑ k ∈ p.support, ‖p.coeff k‖ * (8 : ℝ) ^ k) *
        ∑ n ∈ zetaPrimeLogBand N, zetaMoebiusLogMajorant n * zetaPrimeExpWeight (5 / 4) n := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ ≤ _ := by
      dsimp only [zetaMoebiusFourierBoundaryConstant]
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left hs (by positivity)

/-- The full arithmetic square mass times the exact last sample has a
geometric bound uniform in the cutoff and ordinate. This discharges the
endpoint contribution in the first-difference Fourier energy estimate. -/
theorem zetaMoebiusFourierBoundary_energy_le (p : Polynomial ℂ) (D N : ℕ) (y : ℝ) :
    (∑ n ∈ zetaPrimeLogBand N, ‖zetaMoebiusLogTailCoefficient D n‖ ^ 2) *
        ‖zetaPrimeFilterKernel p N (3 / 2 + I * y) (2 ^ (32 * N) : ℕ)‖ ^ 2 ≤
      ((1 / 2 : ℝ) ^ N * zetaMoebiusFourierBoundaryConstant p) ^ 2 := by
  have hs : (∑ n ∈ zetaPrimeLogBand N, ‖zetaMoebiusLogTailCoefficient D n‖ ^ 2) ≤
      (∑ n ∈ zetaPrimeLogBand N, zetaMoebiusLogMajorant n) ^ 2 := by
    apply (Finset.sum_le_sum (fun n _ ↦ pow_le_pow_left₀ (norm_nonneg _)
      (norm_zetaMoebiusLogTailCoefficient_le D n) 2)).trans
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun n _ ↦ zetaMoebiusLogMajorant_nonneg n)
  calc
    _ ≤ (∑ n ∈ zetaPrimeLogBand N, zetaMoebiusLogMajorant n) ^ 2 *
        ‖zetaPrimeFilterKernel p N (3 / 2 + I * y) (2 ^ (32 * N) : ℕ)‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hs (sq_nonneg _)
    _ = ((∑ n ∈ zetaPrimeLogBand N, zetaMoebiusLogMajorant n) *
        ‖zetaPrimeFilterKernel p N (3 / 2 + I * y) (2 ^ (32 * N) : ℕ)‖) ^ 2 := by rw [mul_pow]
    _ ≤ _ := pow_le_pow_left₀ (mul_nonneg
      (Finset.sum_nonneg (fun n _ ↦ zetaMoebiusLogMajorant_nonneg n)) (norm_nonneg _))
      (sum_zetaMoebiusLogMajorant_mul_norm_upper_le p N y) 2

/-- The boundary budget vanishes for arbitrary moving cutoffs and
ordinates. The interior Fourier energy is a separate remaining obligation. -/
theorem tendsto_zetaMoebiusFourierBoundary_energy (p : Polynomial ℂ) (D : ℕ → ℕ) (y : ℕ → ℝ) :
    Tendsto (fun N ↦ (∑ n ∈ zetaPrimeLogBand N, ‖zetaMoebiusLogTailCoefficient (D N) n‖ ^ 2) *
      ‖zetaPrimeFilterKernel p N (3 / 2 + I * y N) (2 ^ (32 * N) : ℕ)‖ ^ 2)
      atTop (𝓝 0) := by
  have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (zetaMoebiusFourierBoundaryConstant p)).pow 2
  apply squeeze_zero (fun N ↦ mul_nonneg (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)) (sq_nonneg _))
    (fun N ↦ zetaMoebiusFourierBoundary_energy_le p (D N) N (y N))
  simpa using h

end
end RiemannGaussian
