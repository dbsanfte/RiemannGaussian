/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiZeroTail

/-!
# A quantitative rate for the actual zeta divisor tail

The existing multiplicity-aware `3/2` Jensen count gives a geometric bound
on dyadic inverse-square shells. We retain the actual height restriction,
sum every shell beyond it, and obtain an inverse-square-root rate. This is
an independent analytic estimate for the zero-tail allowance.
-/

namespace RiemannGaussian.GaussianFermiZeroTailRate

noncomputable section
open Complex Filter Set
open scoped Topology Classical
open GaussianFermiZeroTail

private def normWeight (ρ : NontrivialZetaZero) : ℝ :=
  (analyticZetaZeroMultiplicity ρ : ℝ) / (1 + ‖ρ.1‖ ^ 2)

private theorem normWeight_nonneg (ρ : NontrivialZetaZero) : 0 ≤ normWeight ρ := by
  unfold normWeight
  positivity

private theorem summable_normWeight : Summable normWeight := by
  change Summable (fun ρ : NontrivialZetaZero =>
    (analyticZetaZeroMultiplicity ρ : ℝ) / (1 + ‖ρ.1‖ ^ 2))
  exact summable_distinct_zetaZeroInverseSquareNorm

private theorem divisorWeight_le_twice_normWeight (ρ : NontrivialZetaZero) :
    divisorWeight ρ ≤ 2 * normWeight ρ := by
  have hden := one_add_norm_sq_le_two_mul_one_add_spectral_re_sq ρ
  rw [zetaSpectralCoordinate_re] at hden
  unfold divisorWeight normWeight
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  exact (mul_le_mul_of_nonneg_left hden (Nat.cast_nonneg _)).trans_eq (by ring)

private theorem index_gt_of_height_gt {H : ℝ} {N : ℕ} (hH : (2 : ℝ) ^ N ≤ H)
    (ρ : NontrivialZetaZero) (hρ : H < |ρ.1.im|) : N < zetaZeroNormDyadicIndex ρ := by
  by_contra hn
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (le_of_not_gt hn)
  have hnorm := norm_lt_two_pow_zetaZeroNormDyadicIndex ρ
  have him := Complex.abs_im_le_norm ρ.1
  linarith

private theorem summable_index_tail (N : ℕ) :
    Summable (fun ρ : NontrivialZetaZero =>
      if N < zetaZeroNormDyadicIndex ρ then normWeight ρ else 0) := by
  exact (summable_normWeight.indicator
    {ρ : NontrivialZetaZero | N < zetaZeroNormDyadicIndex ρ}).congr (fun ρ => by
      classical
      by_cases h : N < zetaZeroNormDyadicIndex ρ <;> simp [h])

private theorem summable_majorant_tail (A : ℝ) (N : ℕ) :
    Summable (fun n : ℕ => if N < n then riemannXiInverseSquareDyadicMajorant A n else 0) := by
  exact ((summable_riemannXiInverseSquareDyadicMajorant A).indicator
    {n : ℕ | N < n}).congr (fun n => by
      classical
      by_cases h : N < n <;> simp [h])

/-- The actual height tail is bounded by the full remaining dyadic
majorant. Every analytic multiplicity is retained in the partition. -/
theorem divisorTail_le_majorant_tail {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ, ‖riemannXi z‖ ≤ Real.exp (A * (‖z‖ + 1) ^ (3 / 2 : ℝ)))
    (N : ℕ) {H : ℝ} (hH : (2 : ℝ) ^ N ≤ H) :
    divisorTail H ≤ 2 * ∑' n : ℕ,
      if N < n then riemannXiInverseSquareDyadicMajorant A n else 0 := by
  let f : NontrivialZetaZero → ℝ := fun ρ =>
    if N < zetaZeroNormDyadicIndex ρ then normWeight ρ else 0
  have hf : Summable f := summable_index_tail N
  have hfirst : divisorTail H ≤ 2 * ∑' ρ : NontrivialZetaZero, f ρ := by
    rw [← tsum_mul_left]
    apply (summable_divisorTail_terms H).tsum_le_tsum ?_ (hf.mul_left 2)
    intro ρ
    by_cases hρ : H < |ρ.1.im|
    · simp only [if_pos hρ, f, if_pos (index_gt_of_height_gt hH ρ hρ)]
      exact divisorWeight_le_twice_normWeight ρ
    · simp only [if_neg hρ, f]
      split_ifs <;> positivity [normWeight_nonneg ρ]
  have hpart := hf.hasSum.tsum_fiberwise zetaZeroNormDyadicIndex
  have hparts : (∑' ρ : NontrivialZetaZero, f ρ) ≤ ∑' n : ℕ,
      if N < n then riemannXiInverseSquareDyadicMajorant A n else 0 := by
    rw [← hpart.tsum_eq]
    apply hpart.summable.tsum_le_tsum ?_ (summable_majorant_tail A N)
    intro n
    by_cases hn : N < n
    · rw [if_pos hn]
      calc
        _ = ∑' ρ : {ρ : NontrivialZetaZero | zetaZeroNormDyadicIndex ρ = n},
            normWeight ρ.1 := by
          apply tsum_congr
          intro ρ
          have hρ : zetaZeroNormDyadicIndex ρ.1 = n := ρ.2
          simp only [f, hρ, if_pos hn]
        _ ≤ _ := tsum_zetaZeroNormDyadicShell_inverseSquare_le hA hbound n
    · rw [if_neg hn]
      apply le_of_eq
      calc
        _ = ∑' ρ : zetaZeroNormDyadicIndex ⁻¹' {n}, (0 : ℝ) := by
          apply tsum_congr
          intro ρ
          have hρ : zetaZeroNormDyadicIndex ρ.1 = n := ρ.2
          simp only [f, hρ, if_neg hn]
        _ = 0 := tsum_zero
  exact hfirst.trans (mul_le_mul_of_nonneg_left hparts (by norm_num))

private theorem majorant_tail_eq_shift (A : ℝ) (N : ℕ) :
    (∑' n : ℕ, if N < n then riemannXiInverseSquareDyadicMajorant A n else 0) =
      ∑' k : ℕ, riemannXiInverseSquareDyadicMajorant A (k + (N + 1)) := by
  have hs := (summable_majorant_tail A N).sum_add_tsum_nat_add (N + 1)
  have hzero : (∑ n ∈ Finset.range (N + 1),
      if N < n then riemannXiInverseSquareDyadicMajorant A n else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [if_neg (by have := Finset.mem_range.mp hn; omega)]
  rw [hzero, zero_add] at hs
  rw [← hs]
  apply tsum_congr
  intro k
  rw [if_pos (by omega)]

/-- Translation of the complete shell tail exposes its exact geometric
factor, with a fixed finite coefficient independent of the height. -/
theorem majorant_tail_geometric (A : ℝ) (N : ℕ) :
    (∑' n : ℕ, if N < n then riemannXiInverseSquareDyadicMajorant A n else 0) =
      Real.exp (-(Real.log 2 / 2) * (N : ℝ)) *
        ∑' k : ℕ, riemannXiInverseSquareDyadicMajorant A (k + 1) := by
  rw [majorant_tail_eq_shift, ← tsum_mul_left]
  apply tsum_congr
  intro k
  simp only [riemannXiInverseSquareDyadicMajorant]
  change A * (5 : ℝ) ^ (3 / 2 : ℝ) / Real.log 2 *
      Real.exp (-(Real.log 2 / 2) * ((k + N : ℕ) : ℝ)) = _
  rw [Nat.cast_add]
  rw [show -(Real.log 2 / 2) * ((k : ℝ) + (N : ℝ)) =
    -(Real.log 2 / 2) * (N : ℝ) + -(Real.log 2 / 2) * (k : ℝ) by ring, Real.exp_add]
  ring

/-- The actual multiplicity-weighted height tail has an unconditional
geometric bound at every dyadic lower cutoff. -/
theorem exists_divisorTail_dyadic_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (H : ℝ), (2 : ℝ) ^ N ≤ H →
      divisorTail H ≤ C * Real.exp (-(Real.log 2 / 2) * (N : ℝ)) := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_threeHalvesGrowth
  let S := ∑' k : ℕ, riemannXiInverseSquareDyadicMajorant A (k + 1)
  have hS : 0 ≤ S := by
    apply tsum_nonneg
    intro k
    dsimp only [riemannXiInverseSquareDyadicMajorant]
    positivity
  refine ⟨2 * (S + 1), by positivity, ?_⟩
  intro N H hH
  have h := divisorTail_le_majorant_tail hA hbound N hH
  rw [majorant_tail_geometric] at h
  dsimp only [S] at *
  nlinarith [Real.exp_pos (-(Real.log 2 / 2) * (N : ℝ))]

private theorem dyadic_exp_sq (N : ℕ) :
    Real.exp (-(Real.log 2 / 2) * (N : ℝ)) ^ 2 * (2 : ℝ) ^ N = 1 := by
  calc
    _ = Real.exp (-(Real.log 2 / 2) * (N : ℝ)) ^ 2 *
        Real.exp (Real.log ((2 : ℝ) ^ N)) := by rw [Real.exp_log (by positivity)]
    _ = Real.exp (-(Real.log 2 / 2) * (N : ℝ) +
        -(Real.log 2 / 2) * (N : ℝ) + Real.log ((2 : ℝ) ^ N)) := by
      rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    _ = 1 := by
      rw [Real.log_pow, show -(Real.log 2 / 2) * (N : ℝ) +
        -(Real.log 2 / 2) * (N : ℝ) + (N : ℝ) * Real.log 2 = 0 by ring,
        Real.exp_zero]

/-- The actual height tail decays at least as the inverse square root of
height, at every real cutoff at least one. The constant is independent of
the cutoff, the Gaussian scale and the evaluation ordinate. -/
theorem exists_divisorTail_sqrt_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 1 ≤ H → divisorTail H ≤ C / Real.sqrt H := by
  obtain ⟨C, hC, hbound⟩ := exists_divisorTail_dyadic_bound
  refine ⟨2 * C, by positivity, ?_⟩
  intro H hH
  obtain ⟨N, hN, hNu⟩ := exists_nat_pow_near hH (by norm_num : (1 : ℝ) < 2)
  have hsqrt : 0 < Real.sqrt H := Real.sqrt_pos.mpr (by linarith)
  have he := dyadic_exp_sq N
  have hpos := Real.exp_pos (-(Real.log 2 / 2) * (N : ℝ))
  have hupper : H * Real.exp (-(Real.log 2 / 2) * (N : ℝ)) ^ 2 < 2 := by
    rw [pow_succ] at hNu
    have hm := mul_lt_mul_of_pos_right hNu (sq_pos_of_pos hpos)
    nlinarith
  have hroot : Real.exp (-(Real.log 2 / 2) * (N : ℝ)) * Real.sqrt H ≤ 2 := by
    have hs : (Real.sqrt H) ^ 2 = H := Real.sq_sqrt (by linarith)
    nlinarith [sq_nonneg (Real.exp (-(Real.log 2 / 2) * (N : ℝ)) * Real.sqrt H - 1)]
  have hdiv := (le_div_iff₀ hsqrt).mpr hroot
  exact (hbound N H hN).trans ((mul_le_mul_of_nonneg_left hdiv hC.le).trans_eq (by ring))

end
end RiemannGaussian.GaussianFermiZeroTailRate
