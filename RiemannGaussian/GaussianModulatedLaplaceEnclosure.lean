/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianModulatedLaplace
import RiemannGaussian.GaussianHalfLaplaceShift

/-!
# Exact source and pole enclosures for positive Gaussian modulation

The bounds are proved for the actual half-line integrals. The source uses
the exact Fourier mass and a signed first moment. The pole uses a global
cosine majorant integrated with the exact Gaussian moment recurrence. No
quadrature or numerical oracle is used in either proof.
-/

namespace RiemannGaussian.GaussianModulatedLaplaceEnclosure
noncomputable section
open MeasureTheory Set
open GaussianFermiZeroPair GaussianFermiLaplaceOrder GaussianHalfLaplaceMoments
open GaussianModulatedLaplace FermiCosineModulation GaussianHalfLaplaceShift

private theorem sqrt_pi_lower : (1772453 / 1000000 : ℝ) ≤ Real.sqrt Real.pi := by
  have hp := Real.pi_gt_d6
  have hs := Real.sq_sqrt Real.pi_pos.le
  nlinarith [Real.sqrt_nonneg Real.pi]

private theorem sqrt_pi_upper : Real.sqrt Real.pi ≤ (1772454 / 1000000 : ℝ) := by
  have hp := Real.pi_lt_d6
  have hs := Real.sq_sqrt Real.pi_pos.le
  nlinarith [Real.sqrt_nonneg Real.pi]

private theorem exp_neg_lower : (56978 / 100000 : ℝ) ≤ Real.exp (-(9 / 16)) := by
  have h := Real.exp_bound (x := -(9 / 16 : ℝ)) (by norm_num) (n := 7) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith [(abs_le.mp h).1]

/-- The exact Fourier mass has a rational lower enclosure. -/
theorem halfModulated_zero_lower : (34779 / 50000 : ℝ) ≤ halfModulated 1 (3 / 2) 0 := by
  rw [halfModulated_zero (by norm_num)]
  norm_num only [div_one, one_mul]
  have h := mul_le_mul sqrt_pi_lower (by linarith [exp_neg_lower] :
    (1 + 56978 / 100000 : ℝ) ≤ 1 + Real.exp (-(9 / 16))) (by norm_num)
    (Real.sqrt_nonneg _)
  linarith

/-- The modulated first moment is strictly smaller than the Gaussian first moment. -/
theorem first_moment_upper :
    (∫ t in Ioi (0 : ℝ), atom 1 0 t * factor (3 / 2) t) ≤ (83 / 256 : ℝ) := by
  have h := first_moment_le (δ := (3 / 2 : ℝ)) (by norm_num)
  norm_num at h ⊢
  exact h

/-- The genuine source integral exceeds the rational value used in the new surplus. -/
theorem halfModulated_source_lower :
    (6911 / 10000 : ℝ) ≤ halfModulated 1 (3 / 2) (69 / 5000) := by
  have h := halfModulated_tangent_lower (3 / 2) (69 / 5000)
  linarith [halfModulated_zero_lower, first_moment_upper]

private theorem exp_neg_le_quadratic {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  let f : ℝ → ℝ := fun t ↦ 1 - t + t ^ 2 / 2 - Real.exp (-t)
  have hd (t : ℝ) : deriv f t = -1 + t + Real.exp (-t) := by
    simp (disch := fun_prop) [f]
    ring
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · fun_prop
    · fun_prop
    · intro t _
      rw [hd]
      linarith [Real.one_sub_le_exp_neg t]
  have h := hm (by simp) hx hx
  simpa [f] using h

private theorem integral_window_quartic_upper {h : ℝ} (hh : 0 ≤ h) :
    (∫ t in -h..0, window 1 t) ≤ h - h ^ 3 / 3 + h ^ 5 / 10 := by
  have hi2 : IntervalIntegrable (fun t : ℝ ↦ t ^ 2) volume (-h) 0 := by
    exact (show Continuous (fun t : ℝ ↦ t ^ 2) by fun_prop).intervalIntegrable _ _
  have hi4 : IntervalIntegrable (fun t : ℝ ↦ t ^ 4 / 2) volume (-h) 0 := by
    exact (show Continuous (fun t : ℝ ↦ t ^ 4 / 2) by fun_prop).intervalIntegrable _ _
  have his : IntervalIntegrable (fun t : ℝ ↦ 1 - t ^ 2) volume (-h) 0 :=
    intervalIntegrable_const.sub hi2
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (by linarith : -h ≤ 0)
    ((continuous_window 1).intervalIntegrable _ _) (his.add hi4)
    (fun t _ ↦ show window 1 t ≤ 1 - t ^ 2 + t ^ 4 / 2 by
      have he := exp_neg_le_quadratic (sq_nonneg t)
      simpa only [window, neg_mul, one_mul, ← pow_mul] using he)
  rw [intervalIntegral.integral_add his hi4,
    intervalIntegral.integral_sub intervalIntegrable_const hi2,
    intervalIntegral.integral_div, integral_pow, integral_pow,
    intervalIntegral.integral_const] at hmono
  norm_num at hmono ⊢
  convert hmono using 1
  ring

/-- A narrow Gaussian enclosure retains the complete displaced endpoint interval. -/
theorem halfGaussian_pole_upper : halfGaussian 1 (-(9 / 16)) ≤ (6279 / 5000 : ℝ) := by
  have he : Real.exp ((9 / 16 : ℝ) ^ 2 / 4) ≤ 216463 / 200000 := by
    have h := Real.exp_bound (x := (9 / 16 : ℝ) ^ 2 / 4) (by norm_num) (n := 4) (by norm_num)
    norm_num [Finset.sum_range_succ] at h ⊢
    linarith [(abs_le.mp h).2]
  have hi := integral_window_quartic_upper (by norm_num : (0 : ℝ) ≤ 9 / 32)
  rw [halfGaussian_neg_shift (by norm_num : (0 : ℝ) < 1)]
  norm_num only [div_one, mul_one]
  have hbr : Real.sqrt Real.pi / 2 + (∫ t in -((9 / 16 : ℝ) / 2)..0, window 1 t) ≤
      (1772454 / 1000000 : ℝ) / 2 + 9 / 32 - (9 / 32) ^ 3 / 3 + (9 / 32) ^ 5 / 10 := by
    norm_num only [show (9 / 16 : ℝ) / 2 = 9 / 32 by norm_num]
    linarith [sqrt_pi_upper]
  calc
    _ ≤ (216463 / 200000 : ℝ) *
        ((1772454 / 1000000) / 2 + 9 / 32 - (9 / 32) ^ 3 / 3 + (9 / 32) ^ 5 / 10) := by
      simpa only [show (9 / 16 : ℝ) ^ 2 / 4 = 81 / 1024 by norm_num,
        show (9 / 16 : ℝ) / 2 = 9 / 32 by norm_num] using
        (mul_le_mul_of_nonneg_left hbr (Real.exp_pos _).le).trans
          (mul_le_mul_of_nonneg_right he (by norm_num))
    _ ≤ _ := by norm_num

/-- The full degree-twelve cosine bound integrates with all alternating
coefficients retained, at every real damping and nonnegative frequency. -/
theorem halfModulated_le_moment_polynomial {δ : ℝ} (hδ : 0 ≤ δ) (x : ℝ) :
    halfModulated 1 δ x ≤ moment 0 x / 2 +
      ∑ j ∈ Finset.range 7, ((-1 : ℝ) ^ j * δ ^ (2 * j) / (2 * (2 * j).factorial)) *
        moment (2 * j) x := by
  let c : ℕ → ℝ := fun j ↦ (-1 : ℝ) ^ j * δ ^ (2 * j) / (2 * (2 * j).factorial)
  have hi : Integrable (fun t : ℝ ↦ ∑ j ∈ Finset.range 7, c j * atom (2 * j) x t) := by
    apply integrable_finsetSum
    intro j _
    exact (integrable_atom (2 * j) x).const_mul _
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioi 0),
      modulate δ (window 1) t * Real.exp (-x * t) ≤ atom 0 x t / 2 +
        ∑ j ∈ Finset.range 7, c j * atom (2 * j) x t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hc := CosineTaylorEnclosure.cos_le_degree_twelve (mul_nonneg hδ (le_of_lt ht))
    have h := mul_le_mul_of_nonneg_left hc
      (show 0 ≤ window 1 t * Real.exp (-x * t) by unfold window; positivity)
    simp only [neg_mul] at h
    norm_num [c, Finset.sum_range_succ, atom, modulate, factor]
    linear_combination h / 2
  have h := integral_mono_ae (integrable_halfModulated (by norm_num : (0 : ℝ) < 1) δ x).integrableOn
    (((integrable_atom 0 x).div_const 2).add hi).integrableOn hpoint
  dsimp only [Pi.add_apply] at h
  rw [integral_add ((integrable_atom 0 x).div_const 2).integrableOn hi.integrableOn,
    integral_div, integral_sum_atoms] at h
  exact h

/-- The actual modulated pole integral satisfies the required rational enclosure. -/
theorem halfModulated_pole_upper :
    halfModulated 1 (3 / 2) (-(9 / 16)) ≤ (2263 / 2500 : ℝ) := by
  have h := halfModulated_le_moment_polynomial (δ := (3 / 2 : ℝ)) (by norm_num) (-(9 / 16))
  norm_num [Finset.sum_range_succ] at h
  have he : moment 0 (-(9 / 16)) / 2 +
      ∑ j ∈ Finset.range 7, ((-1 : ℝ) ^ j * (3 / 2) ^ (2 * j) / (2 * (2 * j).factorial)) *
        moment (2 * j) (-(9 / 16)) =
      (2829543339165709267582518383 / 3723491524413057858095022080 : ℝ) *
        halfGaussian 1 (-(9 / 16)) -
        11433550808402759012745033 / 232718220275816116130938880 := by
    norm_num [Finset.sum_range_succ, moment_succ_succ, moment_one_eq, moment_zero]
    ring
  norm_num [Finset.sum_range_succ] at he
  linarith [halfGaussian_pole_upper]

end
end RiemannGaussian.GaussianModulatedLaplaceEnclosure
