/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiPoleFormula
import RiemannGaussian.GaussianFermiPairDecay

/-!
# Signed Gaussian comparisons for the Fermi poles and resonant zeros

The exact shift partition has opposite useful remainders for the constant
pole and a zero evaluated at its own ordinate. Real Laplace monotonicity
proves both remainder signs. The Gaussian half-line transform stays exact;
no triangle inequality separates the two Fermi terms before comparison.
-/

namespace RiemannGaussian.GaussianFermiLaplaceOrder

noncomputable section
open Complex MeasureTheory Set
open FermiLaplaceReflection GaussianFermiZeroPair GaussianFermiPoleFormula
open GaussianFermiDerivativeBounds GaussianFermiPairDecay GaussianFermiZeroTail

/-- The actual one-sided Gaussian Laplace integral, also at negative damping. -/
def halfGaussian (b x : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), window b u * Real.exp (-x * u)

/-- At real damping the original complex Fermi transform is its real
positive-density Laplace integral. -/
theorem transform_real_re {b : ℝ} (hb : 0 < b) (a x : ℝ) :
    (transform a (window b) (x : ℂ)).re =
      ∫ u in Ioi (0 : ℝ), weight a (window b) u * Real.exp (-x * u) := by
  have hi := integrable_transform_integrand a (continuous_window b)
    (z := (x : ℂ)) (integrable_window_exp hb x)
  have hre : (∫ u in Ioi (0 : ℝ),
      ((weight a (window b) u : ℂ) * Complex.exp (-(x : ℂ) * (u : ℂ))).re) =
      (∫ u in Ioi (0 : ℝ),
        (weight a (window b) u : ℂ) * Complex.exp (-(x : ℂ) * (u : ℂ))).re :=
    integral_re hi.integrableOn
  unfold transform
  rw [← hre]
  apply integral_congr_ae
  filter_upwards with u
  simp [Complex.mul_re, Complex.exp_re]

/-- The original Fermi transform is nonnegative at every real damping,
including negative values admitted by the Gaussian window. -/
theorem transform_real_nonneg {b : ℝ} (hb : 0 < b) (a x : ℝ) :
    0 ≤ (transform a (window b) (x : ℂ)).re := by
  rw [transform_real_re hb]
  apply integral_nonneg
  intro u
  unfold weight window EtaGammaSmoothing.fermi
  positivity

/-- The real Fermi Laplace transform is decreasing in damping. -/
theorem transform_real_antitone {b : ℝ} (hb : 0 < b) (a : ℝ) :
    Antitone (fun x : ℝ => (transform a (window b) (x : ℂ)).re) := by
  intro x y hxy
  dsimp only
  rw [transform_real_re hb, transform_real_re hb]
  apply integral_mono_ae
    (integrable_weight_exp a (continuous_window b) (integrable_window_exp hb y)).integrableOn
    (integrable_weight_exp a (continuous_window b) (integrable_window_exp hb x)).integrableOn
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  apply mul_le_mul_of_nonneg_left
  · apply Real.exp_le_exp.mpr
    have hu0 : 0 < u := hu
    nlinarith
  · unfold weight window EtaGammaSmoothing.fermi
    positivity

/-- Real-part specialization of the exact Fermi partition. -/
theorem transform_real_partition {b : ℝ} (hb : 0 < b) (a x : ℝ) :
    (transform a (window b) (x : ℂ)).re +
      (transform a (window b) ((a + x : ℝ) : ℂ)).re = halfGaussian b x := by
  rw [transform_real_re hb, transform_real_re hb]
  have hi (v : ℝ) : IntegrableOn
      (fun u : ℝ => weight a (window b) u * Real.exp (-v * u)) (Ioi 0) :=
    (integrable_weight_exp a (continuous_window b) (integrable_window_exp hb v)).integrableOn
  rw [← integral_add (hi x) (hi (a + x))]
  unfold halfGaussian
  apply integral_congr_ae
  filter_upwards with u
  have hp := weight_partition a (window b) u
  have he : Real.exp (-(a + x) * u) = Real.exp (-a * u) * Real.exp (-x * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  calc
    _ = (weight a (window b) u + Real.exp (-a * u) * weight a (window b) u) *
        Real.exp (-x * u) := by ring
    _ = _ := congrArg (fun v : ℝ => v * Real.exp (-x * u)) hp

/-- The Gaussian half-line transform is nonnegative. -/
theorem halfGaussian_nonneg (b x : ℝ) : 0 ≤ halfGaussian b x := by
  apply integral_nonneg
  intro u
  unfold window
  positivity

/-- The unsmoothed real Gaussian transform is decreasing in damping. -/
theorem halfGaussian_antitone {b : ℝ} (hb : 0 < b) : Antitone (halfGaussian b) := by
  intro x y hxy
  apply integral_mono_ae (integrable_window_exp hb y).integrableOn
    (integrable_window_exp hb x).integrableOn
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  apply mul_le_mul_of_nonneg_left
  · apply Real.exp_le_exp.mpr
    have hu0 : 0 < u := hu
    nlinarith
  · exact (Real.exp_pos _).le

/-- The exact resonant pair is the Gaussian transform plus a retained
signed difference of Fermi transforms. -/
theorem real_pair_eq_halfGaussian_add_reserve {b : ℝ} (hb : 0 < b) (a x : ℝ) :
    (transform a (window b) (x : ℂ)).re +
      (transform a (window b) ((a - x : ℝ) : ℂ)).re =
        halfGaussian b x + ((transform a (window b) ((a - x : ℝ) : ℂ)).re -
          (transform a (window b) ((a + x : ℝ) : ℂ)).re) := by
  linarith [transform_real_partition hb a x]

/-- At nonnegative real displacement the whole resonant Fermi pair is
at least the unsmoothed Gaussian Laplace transform. -/
theorem halfGaussian_le_real_pair {b x : ℝ} (hb : 0 < b) (hx : 0 ≤ x) (a : ℝ) :
    halfGaussian b x ≤ (transform a (window b) (x : ℂ)).re +
      (transform a (window b) ((a - x : ℝ) : ℂ)).re := by
  rw [real_pair_eq_halfGaussian_add_reserve hb]
  have h := transform_real_antitone hb a (show a - x ≤ a + x by linarith)
  linarith

/-- The constant pole retains an exact subtractive reserve before it is
bounded by the negative-damping Gaussian transform. -/
theorem pole_zero_eq_halfGaussian_sub_reserve {b : ℝ} (hb : 0 < b) (σ : ℝ) :
    polePair b σ 0 = halfGaussian b (σ - 1) -
      ((transform (2 * σ - 1) (window b) ((3 * σ - 2 : ℝ) : ℂ)).re -
        (transform (2 * σ - 1) (window b) (σ : ℂ)).re) := by
  rw [polePair_eq_physical]
  simp only [Complex.ofReal_zero, zero_mul, add_zero]
  have h := transform_real_partition hb (2 * σ - 1) (σ - 1)
  rw [show 2 * σ - 1 + (σ - 1) = 3 * σ - 2 by ring] at h
  linarith

/-- For every evaluation line at or left of one, the constant-frequency
pole is bounded by one Gaussian half-line transform, with no factor-two loss. -/
theorem pole_zero_le_halfGaussian {b σ : ℝ} (hb : 0 < b) (hσ : σ ≤ 1) :
    polePair b σ 0 ≤ halfGaussian b (σ - 1) := by
  rw [pole_zero_eq_halfGaussian_sub_reserve hb]
  have h := transform_real_antitone hb (2 * σ - 1)
    (show 3 * σ - 2 ≤ σ by linarith)
  linarith

/-- Every nonzero-frequency pole has the already established paired
inverse-square bound, on the full admissible interior evaluation strip. -/
theorem abs_polePair_le {b σ t : ℝ} (hb : 0 < b) (hσ0 : 1 / 2 ≤ σ)
    (hσ1 : σ ≤ 1) (hscale : (1 - σ) ^ 2 ≤ b) (ht : t ≠ 0) :
    |polePair b σ t| ≤ integralCost (2 * σ - 1) b (1 - σ) / t ^ 2 := by
  have hz0 : -(1 - σ) ≤ ((σ : ℂ) + (t : ℂ) * I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith
  have hza : ((σ : ℂ) + (t : ℂ) * I).re ≤ (2 * σ - 1) + (1 - σ) := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith
  have hy : ((σ : ℂ) + (t : ℂ) * I).im ≠ 0 := by simpa using ht
  have h := abs_physical_pair_re_le (show 0 ≤ 2 * σ - 1 by linarith) hb
    (show 0 ≤ 1 - σ by linarith) hscale hz0 hza hy
  rw [physical_pair_re_eq] at h
  simpa [polePair] using h

/-- Explicit upper envelope for the actual pole pair: the exact Gaussian
half-line integral at zero, and paired inverse-square decay elsewhere. -/
def poleUpper (b σ t : ℝ) : ℝ :=
  if t = 0 then halfGaussian b (σ - 1)
  else integralCost (2 * σ - 1) b (1 - σ) / t ^ 2

/-- The whole pole pair obeys the stated envelope at every frequency. -/
theorem polePair_le_poleUpper {b σ : ℝ} (hb : 0 < b) (hσ0 : 1 / 2 ≤ σ)
    (hσ1 : σ ≤ 1) (hscale : (1 - σ) ^ 2 ≤ b) (t : ℝ) :
    polePair b σ t ≤ poleUpper b σ t := by
  unfold poleUpper
  split_ifs with ht
  · subst t
    exact pole_zero_le_halfGaussian hb hσ1
  · exact (le_abs_self _).trans (abs_polePair_le hb hσ0 hσ1 hscale ht)

end
end RiemannGaussian.GaussianFermiLaplaceOrder
