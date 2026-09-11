/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiLaplaceOrder
import RiemannGaussian.GaussianFermiGaussianMixture
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Exact reflection and quantitative bounds for the Gaussian half transform

The original half-line Gaussian Laplace integral scales exactly. Its two
real reflections sum to the full Gaussian atom. Integrating the exponential
tangent gives a lower bound; reflection turns the same estimate into an
upper bound at negative damping. These bounds apply to the actual scalar
source and pole envelope in the Fermi zero budget.
-/

namespace RiemannGaussian.GaussianHalfLaplaceBounds

noncomputable section
open Complex MeasureTheory Set
open GaussianFermiZeroPair GaussianFermiLaplaceOrder GaussianFermiGaussianMixture

/-- Exact value at zero damping, in the existing half-line normalization. -/
theorem halfGaussian_zero (b : ℝ) :
    halfGaussian b 0 = Real.sqrt (Real.pi / b) / 2 := by
  simpa [halfGaussian, window] using integral_gaussian_Ioi b

/-- The first half-line Gaussian moment has its exact positive-scale value. -/
theorem integral_half_first_moment {b : ℝ} (hb : 0 < b) :
    (∫ u in Ioi (0 : ℝ), u * window b u) = 1 / (2 * b) := by
  have hc := integral_mul_cexp_neg_mul_sq (b := (b : ℂ)) (by simpa using hb)
  have hi := (integrable_mul_cexp_neg_mul_sq (b := (b : ℂ)) (by simpa using hb)).integrableOn
    (s := Ioi (0 : ℝ))
  have hr : (∫ u : ℝ in Ioi 0, ((u : ℂ) * Complex.exp (-(b : ℂ) * (u : ℂ) ^ 2)).re) =
      (∫ u : ℝ in Ioi 0, (u : ℂ) * Complex.exp (-(b : ℂ) * (u : ℂ) ^ 2)).re := integral_re hi
  have he : (((1 / (2 * b) : ℝ) : ℂ)) = (2 * (b : ℂ))⁻¹ := by
    push_cast
    rw [one_div]
  rw [hc, ← he] at hr
  simpa [window, ← Complex.ofReal_pow, Complex.mul_re, Complex.exp_re] using hr

/-- Integrating the exact exponential tangent bounds the genuine Gaussian
transform below at every real damping. -/
theorem halfGaussian_tangent_lower {b : ℝ} (hb : 0 < b) (x : ℝ) :
    Real.sqrt (Real.pi / b) / 2 - x / (2 * b) ≤ halfGaussian b x := by
  have hi0 : Integrable (window b) := by
    simpa using integrable_window_exp hb 0
  have hi1 : Integrable (fun u : ℝ => u * window b u) := integrable_mul_exp_neg_mul_sq hb
  have hit : Integrable (fun u : ℝ => window b u - x * (u * window b u)) :=
    hi0.sub (hi1.const_mul x)
  have hpoint (u : ℝ) : window b u - x * (u * window b u) ≤
      window b u * Real.exp (-x * u) := by
    have h := mul_le_mul_of_nonneg_left (Real.one_sub_le_exp_neg (x * u))
      (show 0 ≤ window b u from (Real.exp_pos _).le)
    calc
      _ = window b u * (1 - x * u) := by ring
      _ ≤ _ := by simpa only [neg_mul] using h
  have hupper := integral_mono (hit.integrableOn (s := Ioi (0 : ℝ)))
    (integrable_window_exp hb x).integrableOn hpoint
  rw [integral_sub hi0.integrableOn (hi1.const_mul x).integrableOn,
    integral_const_mul, integral_half_first_moment hb] at hupper
  have hzero : (∫ u in Ioi (0 : ℝ), window b u) = Real.sqrt (Real.pi / b) / 2 := by
    simpa [window] using integral_gaussian_Ioi b
  rw [hzero] at hupper
  simpa only [halfGaussian, mul_one_div] using hupper

/-- The two half-line reflections reconstruct the full real Gaussian
Laplace atom exactly, before either reflection is estimated. -/
theorem halfGaussian_reflection {b : ℝ} (hb : 0 < b) (x : ℝ) :
    halfGaussian b x + halfGaussian b (-x) =
      Real.sqrt (Real.pi / b) * Real.exp (x ^ 2 / (4 * b)) := by
  let f : ℝ → ℝ := fun u => window b u * Real.exp (-x * u)
  have hi : Integrable f := integrable_window_exp hb x
  have hneg : (∫ u in Iic (0 : ℝ), f u) = halfGaussian b (-x) := by
    rw [← show (∫ u in Ioi (0 : ℝ), f (-u)) = ∫ u in Iic (0 : ℝ), f u by
      simp]
    apply integral_congr_ae
    filter_upwards with u
    simp [f, window]
  have hsplit := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hi
  rw [compl_Ioi, hneg] at hsplit
  have hfull : (∫ u : ℝ, f u) = Real.sqrt (Real.pi / b) * Real.exp (x ^ 2 / (4 * b)) := by
    have h := integral_timeAtom hb (x : ℂ)
    have he : timeAtom b (x : ℂ) = fun u : ℝ => (f u : ℂ) := by
      funext u
      dsimp only [timeAtom, f]
      push_cast
      rfl
    have hv : gaussianAtom b (x : ℂ) =
        ((Real.sqrt (Real.pi / b) * Real.exp (x ^ 2 / (4 * b)) : ℝ) : ℂ) := by
      dsimp only [gaussianAtom]
      push_cast
      rfl
    simp only [he, hv] at h
    exact_mod_cast h
  exact hsplit.trans hfull

/-- Reflection converts the lower tangent into an explicit negative-damping
upper bound without estimating the two half-lines separately. -/
theorem halfGaussian_neg_upper {b : ℝ} (hb : 0 < b) (x : ℝ) :
    halfGaussian b (-x) ≤ Real.sqrt (Real.pi / b) *
      (Real.exp (x ^ 2 / (4 * b)) - 1 / 2) + x / (2 * b) := by
  linarith [halfGaussian_reflection hb x, halfGaussian_tangent_lower hb x]

/-- Exact positive dilation of both Gaussian scale and damping. -/
theorem halfGaussian_scale {r : ℝ} (hr : 0 < r) (b x : ℝ) :
    r * halfGaussian (b * r ^ 2) (x * r) = halfGaussian b x := by
  have h := integral_comp_mul_left_Ioi' (fun u : ℝ => window b u * Real.exp (-x * u)) 0 hr
  simp only [mul_zero, smul_eq_mul] at h
  have he : (fun u : ℝ => window (b * r ^ 2) u * Real.exp (-(x * r) * u)) =
      (fun u : ℝ => window b (r * u) * Real.exp (-x * (r * u))) := by
    funext u
    unfold window
    congr 2 <;> ring
  simpa only [halfGaussian, he] using h

/-- A convenient exact lower enclosure at the positive profile argument. -/
theorem halfGaussian_unit_three_twentieths_lower :
    (811 / 1000 : ℝ) ≤ halfGaussian 1 (3 / 20) := by
  have hs : (443 / 500 : ℝ) ≤ Real.sqrt Real.pi / 2 := by
    have hpi := Real.pi_gt_d2
    have hsq := Real.sq_sqrt Real.pi_pos.le
    nlinarith [Real.sqrt_nonneg Real.pi]
  have h := halfGaussian_tangent_lower (by norm_num : (0 : ℝ) < 1) (3 / 20)
  norm_num at h
  linarith

/-- An exact upper enclosure for the negative profile argument used in
the interior pole comparison. -/
theorem halfGaussian_unit_neg_sixtythree_twohundredths_upper :
    halfGaussian 1 (-(63 / 200)) ≤ (109 / 100 : ℝ) := by
  have hs : Real.sqrt Real.pi ≤ (887 / 500 : ℝ) := by
    have hpi := Real.pi_lt_d4
    have hsq := Real.sq_sqrt Real.pi_pos.le
    nlinarith [Real.sqrt_nonneg Real.pi]
  have he : Real.exp ((63 / 200 : ℝ) ^ 2 / 4) ≤ 160000 / 156031 := by
    have h := Real.exp_bound_div_one_sub_of_interval
      (by norm_num : (0 : ℝ) ≤ (63 / 200) ^ 2 / 4)
      (by norm_num : (63 / 200 : ℝ) ^ 2 / 4 < 1)
    norm_num at h ⊢
    exact h
  have hp : 0 ≤ Real.exp ((63 / 200 : ℝ) ^ 2 / 4) - 1 / 2 := by
    linarith [Real.add_one_le_exp ((63 / 200 : ℝ) ^ 2 / 4)]
  norm_num at he hp
  have h := halfGaussian_neg_upper (by norm_num : (0 : ℝ) < 1) (63 / 200)
  norm_num only [div_one, mul_one] at h
  calc
    _ ≤ _ := h
    _ ≤ (887 / 500 : ℝ) * (160000 / 156031 - 1 / 2) + 63 / 400 := by
      gcongr
    _ ≤ _ := by norm_num

end
end RiemannGaussian.GaussianHalfLaplaceBounds
