/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiMassRescaling
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Decay of normalized mass derivative energy on compact intervals

Differentiating the exact mass--carrier quadratic surface gives a
pointwise derivative budget proportional to the mass itself. Combined
with the common rescaling denominator, this controls the scaled mass
derivative uniformly and proves its squared integral tends to zero.
No zero simplicity or separation hypothesis is used.
-/

open Complex Filter MeasureTheory Set Topology
namespace RiemannGaussian
noncomputable section

private lemma normSq_derivative {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun u => normSq (f u)) (2 * (f x * starRingEnd ℂ f').re) x := by
  have he : (fun u => normSq (f u)) = fun u => (f u * starRingEnd ℂ (f u)).re := by
    funext u
    rw [mul_conj, ofReal_re]
  rw [he]
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hf.fun_mul hf.star)
  convert! h using 1
  simp only [star_def, Complex.add_re, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, Complex.reCLM_apply]
  ring

private lemma quadratic_surface_budget {u g e : ℝ} (hu : 0 ≤ u) (he : 0 ≤ e)
    (hb : ((1 - 2 * u) * g) ^ 2 ≤ 4 * u * e) :
    g ^ 2 ≤ 16 * u * (e + g ^ 2) := by
  by_cases hsmall : u ≤ 1 / 4
  · have hfactor : 1 / 4 ≤ (1 - 2 * u) ^ 2 := by nlinarith
    have hm := mul_nonneg (sub_nonneg.mpr hfactor) (sq_nonneg g)
    have hext := mul_nonneg hu (sq_nonneg g)
    nlinarith
  · have hm := mul_nonneg (show 0 ≤ 4 * u - 1 by linarith) (sq_nonneg g)
    have hext := mul_nonneg hu he
    nlinarith [sq_nonneg g]

/-- Differentiating the actual mass--carrier surface bounds the square
of the unit mass derivative by the mass times continuous unit data.
This retains the vanishing at zeros that a derivative norm bound loses. -/
theorem deriv_suzukiXiHorizontalMass_sq_le_unit_budget (y x : ℝ) :
    deriv (suzukiXiHorizontalMass 1 y) x ^ 2 ≤
      16 * suzukiXiHorizontalMass 1 y x *
        (‖deriv (suzukiXiHorizontalCarrier 1 y) x‖ ^ 2 + deriv (suzukiXiHorizontalMass 1 y) x ^ 2) := by
  have hS := ((contDiff_suzukiXiHorizontalCarrier (by norm_num : (0 : ℝ) < 1) y).differentiable (by simp) x).hasDerivAt
  have hU := ((contDiff_suzukiXiHorizontalMass (by norm_num : (0 : ℝ) < 1) y).differentiable (by simp) x).hasDerivAt
  have hfun : (fun u => normSq (suzukiXiHorizontalCarrier 1 y u)) =
      fun u => suzukiXiHorizontalMass 1 y u - suzukiXiHorizontalMass 1 y u ^ 2 := by
    funext u
    simpa only [suzukiXiHorizontalCarrier, suzukiXiHorizontalMass, one_pow, one_mul] using normSq_suzukiXiSmoothCarrier_eq_mass (by norm_num : (0 : ℝ) < 1)
      ((u : ℂ) + (y : ℂ) * I)
  have hd := congrArg (fun f : ℝ → ℝ => deriv f x) hfun
  have hderiv := (hU.fun_sub (hU.pow 2)).deriv
  change deriv (fun u => suzukiXiHorizontalMass 1 y u - suzukiXiHorizontalMass 1 y u ^ 2) x = _ at hderiv
  rw [(normSq_derivative hS).deriv, hderiv] at hd
  have heq : 2 * (suzukiXiHorizontalCarrier 1 y x * starRingEnd ℂ (deriv (suzukiXiHorizontalCarrier 1 y) x)).re =
      (1 - 2 * suzukiXiHorizontalMass 1 y x) * deriv (suzukiXiHorizontalMass 1 y) x := by
    simp only [Nat.cast_ofNat] at hd
    linear_combination hd
  apply quadratic_surface_budget (u := suzukiXiHorizontalMass 1 y x)
    (suzukiXiNormalizedMass_nonneg 1 _) (sq_nonneg _) ?_
  rw [← heq]
  have hnorm : (suzukiXiHorizontalCarrier 1 y x * starRingEnd ℂ (deriv (suzukiXiHorizontalCarrier 1 y) x)).re ^ 2 ≤
      normSq (suzukiXiHorizontalCarrier 1 y x * starRingEnd ℂ (deriv (suzukiXiHorizontalCarrier 1 y) x)) := by
    rw [normSq_apply]
    nlinarith [sq_nonneg (suzukiXiHorizontalCarrier 1 y x * starRingEnd ℂ (deriv (suzukiXiHorizontalCarrier 1 y) x)).im]
  rw [map_mul, normSq_conj, congrFun hfun x, normSq_eq_norm_sq] at hnorm
  nlinarith [mul_nonneg (sq_nonneg (suzukiXiHorizontalMass 1 y x))
    (sq_nonneg ‖deriv (suzukiXiHorizontalCarrier 1 y) x‖)]

/-- The scaled derivative energy has a continuous majorant independent
of every smoothing parameter at least two. The bound covers every zero
and genuine carrier pole on the entire horizontal line. -/
theorem suzukiXiHorizontalMass_scaled_derivative_sq_le {r : ℝ} (hr : 2 ≤ r) (y x : ℝ) :
    r ^ 2 * deriv (suzukiXiHorizontalMass r y) x ^ 2 ≤
      32 * (‖deriv (suzukiXiHorizontalCarrier 1 y) x‖ ^ 2 + deriv (suzukiXiHorizontalMass 1 y) x ^ 2) := by
  let u := suzukiXiHorizontalMass 1 y x
  let d := 1 + (r ^ 2 - 1) * u
  let C := ‖deriv (suzukiXiHorizontalCarrier 1 y) x‖ ^ 2 + deriv (suzukiXiHorizontalMass 1 y) x ^ 2
  have hu : 0 ≤ u := suzukiXiNormalizedMass_nonneg 1 _
  have hC : 0 ≤ C := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hd : 1 ≤ d := by
    have hn : 0 ≤ r ^ 2 - 1 := by nlinarith
    dsimp [d]
    nlinarith [mul_nonneg hn hu]
  have hdu : r ^ 2 * u ≤ 2 * d := by
    have hn : 0 ≤ r ^ 2 - 2 := by nlinarith
    dsimp [d]
    nlinarith [mul_nonneg hn hu]
  have hd4 : d ≤ d ^ 4 := by nlinarith [sq_nonneg (d - 1), sq_nonneg (d ^ 2 - 1)]
  have hb := deriv_suzukiXiHorizontalMass_sq_le_unit_budget y x
  change deriv (suzukiXiHorizontalMass 1 y) x ^ 2 ≤ 16 * u * C at hb
  rw [deriv_suzukiXiHorizontalMass_unit_rescaling (by linarith)]
  change r ^ 2 * (deriv (suzukiXiHorizontalMass 1 y) x / d ^ 2) ^ 2 ≤ 32 * C
  calc
    _ = (r ^ 2 * deriv (suzukiXiHorizontalMass 1 y) x ^ 2) / d ^ 4 := by ring_nf
    _ ≤ 32 * C := by
      apply (div_le_iff₀ (pow_pos (by linarith : 0 < d) 4)).mpr
      calc
        _ ≤ r ^ 2 * (16 * u * C) := mul_le_mul_of_nonneg_left hb (sq_nonneg r)
        _ = 16 * C * (r ^ 2 * u) := by ring
        _ ≤ 16 * C * (2 * d) := mul_le_mul_of_nonneg_left hdu (by positivity)
        _ ≤ 16 * C * (2 * d ^ 4) := by gcongr
        _ = _ := by ring

/-- The actual scaled mass derivative energy tends to zero on every
compact subset of a horizontal line. The continuous unit-field
majorant discharges dominated convergence through the whole divisor. -/
theorem tendsto_integral_suzukiXiHorizontalMassDerivativeEnergy (y : ℝ)
    {K : Set ℝ} (hK : IsCompact K) :
    Tendsto (fun r : ℝ => ∫ x in K, r ^ 2 * deriv (suzukiXiHorizontalMass r y) x ^ 2)
      atTop (𝓝 0) := by
  let C : ℝ → ℝ := fun x =>
    32 * (‖deriv (suzukiXiHorizontalCarrier 1 y) x‖ ^ 2 + deriv (suzukiXiHorizontalMass 1 y) x ^ 2)
  have hc : Continuous C := by
    exact continuous_const.mul
      ((((contDiff_suzukiXiHorizontalCarrier (by norm_num : (0 : ℝ) < 1) y).continuous_deriv (by simp)).norm.pow 2).add
        (((contDiff_suzukiXiHorizontalMass (by norm_num : (0 : ℝ) < 1) y).continuous_deriv (by simp)).pow 2))
  have ht := tendsto_integral_filter_of_dominated_convergence
    (l := (atTop : Filter ℝ)) (μ := volume.restrict K)
    (F := fun r : ℝ => fun x => r ^ 2 * deriv (suzukiXiHorizontalMass r y) x ^ 2)
    (f := fun _ => (0 : ℝ)) C ?_ ?_ (hc.continuousOn.integrableOn_compact hK) ?_
  · simpa only [integral_zero] using ht
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact (continuous_const.mul (((contDiff_suzukiXiHorizontalMass hr y).continuous_deriv (by simp)).pow 2)).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with r hr
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg r) (sq_nonneg _))]
      exact suzukiXiHorizontalMass_scaled_derivative_sq_le hr y x
  · exact ae_of_all _ fun x => by
      simpa only [mul_pow, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
        (tendsto_deriv_suzukiXiHorizontalMass_scaled y x).pow 2

end
end RiemannGaussian
