/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RiemannXiSuzukiSpectralStaticContourCriticalZetaLowerSubquadratic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Vanishing variation of the canonical xi residual

The canonical decomposition leaves a zero-free analytic factor on each
expanding disk. Its logarithmic derivative need not tend to zero. Its
*difference at two fixed points* does tend to zero: two Cauchy estimates
retain the strict gap between xi's proved growth exponent `3/2` and `2`.
This removes the analytic ambiguity needed for a global paired partial
fraction expansion, without choosing an unknown affine factor.
-/

open Complex Filter MeromorphicOn Metric Set Topology
open scoped Topology

namespace RiemannGaussian

noncomputable section

private lemma analyticAt_canonicalResidual_logDeriv (n : ℕ) {z : ℂ}
    (hz : z ∈ closedBall 0 (xiCanonicalRadius n)) :
    AnalyticAt ℂ (logDeriv (riemannXiCanonicalResidual n)) z := by
  have hg := (riemannXiCanonicalResidual_decomp n).analyticOnNhd z hz
  simpa only [logDeriv] using hg.deriv.div hg
    ((riemannXiCanonicalResidual_decomp n).ne_zero z hz)

/-- Cauchy's first estimate retains the actual three-halves xi growth in
the logarithmic derivative of the zero-free canonical residual. -/
theorem norm_logDeriv_riemannXiCanonicalResidual_le_of_threeHalves_growth
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤ Real.exp (A * (‖z‖ + 1) ^ (3 / 2 : ℝ)))
    (n : ℕ) {z : ℂ} (hz : ‖z‖ ≤ xiCanonicalRadius n / 4) :
    ‖logDeriv (riemannXiCanonicalResidual n) z‖ ≤
      8 * (A * (xiCanonicalRadius n + 1) ^ (3 / 2 : ℝ)) /
        xiCanonicalRadius n := by
  let R := xiCanonicalRadius n
  let L := riemannXiCanonicalLog n
  let M := A * (R + 1) ^ (3 / 2 : ℝ)
  have hR : 0 < R := xiCanonicalRadius_pos n
  have hr : 0 < R / 4 := by positivity
  have hz' : ‖z‖ ≤ R / 4 := hz
  have hzball : z ∈ ball 0 R := by
    rw [mem_ball, dist_zero_right]
    linarith
  have hglobalDiff : DifferentiableOn ℂ L (ball 0 R) := by
    intro w hw
    exact (riemannXiCanonicalLog_hasDerivAt n hw).differentiableAt.differentiableWithinAt
  have hnorm : ∀ w ∈ closedBall z (R / 4), ‖w‖ ≤ R / 2 := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    calc
      ‖w‖ = ‖(w - z) + z‖ := by ring_nf
      _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ R / 4 + R / 4 := add_le_add hw hz'
      _ = R / 2 := by ring
  have hlocalSubset : closedBall z (R / 4) ⊆ ball 0 R := by
    intro w hw
    rw [mem_ball, dist_zero_right]
    have := hnorm w hw
    linarith
  have hlocalDiff : DiffContOnCl ℂ L (ball z (R / 4)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z hr.ne']
    exact hglobalDiff.mono hlocalSubset
  have hboundary : ∀ w ∈ sphere z (R / 4), ‖L w‖ ≤ 2 * M := by
    intro w hw
    have hwclosed := sphere_subset_closedBall hw
    have hwnorm := hnorm w hwclosed
    have hL := norm_riemannXiCanonicalLog_le_of_threeHalves_growth hA hbound n
      (hlocalSubset hwclosed)
    have hden : 0 < R - ‖w‖ := by linarith
    have hratio : ‖w‖ / (R - ‖w‖) ≤ 1 :=
      (div_le_one hden).mpr (by linarith)
    calc
      ‖L w‖ ≤ 2 * M * ‖w‖ / (R - ‖w‖) := hL
      _ = (2 * M) * (‖w‖ / (R - ‖w‖)) := by ring
      _ ≤ (2 * M) * 1 :=
        mul_le_mul_of_nonneg_left hratio (by dsimp [M]; positivity)
      _ = 2 * M := by ring
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    hr hlocalDiff hboundary
  change ‖deriv (riemannXiCanonicalLog n) z‖ ≤ _ at hcauchy
  rw [(riemannXiCanonicalLog_hasDerivAt n hzball).deriv] at hcauchy
  convert hcauchy using 1
  dsimp [M, R]
  ring

/-- A second Cauchy estimate bounds the derivative of the residual's
logarithmic derivative by a quantity of order `R^(-1/2)`. -/
theorem norm_deriv_logDeriv_riemannXiCanonicalResidual_le_of_threeHalves_growth
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤ Real.exp (A * (‖z‖ + 1) ^ (3 / 2 : ℝ)))
    (n : ℕ) {z : ℂ} (hz : ‖z‖ ≤ xiCanonicalRadius n / 8) :
    ‖deriv (logDeriv (riemannXiCanonicalResidual n)) z‖ ≤
      64 * (A * (xiCanonicalRadius n + 1) ^ (3 / 2 : ℝ)) /
        xiCanonicalRadius n ^ 2 := by
  let R := xiCanonicalRadius n
  let f := logDeriv (riemannXiCanonicalResidual n)
  have hR : 0 < R := xiCanonicalRadius_pos n
  have hr : 0 < R / 8 := by positivity
  have hz' : ‖z‖ ≤ R / 8 := hz
  have hnorm : ∀ w ∈ closedBall z (R / 8), ‖w‖ ≤ R / 4 := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    calc
      ‖w‖ = ‖(w - z) + z‖ := by ring_nf
      _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ R / 8 + R / 8 := add_le_add hw hz'
      _ = R / 4 := by ring
  have hlocalDiff : DiffContOnCl ℂ f (ball z (R / 8)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z hr.ne']
    intro w hw
    apply (analyticAt_canonicalResidual_logDeriv n ?_).differentiableAt.differentiableWithinAt
    rw [mem_closedBall, dist_zero_right]
    have := hnorm w hw
    linarith
  have hboundary : ∀ w ∈ sphere z (R / 8),
      ‖f w‖ ≤ 8 * (A * (R + 1) ^ (3 / 2 : ℝ)) / R := by
    intro w hw
    exact norm_logDeriv_riemannXiCanonicalResidual_le_of_threeHalves_growth
      hA hbound n (hnorm w (sphere_subset_closedBall hw))
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    hr hlocalDiff hboundary
  convert hcauchy using 1
  dsimp [R]
  ring

/-- The actual canonical residual has uniformly small logarithmic-derivative
variation between any two points in the inner eighth of its disk. -/
theorem norm_logDeriv_riemannXiCanonicalResidual_sub_le_of_threeHalves_growth
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤ Real.exp (A * (‖z‖ + 1) ^ (3 / 2 : ℝ)))
    (n : ℕ) {s w : ℂ}
    (hs : ‖s‖ ≤ xiCanonicalRadius n / 8)
    (hw : ‖w‖ ≤ xiCanonicalRadius n / 8) :
    ‖logDeriv (riemannXiCanonicalResidual n) s -
        logDeriv (riemannXiCanonicalResidual n) w‖ ≤
      (64 * (A * (xiCanonicalRadius n + 1) ^ (3 / 2 : ℝ)) /
        xiCanonicalRadius n ^ 2) * ‖s - w‖ := by
  apply Convex.norm_image_sub_le_of_norm_deriv_le
    (s := closedBall 0 (xiCanonicalRadius n / 8))
  · intro z hz
    apply (analyticAt_canonicalResidual_logDeriv n ?_).differentiableAt
    exact closedBall_subset_closedBall (by have := xiCanonicalRadius_pos n; linarith) hz
  · intro z hz
    exact norm_deriv_logDeriv_riemannXiCanonicalResidual_le_of_threeHalves_growth
      hA hbound n (by simpa only [mem_closedBall, dist_zero_right] using hz)
  · exact convex_closedBall (0 : ℂ) _
  · simpa only [mem_closedBall, dist_zero_right] using hw
  · simpa only [mem_closedBall, dist_zero_right] using hs

/-- The zero-free canonical xi radii tend to infinity. -/
theorem tendsto_xiCanonicalRadius_atTop : Tendsto xiCanonicalRadius atTop atTop := by
  apply tendsto_atTop_mono (fun n => (xiCanonicalRadius_spec n).1.le)
  exact ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds).const_mul_atTop
    (by norm_num)

/-- Dividing the three-halves growth of any fixed positive affine radius
by its square tends to zero. This also controls the mirror factors. -/
theorem tendsto_affine_threeHalves_div_xiCanonicalRadius_sq
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Tendsto (fun n => (a * xiCanonicalRadius n + b) ^ (3 / 2 : ℝ) /
      xiCanonicalRadius n ^ 2) atTop (𝓝 0) := by
  have hR := tendsto_xiCanonicalRadius_atTop
  have hdecay : Tendsto (fun n => xiCanonicalRadius n ^ (- (1 / 2 : ℝ)))
      atTop (𝓝 0) := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hR
  refine squeeze_zero' (Eventually.of_forall fun n => by
    have := xiCanonicalRadius_pos n
    positivity) ?_
    (by simpa only [mul_zero] using hdecay.const_mul ((a + b) ^ (3 / 2 : ℝ)))
  filter_upwards [hR.eventually (eventually_ge_atTop 1)] with n hn
  have hpos := xiCanonicalRadius_pos n
  calc
    (a * xiCanonicalRadius n + b) ^ (3 / 2 : ℝ) / xiCanonicalRadius n ^ 2
      ≤ ((a + b) * xiCanonicalRadius n) ^ (3 / 2 : ℝ) /
          xiCanonicalRadius n ^ 2 := by
        gcongr
        nlinarith
    _ = (a + b) ^ (3 / 2 : ℝ) * xiCanonicalRadius n ^ (- (1 / 2 : ℝ)) := by
      rw [Real.mul_rpow (by positivity) hpos.le, mul_div_assoc,
        ← Real.rpow_natCast, ← Real.rpow_sub hpos]
      norm_num

/-- At arbitrary fixed complex points, the difference of the actual
canonical residual logarithmic derivatives tends to zero unconditionally.
Neither point is required to avoid xi zeros, since the residual is zero-free. -/
theorem tendsto_logDeriv_riemannXiCanonicalResidual_sub (s w : ℂ) :
    Tendsto (fun n => logDeriv (riemannXiCanonicalResidual n) s -
      logDeriv (riemannXiCanonicalResidual n) w) atTop (𝓝 0) := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_threeHalvesGrowth
  have hdecay := (tendsto_affine_threeHalves_div_xiCanonicalRadius_sq
    (a := 1) (b := 1) (by norm_num) (by norm_num)).const_mul (64 * A * ‖s - w‖)
  simp only [one_mul, mul_zero] at hdecay
  refine squeeze_zero_norm' ?_ hdecay
  filter_upwards [tendsto_xiCanonicalRadius_atTop.eventually
    (eventually_ge_atTop (8 * max ‖s‖ ‖w‖))] with n hn
  have hs : ‖s‖ ≤ xiCanonicalRadius n / 8 := by
    have := le_max_left ‖s‖ ‖w‖
    linarith
  have hw : ‖w‖ ≤ xiCanonicalRadius n / 8 := by
    have := le_max_right ‖s‖ ‖w‖
    linarith
  convert norm_logDeriv_riemannXiCanonicalResidual_sub_le_of_threeHalves_growth
    hA hbound n hs hw using 1
  ring

end

end RiemannGaussian
