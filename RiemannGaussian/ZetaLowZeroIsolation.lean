/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaLowZeroDisc
import RiemannGaussian.ZetaLowZeroSamples
import RiemannGaussian.GaussianZetaBridge

/-!
# An actual isolated simple critical-line zero

Two kernel-checked zeta values and an independent Cauchy bound discharge a
complex Newton contraction. Its unique zero is fixed by the functional-
equation reflection, proving that it lies exactly on the critical line.
This is one verified isolating neighborhood, not a complete low-zero list.
-/

namespace RiemannGaussian.ZetaLowZeroSamples
open LeanCert.Core LeanCert.Engine CertifiedComplexInterval ZetaEulerMaclaurinValue

/-- The actual zeta residual at the center is less than one hundred-millionth. -/
theorem norm_center_lt : ‖riemannZeta center‖ < (1 / 10 ^ 8 : ℝ) := by
  have hs : Mem center (rational config.precision (1 / 2) ordinate) := by
    simpa only [center, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      mem_rational (by decide : config.precision ≤ 0) (1 / 2) ordinate
  have hh := norm_sub_lt_of_closeCheck center_check hs
  simpa only [Rat.cast_zero, zero_mul, add_zero, sub_zero, Rat.cast_div,
    Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using hh

/-- The actual displaced zeta value lies within the certified error of
the proposed slope times the actual displacement. -/
theorem norm_step_lt :
    ‖riemannZeta (center + (step : ℂ)) - slope * (step : ℂ)‖ < (1 / 20000000 : ℝ) := by
  have hs : Mem (center + (step : ℂ))
      (rational config.precision (1 / 2 + step) ordinate) := by
    convert mem_rational (by decide : config.precision ≤ 0) (1 / 2 + step) ordinate using 1
    simp only [center, Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    ring
  have hh := norm_sub_lt_of_closeCheck step_check hs
  convert hh using 1 <;>
    simp only [ZetaLowZeroSamples.slope, Rat.cast_mul, Rat.cast_div, Rat.cast_one,
      Rat.cast_ofNat]
  congr 2
  ring

end RiemannGaussian.ZetaLowZeroSamples

namespace RiemannGaussian.ZetaLowZeroIsolation
noncomputable section
open Complex Metric AnalyticNewtonIsolation ZetaLowZeroSamples
open Set hiding center

private theorem ordinate_range : (ordinate : ℝ) ∈ Icc (14 : ℝ) 15 := by
  norm_num [ordinate]

private theorem center_eq : center = ZetaLowZeroDisc.center (ordinate : ℝ) := by
  simp [center, ZetaLowZeroDisc.center]

private theorem analytic_small {r : ℝ} (hr : r ≤ 1 / 4) :
    AnalyticOnNhd ℂ riemannZeta (closedBall center r) := by
  rw [center_eq]
  exact (ZetaLowZeroDisc.analytic_on_disc ordinate_range).mono
    (closedBall_subset_closedBall hr)

private theorem second_small {r : ℝ} (hr : r ≤ 1 / 8) {z : ℂ}
    (hz : z ∈ closedBall center r) : ‖deriv (deriv riemannZeta) z‖ ≤ 4096 := by
  rw [center_eq] at hz
  exact ZetaLowZeroDisc.second_derivative_bound ordinate_range
    (closedBall_subset_closedBall hr hz)

/-- The two certified values constrain the actual derivative at the center. -/
theorem derivative_center_bound : ‖deriv riemannZeta center - slope‖ ≤ (1 / 14 : ℝ) := by
  have hh := derivative_from_two_values (f := riemannZeta) (c := center) (a := slope)
    (h := (step : ℝ)) (E := 4096) (by norm_num [step]) (by norm_num)
    (analytic_small (by norm_num [step]))
    (fun z hz => second_small (by norm_num [step]) hz)
  have h0 := norm_center_lt
  have h1 := norm_step_lt
  norm_num only [step, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat] at hh h1
  linarith

/-- The complete derivative error is small throughout the isolating disc. -/
theorem derivative_disc_bound {z : ℂ}
    (hz : z ∈ closedBall center (1 / 100000 : ℝ)) :
    ‖deriv riemannZeta z - slope‖ ≤ (1 / 8 : ℝ) := by
  have hv := derivative_variation (f := riemannZeta) (by norm_num : (0 : ℝ) ≤ 1 / 100000)
    (analytic_small (by norm_num)) (fun w hw => second_small (by norm_num) hw) hz
  have hn := mem_closedBall_iff_norm.mp hz
  have ht := norm_sub_le_norm_sub_add_norm_sub (deriv riemannZeta z)
    (deriv riemannZeta center) slope
  linarith [derivative_center_bound]

private theorem slope_norm_lower : (3 / 4 : ℝ) ≤ ‖slope‖ := by
  have hh := Complex.abs_re_le_norm slope
  norm_num [ZetaLowZeroSamples.slope] at hh
  exact hh

/-- There is one unique zero in the entire specified complex disc, and its
actual complex derivative is nonzero. All numerical hypotheses are discharged. -/
theorem exists_unique_simple_zero :
    ∃ z ∈ closedBall center (1 / 100000 : ℝ), riemannZeta z = 0 ∧
      deriv riemannZeta z ≠ 0 ∧
      ∀ w ∈ closedBall center (1 / 100000 : ℝ), riemannZeta w = 0 → w = z := by
  apply exists_unique_zero (a := slope) (q := (1 / 4 : NNReal)) (by norm_num)
    (by intro he; have hh := slope_norm_lower; rw [he, norm_zero] at hh; norm_num at hh)
    (by norm_num)
  · exact fun z hz => (analytic_small (by norm_num) z hz).differentiableAt
  · intro z hz
    have hd := derivative_disc_bound hz
    norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    linarith [slope_norm_lower]
  · have hh := norm_center_lt
    norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    nlinarith [slope_norm_lower]

/-- Every zero in the isolation disc is strictly within twenty billionths
of its rational center. In particular the outer contour contains no zero. -/
theorem zero_distance_lt {z : ℂ}
    (hz : z ∈ closedBall center (1 / 100000 : ℝ)) (hzero : riemannZeta z = 0) :
    ‖z - center‖ < (1 / 50000000 : ℝ) := by
  let g : ℂ → ℂ := fun w => riemannZeta w - slope * w
  have hg (w : ℂ) (hw : w ∈ closedBall center (1 / 100000 : ℝ)) :
      HasDerivAt g (deriv riemannZeta w - slope) w := by
    apply HasDerivAt.sub
    · exact (analytic_small (by norm_num) w hw).differentiableAt.hasDerivAt
    · simpa only [mul_one, id_eq] using (hasDerivAt_id w).const_mul slope
  have hh := (convex_closedBall center (1 / 100000 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun w hw => (hg w hw).hasDerivWithinAt)
    (fun w hw => derivative_disc_bound hw) (mem_closedBall_self (by norm_num)) hz
  have he : slope * (z - center) = -(g z - g center) - riemannZeta center := by
    simp only [g, hzero]
    ring
  have hb : ‖slope‖ * ‖z - center‖ ≤ (1 / 8 : ℝ) * ‖z - center‖ +
      ‖riemannZeta center‖ := by
    rw [← norm_mul, he]
    exact (norm_sub_le _ _).trans (by simpa only [norm_neg] using add_le_add hh le_rfl)
  nlinarith [slope_norm_lower, norm_nonneg (z - center), norm_center_lt]

/-- The entire explicit circular boundary is zero-free, as needed to use
the isolating disc in a subsequent completeness count. -/
theorem nonzero_on_sphere {z : ℂ} (hz : z ∈ sphere center (1 / 100000 : ℝ)) :
    riemannZeta z ≠ 0 := by
  intro hzero
  have hh := zero_distance_lt (sphere_subset_closedBall hz) hzero
  rw [mem_sphere_iff_norm.mp hz] at hh
  norm_num at hh

private theorem positive_im {z : ℂ} (hz : z ∈ closedBall center (1 / 100000 : ℝ)) :
    0 < z.im := by
  have hh := (Complex.abs_im_le_norm (z - center)).trans (mem_closedBall_iff_norm.mp hz)
  have hc : center.im = (ordinate : ℝ) := by simp [center]
  rw [sub_im, hc] at hh
  have ht := ordinate_range.1
  linarith [(abs_le.mp hh).1]

private theorem reflected_mem {z : ℂ} (hz : z ∈ closedBall center (1 / 100000 : ℝ)) :
    1 - starRingEnd ℂ z ∈ closedBall center (1 / 100000 : ℝ) := by
  have hc : 1 - starRingEnd ℂ center = center := by
    apply Complex.ext <;> norm_num [center]
  have he : (1 - starRingEnd ℂ z) - center = -starRingEnd ℂ (z - center) := by
    rw [map_sub]
    linear_combination hc
  apply mem_closedBall_iff_norm.mpr
  rw [he, norm_neg, norm_conj]
  exact mem_closedBall_iff_norm.mp hz

/-- The unique verified zero lies exactly on the critical line and has
analytic multiplicity one. Completeness outside this disc is not asserted. -/
theorem isolated_critical_zero :
    ∃ z ∈ closedBall center (1 / 100000 : ℝ), riemannZeta z = 0 ∧
      z.re = 1 / 2 ∧ analyticOrderAt riemannZeta z = 1 ∧
      ∀ w ∈ closedBall center (1 / 100000 : ℝ), riemannZeta w = 0 → w = z := by
  obtain ⟨z, hz, hzero, hderiv, hunique⟩ := exists_unique_simple_zero
  have him := positive_im hz
  have hn : IsNontrivialZetaZero z := by
    refine ⟨hzero, ?_, ?_⟩
    · rintro ⟨n, he⟩
      have hh := congrArg Complex.im he
      norm_num at hh
      linarith
    · intro he
      norm_num [he] at him
  let rho : NontrivialZetaZero := ⟨z, hn⟩
  have hpartner : riemannZeta (1 - starRingEnd ℂ z) = 0 :=
    (NontrivialZetaZero.conjugatePartner rho).2.1
  have he := hunique _ (reflected_mem hz) hpartner
  have hre : z.re = 1 / 2 := by
    have hh := congrArg Complex.re he
    simp only [sub_re, one_re, conj_re] at hh
    linarith
  exact ⟨z, hz, hzero, hre,
    (analytic_small (by norm_num) z hz).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hzero hderiv,
    hunique⟩

/-- Every zero in this explicit disc is on the line; this is a local
exclusion of off-line zeros, with the central zero itself retained. -/
theorem local_critical_line {s : ℂ} (hs : s ∈ closedBall center (1 / 100000 : ℝ))
    (hzero : riemannZeta s = 0) : s.re = 1 / 2 := by
  obtain ⟨z, _, _, hre, _, hu⟩ := isolated_critical_zero
  exact (congrArg Complex.re (hu s hs hzero)).trans hre

end
end RiemannGaussian.ZetaLowZeroIsolation
