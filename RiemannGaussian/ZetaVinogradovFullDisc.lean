/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaVinogradovCanonical

/-!
# The full available Vinogradov disc

The actual growth bound covers the entire radius Delta_n. Enlarging the
previous half-radius disc adds no height exponent or profile cost. No
zero-free-disc hypothesis is imposed; all interior zeros are retained.
-/

namespace RiemannGaussian.ZetaVinogradovFullDisc
noncomputable section
open Complex Metric Set VinogradovNearOneBudget VinogradovScaleSelection
open ZetaVinogradovLocalDisc
open ZetaNearOneLocalDisc (center)
open ZetaNearOneCanonical (translated)

/-- The entire radius Delta_n lies inside the proved strip and unit
height window at every eligible Euler-side center. -/
theorem disc_geometry (n : ℕ) (t : ℝ) {x : ℝ} (hx : 0 < x) (hx' : x ≤ delta n / 4)
    {s : ℂ} (hs : s ∈ closedBall (center x t) (delta n)) :
    line n ≤ s.re ∧ s.re ≤ 3 / 2 ∧ |s.im - t| ≤ 1 := by
  have hn : ‖s - center x t‖ ≤ delta n := by
    simpa only [mem_closedBall, dist_eq_norm] using hs
  have hre := (Complex.abs_re_le_norm (s - center x t)).trans hn
  have him := (Complex.abs_im_le_norm (s - center x t)).trans hn
  simp only [ZetaNearOneLocalDisc.center, Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, add_zero] at hre
  simp only [ZetaNearOneLocalDisc.center, Complex.sub_im, Complex.add_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, one_mul, zero_add] at him
  have hδ := delta_le n
  refine ⟨?_, ?_, ?_⟩
  · unfold line
    linarith [(abs_le.mp hre).1]
  · linarith [(abs_le.mp hre).2]
  · linarith

/-- The full actual translated disc is analytic, with the zeta pole
excluded by the same original buffered height condition. -/
theorem analyticOnNhd_translated (n : ℕ) (hn : 12 ≤ n) {t x : ℝ}
    (ht : (heightThreshold n : ℝ) + 1 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta n / 4) :
    AnalyticOnNhd ℂ (translated x t) (closedBall 0 (delta n)) := by
  have hbT : (rootBase n : ℝ) ≤ heightThreshold n := by
    exact_mod_cast rootBase_le_heightThreshold (show 1 ≤ n by omega)
  have hb : (16 : ℝ) ≤ rootBase n := by exact_mod_cast rootBase_ge_sixteen n
  intro z hz
  have hm : z + center x t ∈ closedBall (center x t) (delta n) := by
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero] using hz
  have ha := analyticOn_riemannZeta (z + center x t)
    (ZetaNearOneLocalDisc.ne_one_of_window (by linarith) (disc_geometry n t hx hx' hm).2.2)
  exact ha.comp (f := fun w : ℂ ↦ w + center x t) (by fun_prop)

/-- The entire enlarged disc retains the original Vinogradov profile
with no additional height or constant allowance. -/
theorem norm_translated_le (n : ℕ) (hn : 12 ≤ n) {t x : ℝ}
    (ht : (heightThreshold n : ℝ) + 1 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta n / 4)
    {z : ℂ} (hz : z ∈ closedBall 0 (delta n)) :
    ‖translated x t z‖ ≤ Real.exp (profile n t) := by
  have hm : z + center x t ∈ closedBall (center x t) (delta n) := by
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero] using hz
  obtain ⟨hlo, hhi, hw⟩ := disc_geometry n t hx hx' hm
  exact local_norm_bound n hn ht hlo hhi hw

end
end RiemannGaussian.ZetaVinogradovFullDisc
