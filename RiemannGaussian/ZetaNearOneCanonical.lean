/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.AnalyticDiscLogarithm
import RiemannGaussian.AnalyticDiscSignedDerivative
import RiemannGaussian.ZetaNearOneJensen

/-!
# Controlled canonical decomposition on actual shrinking zeta discs

The Gaussian strip bound and full Euler center allowance discharge every
premise of the scale-uniform canonical residual estimate. A complete
zero-free boundary is selected inside the proved analytic disc. The exact
complex logarithmic derivative retains the entire coupled divisor.
-/

namespace RiemannGaussian.ZetaNearOneCanonical
noncomputable section
open Complex Metric Set MeromorphicOn ZetaNearOneLocalDisc ZetaNearOneLogProfile
open DirichletPowerParameters DerivativeOrderComparison ZetaNearOneJensen
open AnalyticDiscCanonicalBounds AnalyticDiscSignedDerivative

/-- Zeta translated to the actual Euler-side center. -/
def translated (x t : ℝ) (z : ℂ) : ℂ := riemannZeta (z + center x t)

/-- Translation retains the actual center value. -/
theorem translated_zero (x t : ℝ) : translated x t 0 = riemannZeta (center x t) := by
  simp [translated]

/-- The entire outer translated disc is analytic, including its zeros. -/
theorem analyticOnNhd_translated (k : ℕ) (hk : 1 ≤ k) {t x : ℝ}
    (ht : 2 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta k / 4) :
    AnalyticOnNhd ℂ (translated x t) (closedBall 0 (delta k / 2)) := by
  intro z hz
  have hm : z + center x t ∈ closedBall (center x t) (delta k / 2) := by
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero] using hz
  exact (analyticOnNhd_disc k hk ht hx hx' _ hm).comp (f := fun w : ℂ ↦ w + center x t)
    (show AnalyticAt ℂ (fun w : ℂ ↦ w + center x t) z by fun_prop)

/-- The actual zeta bound controls the entire translated disc. -/
theorem norm_translated_le (k : ℕ) (hk : 1 ≤ k) {t x : ℝ}
    (ht : 2 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta k / 4)
    {z : ℂ} (hz : z ∈ closedBall 0 (delta k / 2)) :
    ‖translated x t z‖ ≤ Real.exp (profile k t + 14) := by
  have hm : z + center x t ∈ closedBall (center x t) (delta k / 2) := by
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero] using hz
  obtain ⟨hlo, hhi, him⟩ := disc_geometry k hk t hx hx' hm
  exact local_norm_bound k hk ht hlo hhi him

/-- The center translation has derivative one, so it preserves the
full complex logarithmic derivative. -/
theorem logDeriv_translated (k : ℕ) (hk : 1 ≤ k) {t x : ℝ}
    (ht : 2 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta k / 4) :
    logDeriv (translated x t) 0 = logDeriv riemannZeta (center x t) := by
  have hp : 0 ≤ delta k / 2 := div_nonneg (delta_pos k).le (by norm_num)
  have hd := (analyticOnNhd_disc k hk ht hx hx' _ (mem_closedBall_self hp)).differentiableAt
  change logDeriv (riemannZeta ∘ (· + center x t)) 0 = _
  rw [logDeriv_comp (by simpa using hd) (by fun_prop)]
  simp

/-- The complete explicit logarithmic allowance is strictly positive. -/
theorem allowance_pos (k : ℕ) (t : ℝ) {x : ℝ} (hx : 0 < x) : 0 < allowance k x t := by
  have hi : 0 ≤ 1 / x := by positivity
  have hl : 0 ≤ Real.log (1 + 1 / x) := Real.log_nonneg (by linarith)
  unfold allowance
  linarith [profile_nonneg k t]

/-- An actual complete canonical divisor has a controlled residual and
an exact signed complex derivative identity at a shrinking radius. -/
theorem exists_controlled_decomp (k : ℕ) (hk : 1 ≤ k) {t x : ℝ}
    (ht : 2 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta k / 4) :
    ∃ r : ℝ, delta k / 4 < r ∧ r < 3 * delta k / 8 ∧
      ∃ g : ℂ → ℂ, ECanonicalDecomp (translated x t) g r ∧
        (∀ z : ℂ, ‖z‖ = r → translated x t z ≠ 0) ∧
        ‖logDeriv g 0‖ ≤ 8 * allowance k x t / delta k ∧
        logDeriv riemannZeta (center x t) = logDeriv g 0 +
          ∑ᶠ a, divisor (translated x t) (ball 0 r) a • kernel r a := by
  have hδ := delta_pos k
  have houter : 0 < delta k / 2 := by positivity
  have hf := analyticOnNhd_translated k hk ht hx hx'
  have hf0 : translated x t 0 ≠ 0 := by rw [translated_zero]; exact center_ne_zero t hx
  obtain ⟨r, hrlo, hrhi, hs⟩ := exists_zeroFree_sphere houter hf hf0
  have hr : 0 < r := by linarith
  have hrR : r ≤ delta k / 2 := by linarith
  have hfr := hf.mono (closedBall_subset_closedBall hrR)
  obtain ⟨g, D⟩ := exists_decomp hr hfr hf0
  have hbound : ∀ z ∈ closedBall 0 r, ‖g z‖ ≤ Real.exp (profile k t + 14) := by
    intro z hz
    apply AnalyticDiscCanonicalBounds.norm_le hr hfr hs D _ hz
    intro w hw
    exact norm_translated_le k hk ht hx hx'
      ((closedBall_subset_closedBall hrR) (sphere_subset_closedBall hw))
  have hcenter : -Real.log ‖g 0‖ ≤ Real.log (1 + 1 / x) := by
    have hn := center_norm_le hr hfr hf0 hs D
    have hlog := Real.log_le_log (norm_pos_iff.mpr hf0) hn
    have hc := center_log_bound t hx
    rw [← translated_zero x t] at hc
    linarith
  have hb := AnalyticDiscLogarithm.norm_logDeriv_center_le_sharp hr D.analyticOnNhd D.ne_zero
    (B := profile k t + 14) (C := Real.log (1 + 1 / x))
    (allowance_pos k t hx) hbound hcenter
  have hres : ‖logDeriv g 0‖ ≤ 8 * allowance k x t / delta k := by
    apply hb.trans
    have hA := allowance_pos k t hx
    have hh := div_le_div_of_nonneg_left
      (by positivity : 0 ≤ 2 * allowance k x t)
      (by positivity : 0 < delta k / 4) (by linarith : delta k / 4 ≤ r)
    convert hh using 1 <;> unfold allowance <;> ring
  refine ⟨r, by linarith, by linarith, g, D, hs, hres, ?_⟩
  rw [← logDeriv_translated k hk ht hx hx']
  exact logDeriv_center_eq hr hfr hf0 hs D

end
end RiemannGaussian.ZetaNearOneCanonical
