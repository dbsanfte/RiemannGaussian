/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaNearOneAngularBound
import RiemannGaussian.ZetaEulerGaussianDisc
import RiemannGaussian.ZetaNearOneSharpAngularBound

/-!
# The actual signed angular bound with direct Euler growth

The height-uniform ordinary reconstruction reaches the complete signed
boundary moment and selected zero source. The full Gaussian correction,
Euler reciprocal lower bound, multiplicity and radial term are retained.
The exact removed allowance is log(4/delta_k) on every frequency channel.
-/

namespace RiemannGaussian.ZetaEulerAngularBound
noncomputable section
open Complex Filter Metric Set MeromorphicOn ZetaNearOneLocalDisc ZetaNearOneLogProfile
open DerivativeOrderComparison ZetaNearOneCanonical ZetaNearOneJensen ZetaNearOneSignedBound
open AnalyticDiscBoundaryMoment
open scoped Topology

/-- The complete angular allowance retains the true Gaussian and
rational reconstruction costs at the original height and radius. -/
def allowance (k : ℕ) (x t : ℝ) : ℝ :=
  ZetaEulerLogProfile.profile k t + ZetaGaussianSharpDisc.correction k t + Real.log (1 + 1 / x)

/-- The sharper full allowance is nonnegative throughout its actual
analytic range. -/
theorem allowance_nonneg (k : ℕ) (hk : 2 ≤ k) {x t : ℝ}
    (ht : 2 ≤ |t|) (hx : 0 < x) : 0 ≤ allowance k x t := by
  have hp := ZetaEulerLogProfile.profile_ge_six k t
  have hc := (ZetaGaussianSharpDisc.correction_bounds k hk ht).1
  have hl : 0 ≤ Real.log (1 + 1 / x) := by
    apply Real.log_nonneg
    have hi : 0 ≤ 1 / x := by positivity
    linarith
  unfold allowance
  linarith

/-- The removed eta and coefficient cost is an exact height-independent
identity for the complete allowance, before any bound or channel sum. -/
theorem allowance_add_gain (k : ℕ) (x t : ℝ) :
    allowance k x t + ZetaEulerLogProfile.gain k =
      ZetaNearOneSharpAngularBound.allowance k x t := by
  have h := ZetaEulerLogProfile.profile_add_gain k t
  unfold allowance ZetaNearOneSharpAngularBound.allowance
  linarith

/-- Every eligible channel retains the earlier Gaussian improvement
and additionally removes the nonnegative eta-division allowance. -/
theorem allowance_add_twelve_le_previous (k : ℕ) (hk : 2 ≤ k) (x : ℝ) {t : ℝ}
    (ht : 2 ≤ |t|) : allowance k x t + 12 ≤ ZetaNearOneJensen.allowance k x t := by
  have h := ZetaNearOneSharpAngularBound.allowance_add_twelve_le_previous k hk x ht
  rw [← allowance_add_gain] at h
  linarith [ZetaEulerLogProfile.gain_nonneg k]

/-- The actual signed angular moment uses upper growth only on the
left and the full Euler reciprocal bound on the right. -/
theorem boundary_moment_le (k : ℕ) (hk : 2 ≤ k) {t x r : ℝ}
    (ht : 2 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta k / 4) (hr : 0 < r)
    (hrδ : r ≤ delta k) (hs : ∀ z : ℂ, ‖z‖ = r → translated x t z ≠ 0) :
    (-moment (translated x t) r).re ≤ 2 * allowance k x t / (Real.pi * r) := by
  have hf := (ZetaNearOneFullDisc.analyticOnNhd_translated k hk ht hx hx').mono
    (closedBall_subset_closedBall hrδ)
  apply AnalyticDiscSignedBoundary.neg_moment_re_le hr
    (hf.continuousOn.mono sphere_subset_closedBall)
    (fun z hz ↦ hs z (by simpa only [mem_sphere, dist_zero_right] using hz))
  · intro z hz _
    have hn := ZetaEulerGaussianDisc.norm_translated_le k hk ht hx hx'
      (closedBall_subset_closedBall hrδ (sphere_subset_closedBall hz))
    have hpos : 0 < ‖translated x t z‖ := norm_pos_iff.mpr
      (hs z (by simpa only [mem_sphere, dist_zero_right] using hz))
    simpa only [Real.log_exp] using Real.log_le_log hpos hn
  · intro z _ hz
    exact ZetaNearOneAngularBound.right_arc_lower t hx hz

/-- All unselected coupled zero terms have favorable sign, leaving
the actual angular allowance with its factor `1/pi` retained. -/
theorem neg_logDeriv_re_le_at_radius (k : ℕ) (hk : 2 ≤ k) {t x r : ℝ}
    (ht : 2 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta k / 4) (hr : 0 < r)
    (hrδ : r ≤ delta k) (hs : ∀ z : ℂ, ‖z‖ = r → translated x t z ≠ 0) :
    (-logDeriv riemannZeta (center x t)).re ≤ 2 * allowance k x t / (Real.pi * r) := by
  have hb := boundary_moment_le k hk ht hx hx' hr hrδ hs
  have hf := (ZetaNearOneFullDisc.analyticOnNhd_translated k hk ht hx hx').mono
    (closedBall_subset_closedBall hrδ)
  have hsum := coupledSum_nonneg hx hr hf
  rw [ZetaNearOneAngularBound.logDeriv_eq_boundary_moment_add_sum k hk ht hx hx' hr hrδ hs, neg_add, Complex.add_re,
    Complex.neg_re]
  simp only [Complex.neg_re] at hb ⊢
  linarith

/-- The selected zero's complete signed source and radial correction
remain coupled in the improved angular bound at every enclosing circle. -/
theorem neg_logDeriv_re_le_sub_zero_at_radius (k : ℕ) (hk : 2 ≤ k)
    (ρ : NontrivialZetaZero) {x r : ℝ} (ht : 2 ≤ |ρ.1.im|)
    (hx : 0 < x) (hx' : x ≤ delta k / 4) (hr : 0 < r) (hrδ : r ≤ delta k)
    (hs : ∀ z : ℂ, ‖z‖ = r → translated x ρ.1.im z ≠ 0)
    (hnear : x + 1 - ρ.1.re < r) :
    (-logDeriv riemannZeta (center x ρ.1.im)).re ≤
      2 * allowance k x ρ.1.im / (Real.pi * r) - (analyticZetaZeroMultiplicity ρ : ℝ) *
        (1 / (x + 1 - ρ.1.re) - (x + 1 - ρ.1.re) / r ^ 2) := by
  have hb := boundary_moment_le k hk ht hx hx' hr hrδ hs
  have hf := (ZetaNearOneFullDisc.analyticOnNhd_translated k hk ht hx hx').mono
    (closedBall_subset_closedBall hrδ)
  have hsource := source_le_sum ρ hx hr hf hnear
  rw [ZetaNearOneAngularBound.logDeriv_eq_boundary_moment_add_sum k hk ht hx hx' hr hrδ hs, neg_add, Complex.add_re,
    Complex.neg_re]
  simp only [Complex.neg_re] at hb ⊢
  linarith

/-- The improved angular allowance holds at the entire available
radius, including when that outer sphere contains actual zeta zeros. -/
theorem neg_logDeriv_re_le (k : ℕ) (hk : 2 ≤ k) {t x : ℝ}
    (ht : 2 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta k / 4) :
    (-logDeriv riemannZeta (center x t)).re ≤ 2 * allowance k x t / (Real.pi * delta k) := by
  have hδ := delta_pos k
  have hzero : translated x t 0 ≠ 0 := by
    rw [translated_zero]
    exact center_ne_zero t hx
  obtain ⟨r, hlim, hr⟩ := AnalyticDiscBoundarySequence.exists_sphere_tendsto hδ
    (ZetaNearOneFullDisc.analyticOnNhd_translated k hk ht hx hx') hzero
  have hl : Tendsto (fun n : ℕ ↦ 2 * allowance k x t / (Real.pi * r n)) atTop
      (𝓝 (2 * allowance k x t / (Real.pi * delta k))) :=
    tendsto_const_nhds.div (hlim.const_mul Real.pi) (mul_pos Real.pi_pos hδ).ne'
  exact ge_of_tendsto' hl (fun n ↦ neg_logDeriv_re_le_at_radius k hk ht hx hx'
    (hr n).1 (hr n).2.1.le (hr n).2.2)

/-- Passing the complete signed source bound to the full radius
retains the angular gain, actual multiplicity and exact radial correction. -/
theorem neg_logDeriv_re_le_sub_zero (k : ℕ) (hk : 2 ≤ k) (ρ : NontrivialZetaZero)
    {x : ℝ} (ht : 2 ≤ |ρ.1.im|) (hx : 0 < x) (hx' : x ≤ delta k / 4)
    (hnear : x + 1 - ρ.1.re < delta k) :
    (-logDeriv riemannZeta (center x ρ.1.im)).re ≤
      2 * allowance k x ρ.1.im / (Real.pi * delta k) - (analyticZetaZeroMultiplicity ρ : ℝ) *
        (1 / (x + 1 - ρ.1.re) - (x + 1 - ρ.1.re) / (delta k) ^ 2) := by
  have hδ := delta_pos k
  have hzero : translated x ρ.1.im 0 ≠ 0 := by
    rw [translated_zero]
    exact center_ne_zero ρ.1.im hx
  obtain ⟨r, hlim, hr⟩ := AnalyticDiscBoundarySequence.exists_sphere_tendsto hδ
    (ZetaNearOneFullDisc.analyticOnNhd_translated k hk ht hx hx') hzero
  have hl : Tendsto (fun n : ℕ ↦ 2 * allowance k x ρ.1.im / (Real.pi * r n) -
      (analyticZetaZeroMultiplicity ρ : ℝ) *
        (1 / (x + 1 - ρ.1.re) - (x + 1 - ρ.1.re) / (r n) ^ 2)) atTop
      (𝓝 (2 * allowance k x ρ.1.im / (Real.pi * delta k) - (analyticZetaZeroMultiplicity ρ : ℝ) *
        (1 / (x + 1 - ρ.1.re) - (x + 1 - ρ.1.re) / (delta k) ^ 2))) :=
    (tendsto_const_nhds.div (hlim.const_mul Real.pi) (mul_pos Real.pi_pos hδ).ne').sub
      ((tendsto_const_nhds.sub (tendsto_const_nhds.div (hlim.pow 2)
        (pow_ne_zero 2 hδ.ne'))).const_mul _)
  apply ge_of_tendsto hl
  filter_upwards [hlim.eventually (lt_mem_nhds hnear)] with n hn
  exact neg_logDeriv_re_le_sub_zero_at_radius k hk ρ ht hx hx'
    (hr n).1 (hr n).2.1.le (hr n).2.2 hn

end
end RiemannGaussian.ZetaEulerAngularBound
