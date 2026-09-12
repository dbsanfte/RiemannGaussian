/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.AnalyticDiscBoundarySequence
import RiemannGaussian.AnalyticDiscCanonicalControl
import RiemannGaussian.ZetaNearOneFullDisc
import RiemannGaussian.ZetaNearOneSignedBound

/-!
# Signed zeta control at the entire available radius

Complete canonical decompositions on zero-free circles approaching the
outer disc retain each signed pole and its correction. Passing their
scalar bounds to the full radius removes every fixed fractional radius
loss. Zeros on the outer boundary are allowed throughout.
-/

namespace RiemannGaussian.ZetaNearOneFullRadius
noncomputable section
open Complex Filter Metric Set MeromorphicOn ZetaNearOneLocalDisc ZetaNearOneLogProfile
open DerivativeOrderComparison ZetaNearOneCanonical ZetaNearOneJensen ZetaNearOneSignedBound
open AnalyticDiscSignedDerivative
open scoped Topology

/-- At each eligible interior circle the actual zeta function has a
complete controlled canonical decomposition and its full complex identity. -/
theorem controlled_decomp_at_radius (k : ℕ) (hk : 2 ≤ k) {t x r : ℝ}
    (ht : 2 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta k / 4) (hr : 0 < r)
    (hrδ : r ≤ delta k) (hs : ∀ z : ℂ, ‖z‖ = r → translated x t z ≠ 0) :
    ∃ g : ℂ → ℂ, ECanonicalDecomp (translated x t) g r ∧
      ‖logDeriv g 0‖ ≤ 2 * allowance k x t / r ∧
      logDeriv riemannZeta (center x t) = logDeriv g 0 + coupledSum x t r := by
  have hf := (ZetaNearOneFullDisc.analyticOnNhd_translated k hk ht hx hx').mono
    (closedBall_subset_closedBall hrδ)
  have hzero : translated x t 0 ≠ 0 := by
    rw [translated_zero]
    exact center_ne_zero t hx
  have hc : -Real.log ‖translated x t 0‖ ≤ Real.log (1 + 1 / x) := by
    rw [translated_zero]
    exact center_log_bound t hx
  obtain ⟨g, D, hb, he⟩ := AnalyticDiscCanonicalControl.exists_controlled_decomp
    hr hf hzero hs (allowance_pos k t hx)
    (fun z hz ↦ ZetaNearOneFullDisc.norm_translated_le k hk ht hx hx'
      ((closedBall_subset_closedBall hrδ) hz)) hc
  rw [logDeriv_translated k (by omega) ht hx hx'] at he
  exact ⟨g, D, hb, he⟩

/-- All actual coupled zero terms have favorable sign at every chosen
circle, leaving only the sharp radius-dependent analytic allowance. -/
theorem neg_logDeriv_re_le_at_radius (k : ℕ) (hk : 2 ≤ k) {t x r : ℝ}
    (ht : 2 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta k / 4) (hr : 0 < r)
    (hrδ : r ≤ delta k) (hs : ∀ z : ℂ, ‖z‖ = r → translated x t z ≠ 0) :
    (-logDeriv riemannZeta (center x t)).re ≤ 2 * allowance k x t / r := by
  obtain ⟨g, _, hb, he⟩ := controlled_decomp_at_radius k hk ht hx hx' hr hrδ hs
  have hf := (ZetaNearOneFullDisc.analyticOnNhd_translated k hk ht hx hx').mono
    (closedBall_subset_closedBall hrδ)
  have hsum := coupledSum_nonneg hx hr hf
  have hg : (-logDeriv g 0).re ≤ ‖logDeriv g 0‖ := by
    simpa only [norm_neg] using Complex.re_le_norm (-logDeriv g 0)
  rw [he, neg_add, Complex.add_re]
  simp only [Complex.neg_re] at hg ⊢
  linarith

/-- The selected zero contributes its complete multiplicity and exact
radial correction on every zero-free circle enclosing it. -/
theorem neg_logDeriv_re_le_sub_zero_at_radius (k : ℕ) (hk : 2 ≤ k)
    (ρ : NontrivialZetaZero) {x r : ℝ} (ht : 2 ≤ |ρ.1.im|)
    (hx : 0 < x) (hx' : x ≤ delta k / 4) (hr : 0 < r) (hrδ : r ≤ delta k)
    (hs : ∀ z : ℂ, ‖z‖ = r → translated x ρ.1.im z ≠ 0)
    (hnear : x + 1 - ρ.1.re < r) :
    (-logDeriv riemannZeta (center x ρ.1.im)).re ≤ 2 * allowance k x ρ.1.im / r -
      (analyticZetaZeroMultiplicity ρ : ℝ) *
        (1 / (x + 1 - ρ.1.re) - (x + 1 - ρ.1.re) / r ^ 2) := by
  obtain ⟨g, _, hb, he⟩ := controlled_decomp_at_radius k hk ht hx hx' hr hrδ hs
  have hf := (ZetaNearOneFullDisc.analyticOnNhd_translated k hk ht hx hx').mono
    (closedBall_subset_closedBall hrδ)
  have hsource := source_le_sum ρ hx hr hf hnear
  have hg : (-logDeriv g 0).re ≤ ‖logDeriv g 0‖ := by
    simpa only [norm_neg] using Complex.re_le_norm (-logDeriv g 0)
  rw [he, neg_add, Complex.add_re]
  simp only [Complex.neg_re] at hg ⊢
  linarith

/-- The actual logarithmic derivative is bounded at the full available
radius, even when that outer sphere contains zeta zeros. -/
theorem neg_logDeriv_re_le (k : ℕ) (hk : 2 ≤ k) {t x : ℝ}
    (ht : 2 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta k / 4) :
    (-logDeriv riemannZeta (center x t)).re ≤ 2 * allowance k x t / delta k := by
  have hδ := delta_pos k
  have hzero : translated x t 0 ≠ 0 := by
    rw [translated_zero]
    exact center_ne_zero t hx
  obtain ⟨r, hlim, hr⟩ := AnalyticDiscBoundarySequence.exists_sphere_tendsto hδ
    (ZetaNearOneFullDisc.analyticOnNhd_translated k hk ht hx hx') hzero
  have hl : Tendsto (fun n : ℕ ↦ 2 * allowance k x t / r n) atTop
      (𝓝 (2 * allowance k x t / delta k)) :=
    tendsto_const_nhds.div hlim hδ.ne'
  exact ge_of_tendsto' hl (fun n ↦ neg_logDeriv_re_le_at_radius k hk ht hx hx'
    (hr n).1 (hr n).2.1.le (hr n).2.2)

/-- Passing the complete signed source inequality to the full radius
retains the exact endpoint correction. No fixed fraction of the analytic
radius, zero multiplicity or reciprocal-distance source is discarded. -/
theorem neg_logDeriv_re_le_sub_zero (k : ℕ) (hk : 2 ≤ k) (ρ : NontrivialZetaZero)
    {x : ℝ} (ht : 2 ≤ |ρ.1.im|) (hx : 0 < x) (hx' : x ≤ delta k / 4)
    (hnear : x + 1 - ρ.1.re < delta k) :
    (-logDeriv riemannZeta (center x ρ.1.im)).re ≤
      2 * allowance k x ρ.1.im / delta k - (analyticZetaZeroMultiplicity ρ : ℝ) *
        (1 / (x + 1 - ρ.1.re) - (x + 1 - ρ.1.re) / (delta k) ^ 2) := by
  have hδ := delta_pos k
  have hzero : translated x ρ.1.im 0 ≠ 0 := by
    rw [translated_zero]
    exact center_ne_zero ρ.1.im hx
  obtain ⟨r, hlim, hr⟩ := AnalyticDiscBoundarySequence.exists_sphere_tendsto hδ
    (ZetaNearOneFullDisc.analyticOnNhd_translated k hk ht hx hx') hzero
  have hl : Tendsto (fun n : ℕ ↦ 2 * allowance k x ρ.1.im / r n -
      (analyticZetaZeroMultiplicity ρ : ℝ) *
        (1 / (x + 1 - ρ.1.re) - (x + 1 - ρ.1.re) / (r n) ^ 2)) atTop
      (𝓝 (2 * allowance k x ρ.1.im / delta k - (analyticZetaZeroMultiplicity ρ : ℝ) *
        (1 / (x + 1 - ρ.1.re) - (x + 1 - ρ.1.re) / (delta k) ^ 2))) :=
    (tendsto_const_nhds.div hlim hδ.ne').sub
      ((tendsto_const_nhds.sub (tendsto_const_nhds.div (hlim.pow 2)
        (pow_ne_zero 2 hδ.ne'))).const_mul _)
  apply ge_of_tendsto hl
  filter_upwards [hlim.eventually (lt_mem_nhds hnear)] with n hn
  exact neg_logDeriv_re_le_sub_zero_at_radius k hk ρ ht hx hx'
    (hr n).1 (hr n).2.1.le (hr n).2.2 hn

end
end RiemannGaussian.ZetaNearOneFullRadius
