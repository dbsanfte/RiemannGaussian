/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaVinogradovLocalDisc
import RiemannGaussian.ZetaNearOneCanonical
import RiemannGaussian.AnalyticDiscCanonicalControl

/-!
# Canonical zero removal with the actual Vinogradov allowance

The complete high-height disc bound supplies the canonical residual
estimate. The existing translated zeta function, full divisor and
coupled kernel are retained. Only the analytic remainder is estimated;
the exact multiplicity-weighted zero contribution stays complex.
-/

namespace RiemannGaussian.ZetaVinogradovCanonical
noncomputable section
open Complex Metric Set MeromorphicOn
open VinogradovNearOneBudget VinogradovScaleSelection ZetaVinogradovLocalDisc
open ZetaNearOneLocalDisc (center)
open ZetaNearOneJensen (center_ne_zero center_log_bound)
open ZetaNearOneCanonical (translated translated_zero)
open AnalyticDiscCanonicalBounds AnalyticDiscSignedDerivative

/-- The complete profile and actual reciprocal-zeta center cost. -/
def allowance (n : ℕ) (x t : ℝ) : ℝ := profile n t + Real.log (1 + 1 / x)

/-- The actual center makes the full allowance strictly positive. -/
theorem allowance_pos {n : ℕ} (hn : 1 ≤ n) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    0 < allowance n x t := by
  have hi : 0 < 1 / x := by positivity
  have hlog : 0 < Real.log (1 + 1 / x) := Real.log_pos (by linarith)
  unfold allowance
  linarith [profile_nonneg hn t]

/-- The whole translated disc is genuinely analytic, with no zero-free
disc premise and no exception for zeros inside its boundary. -/
theorem analyticOnNhd_translated (n : ℕ) (hn : 12 ≤ n) {t x : ℝ}
    (ht : (heightThreshold n : ℝ) + 1 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta n / 4) :
    AnalyticOnNhd ℂ (translated x t) (closedBall 0 (delta n / 2)) := by
  intro z hz
  have hm : z + center x t ∈ closedBall (center x t) (delta n / 2) := by
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero] using hz
  exact (analyticOnNhd_disc n hn ht hx hx' _ hm).comp
    (f := fun w : ℂ ↦ w + center x t) (by fun_prop)

/-- The actual high-moment zeta profile bounds the complete translated disc. -/
theorem norm_translated_le (n : ℕ) (hn : 12 ≤ n) {t x : ℝ}
    (ht : (heightThreshold n : ℝ) + 1 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta n / 4)
    {z : ℂ} (hz : z ∈ closedBall 0 (delta n / 2)) :
    ‖translated x t z‖ ≤ Real.exp (profile n t) := by
  apply disc_norm_bound n hn ht hx hx'
  simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero] using hz

/-- Translation by the Euler-side center preserves the actual complex
logarithmic derivative at zero. -/
theorem logDeriv_translated (n : ℕ) (hn : 12 ≤ n) {t x : ℝ}
    (ht : (heightThreshold n : ℝ) + 1 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta n / 4) :
    logDeriv (translated x t) 0 = logDeriv riemannZeta (center x t) := by
  have hd := (analyticOnNhd_disc n hn ht hx hx' _
    (mem_closedBall_self (div_nonneg (delta_pos n).le (by norm_num)))).differentiableAt
  change logDeriv (riemannZeta ∘ (· + center x t)) 0 = _
  rw [logDeriv_comp (by simpa using hd) (by fun_prop)]
  simp

/-- Complete zero removal has the new explicit residual bound and
retains the full signed divisor identity, at an actually selected radius. -/
theorem exists_controlled_decomp (n : ℕ) (hn : 12 ≤ n) {t x : ℝ}
    (ht : (heightThreshold n : ℝ) + 1 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta n / 4) :
    ∃ r : ℝ, delta n / 4 < r ∧ r < 3 * delta n / 8 ∧
      ∃ g : ℂ → ℂ, ECanonicalDecomp (translated x t) g r ∧
        (∀ z : ℂ, ‖z‖ = r → translated x t z ≠ 0) ∧
        ‖logDeriv g 0‖ ≤ 8 * allowance n x t / delta n ∧
        logDeriv riemannZeta (center x t) = logDeriv g 0 +
          ∑ᶠ a, divisor (translated x t) (ball 0 r) a • kernel r a := by
  have hδ := delta_pos n
  have hf := analyticOnNhd_translated n hn ht hx hx'
  have hf0 : translated x t 0 ≠ 0 := by rw [translated_zero]; exact center_ne_zero t hx
  obtain ⟨r, hrlo, hrhi, hs⟩ := exists_zeroFree_sphere (by positivity : 0 < delta n / 2) hf hf0
  have hr : 0 < r := by linarith
  have hrR : r ≤ delta n / 2 := by linarith
  have hfr := hf.mono (closedBall_subset_closedBall hrR)
  have hA := allowance_pos (by omega : 1 ≤ n) t hx
  obtain ⟨g, D, hb, he⟩ := AnalyticDiscCanonicalControl.exists_controlled_decomp hr hfr hf0 hs
    hA (fun z hz => norm_translated_le n hn ht hx hx'
      ((closedBall_subset_closedBall hrR) hz))
    (by rw [translated_zero]; exact center_log_bound t hx)
  have hres : ‖logDeriv g 0‖ ≤ 8 * allowance n x t / delta n := by
    apply hb.trans
    have h := div_le_div_of_nonneg_left (by positivity : 0 ≤ 2 * allowance n x t)
      (by positivity : 0 < delta n / 4) (by linarith : delta n / 4 ≤ r)
    convert h using 1 <;> unfold allowance <;> ring
  rw [logDeriv_translated n hn ht hx hx'] at he
  exact ⟨r, by linarith, by linarith, g, D, hs, hres, he⟩

end
end RiemannGaussian.ZetaVinogradovCanonical
