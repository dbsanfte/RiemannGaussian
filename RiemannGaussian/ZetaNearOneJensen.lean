/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaNearOneLocalDisc
import RiemannGaussian.ZetaEulerReciprocalAllowance
import Mathlib.Analysis.Complex.JensenFormula

/-!
# Multiplicity-aware Jensen bounds on shrinking near-one zeta discs

The complete local logarithmic divisor mass is exactly the signed
boundary average minus the actual center logarithm. The Gaussian strip
estimate controls the boundary; the genuine Mobius series pays for the
center. Every selected zero keeps its own logarithmic distance weight.
No zero-free-disc or unproved center-value hypothesis remains.
-/

namespace RiemannGaussian.ZetaNearOneJensen
noncomputable section
open Complex Metric Set MeromorphicOn ZetaNearOneLocalDisc ZetaNearOneLogProfile
open DirichletPowerParameters DerivativeOrderComparison ZetaEulerReciprocalAllowance

/-- The full logarithmic allowance includes both the line estimate
and the explicit reciprocal-zeta cost at the safe center. -/
def allowance (k : ℕ) (x t : ℝ) : ℝ :=
  profile k t + 14 + Real.log (1 + 1 / x)

/-- The local allowance is nonnegative at every positive horizontal shift. -/
theorem allowance_nonneg (k : ℕ) (t : ℝ) {x : ℝ} (hx : 0 < x) : 0 ≤ allowance k x t := by
  have hi : 0 ≤ 1 / x := by positivity
  have hlog : 0 ≤ Real.log (1 + 1 / x) :=
    Real.log_nonneg (by linarith)
  unfold allowance
  linarith [profile_nonneg k t]

/-- The safe center is nonzero by the actual Euler-half-plane theorem. -/
theorem center_ne_zero (t : ℝ) {x : ℝ} (hx : 0 < x) : riemannZeta (center x t) ≠ 0 := by
  apply riemannZeta_ne_zero_of_one_lt_re
  simp only [ZetaNearOneLocalDisc.center, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
  linarith

/-- The center's negative logarithm has its explicit reciprocal allowance. -/
theorem center_log_bound (t : ℝ) {x : ℝ} (hx : 0 < x) :
    -Real.log ‖riemannZeta (center x t)‖ ≤ Real.log (1 + 1 / x) := by
  have hre : (center x t).re = 1 + x := by simp [ZetaNearOneLocalDisc.center]
  have h := neg_log_norm_zeta_le (s := center x t) (by rw [hre]; linarith)
  simpa only [hre, add_sub_cancel_left] using h

/-- The whole finite logarithmic divisor mass, with each exact distance
and analytic multiplicity retained. -/
def weightedMass (k : ℕ) (x t : ℝ) : ℝ :=
  ∑ᶠ u, (divisor riemannZeta (closedBall (center x t) (delta k / 2)) u : ℝ) *
    Real.log ((delta k / 2) * ‖center x t - u‖⁻¹)

/-- Exact Jensen identity for the actual shrinking disc. Its boundary
logarithm remains signed and zeros on the boundary are permitted. -/
theorem jensen_identity (k : ℕ) (hk : 1 ≤ k) {t x : ℝ}
    (ht : 2 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta k / 4) :
    Real.circleAverage (fun s => Real.log ‖riemannZeta s‖) (center x t) (delta k / 2) =
      weightedMass k x t + Real.log ‖riemannZeta (center x t)‖ := by
  have hR : 0 < delta k / 2 := by have h := delta_pos k; positivity
  have han := analyticOnNhd_disc k hk ht hx hx'
  have hj := AnalyticOnNhd.circleAverage_log_norm (R := delta k / 2) hR.ne'
    (by simpa only [abs_of_pos hR] using han) (center_ne_zero t hx)
  rw [abs_of_pos hR] at hj
  exact hj

/-- The signed boundary average has the proved local positive-log allowance,
with genuine integrability through any boundary zeros. -/
theorem circle_average_bound (k : ℕ) (hk : 1 ≤ k) {t x : ℝ}
    (ht : 2 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta k / 4) :
    Real.circleAverage (fun s => Real.log ‖riemannZeta s‖) (center x t) (delta k / 2) ≤
      profile k t + 14 := by
  have hR : 0 < delta k / 2 := by have h := delta_pos k; positivity
  apply Real.circleAverage_mono_on_of_le_circle
  · have hm : MeromorphicOn riemannZeta (sphere (center x t) (delta k / 2)) :=
      ((analyticOnNhd_disc k hk ht hx hx').mono sphere_subset_closedBall).meromorphicOn
    exact MeromorphicOn.circleIntegrable_log_norm_of_nonneg hm hR.le
  · intro s hs
    rw [abs_of_pos hR] at hs
    exact (le_max_right (0 : ℝ) (Real.log ‖riemannZeta s‖)).trans
      (disc_posLog_bound k hk ht hx hx' (sphere_subset_closedBall hs))

/-- The entire distance-weighted zero divisor is independently bounded
by the explicit line and Euler allowances. -/
theorem weighted_mass_bound (k : ℕ) (hk : 1 ≤ k) {t x : ℝ}
    (ht : 2 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta k / 4) :
    weightedMass k x t ≤ allowance k x t := by
  have hj := jensen_identity k hk ht hx hx'
  have hb := circle_average_bound k hk ht hx hx'
  have hc := center_log_bound t hx
  unfold allowance
  linarith

/-- Every actual zero contribution to the local Jensen mass is
nonnegative; the nonzero center and the full domain are checked. -/
theorem divisor_term_nonneg (k : ℕ) (hk : 1 ≤ k) {t x : ℝ}
    (ht : 2 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta k / 4) (u : ℂ) :
    0 ≤ (divisor riemannZeta (closedBall (center x t) (delta k / 2)) u : ℝ) *
      Real.log ((delta k / 2) * ‖center x t - u‖⁻¹) := by
  let d := divisor riemannZeta (closedBall (center x t) (delta k / 2))
  have han := analyticOnNhd_disc k hk ht hx hx'
  have hc : center x t ∈ closedBall (center x t) (delta k / 2) :=
    mem_closedBall_self (div_nonneg (delta_pos k).le (by norm_num))
  by_cases hu : d u = 0
  · change 0 ≤ (d u : ℝ) * _
    simp [hu]
  · have hmem := d.supportWithinDomain hu
    have hune : center x t ≠ u := by
      intro he
      apply hu
      rw [← he]
      dsimp [d]
      rw [han.divisor_apply hc,
        (han _ hc).analyticOrderAt_eq_zero.mpr
          (center_ne_zero t hx)]
      rfl
    have hd : 0 < ‖center x t - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hune)
    have hdist : ‖center x t - u‖ ≤ delta k / 2 := by
      simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using hmem
    apply mul_nonneg
    · exact_mod_cast han.divisor_nonneg u
    · apply Real.log_nonneg
      rw [← div_eq_mul_inv]
      exact (one_le_div hd).mpr hdist

/-- Each selected divisor term retains its full logarithmic distance
weight under the independently proved total allowance. -/
theorem divisor_term_bound (k : ℕ) (hk : 1 ≤ k) {t x : ℝ}
    (ht : 2 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta k / 4) (u : ℂ) :
    (divisor riemannZeta (closedBall (center x t) (delta k / 2)) u : ℝ) *
      Real.log ((delta k / 2) * ‖center x t - u‖⁻¹) ≤ allowance k x t := by
  apply le_trans _ (weighted_mass_bound k hk ht hx hx')
  apply single_le_finsum u _ (divisor_term_nonneg k hk ht hx hx')
  apply ((divisor riemannZeta (closedBall (center x t) (delta k / 2))).finiteSupport
    (isCompact_closedBall ..)).subset
  intro i hi hdi
  exact hi (by simp [hdi])

/-- A selected genuine zeta zero contributes its actual analytic
multiplicity, without a simple-zero assumption or a discarded distance. -/
theorem zero_source_bound (k : ℕ) (hk : 1 ≤ k) {t x : ℝ}
    (ht : 2 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta k / 4) (ρ : NontrivialZetaZero)
    (hρ : ρ.1 ∈ closedBall (center x t) (delta k / 2)) :
    (analyticZetaZeroMultiplicity ρ : ℝ) *
      Real.log ((delta k / 2) * ‖center x t - ρ.1‖⁻¹) ≤ allowance k x t := by
  have he : divisor riemannZeta (closedBall (center x t) (delta k / 2)) ρ.1 =
      (analyticZetaZeroMultiplicity ρ : ℤ) := by
    rw [(analyticOnNhd_disc k hk ht hx hx').divisor_apply hρ,
      ← Nat.cast_analyticOrderNatAt (analyticOrderAt_riemannZeta_nontrivialZero_ne_top ρ)]
    simp [analyticZetaZeroMultiplicity]
  have h := divisor_term_bound k hk ht hx hx' ρ.1
  simpa only [he, Int.cast_natCast] using h

/-- Every smaller closed disc has an explicit full multiplicity bound,
retaining its actual radius ratio. -/
theorem count_bound (k : ℕ) (hk : 1 ≤ k) {t x r : ℝ}
    (ht : 2 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta k / 4)
    (hr : 0 < r) (hr' : r < delta k / 2) :
    ((∑ᶠ u, divisor riemannZeta (closedBall (center x t) r) u : ℤ) : ℝ) ≤
      allowance k x t / Real.log ((delta k / 2) / r) := by
  have hR : 0 < delta k / 2 := by have h := delta_pos k; positivity
  have han := analyticOnNhd_disc k hk ht hx hx'
  have hj := AnalyticOnNhd.sum_divisor_le (f := riemannZeta) (c := center x t)
    (r := r) (R := delta k / 2) (M := Real.exp (profile k t + 14))
    (by rwa [abs_of_pos hr]) (by rwa [abs_of_pos hr, abs_of_pos hR])
    (Real.one_le_exp_iff.mpr (by linarith [profile_nonneg k t]))
    (by simpa only [abs_of_pos hR] using han) (center_ne_zero t hx) (by
      intro s hs
      have hs' : s ∈ closedBall (center x t) (delta k / 2) :=
        sphere_subset_closedBall (by simpa only [abs_of_pos hR] using hs)
      obtain ⟨hlo, hhi, him⟩ := disc_geometry k hk t hx hx' hs'
      exact local_norm_bound k hk ht hlo hhi him)
  rw [abs_of_pos hr] at hj
  apply hj.trans
  apply div_le_div_of_nonneg_right _
    (Real.log_pos ((one_lt_div hr).mpr hr')).le
  rw [Real.log_div (Real.exp_pos _).ne' (norm_pos_iff.mpr (center_ne_zero t hx)).ne',
    Real.log_exp]
  unfold allowance
  linarith [center_log_bound t hx]

end
end RiemannGaussian.ZetaNearOneJensen
