/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeCharacterRemainder

/-!
# Integrated control of the nonlinear prime-character multiplicative factor

The local-log remainder stays bounded and integrable after exponentiation
and subtraction of one, uniformly over finite prime cutoffs at every fixed
real part greater than one half. This controls a multiplicative correction;
the first-order factor and its coupling through the original factorial
filter still require an independent arithmetic estimate.
-/

namespace RiemannGaussian.ZetaPrimeNonlinearFactor
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
open ZetaPrimeCharacterRemainder ZetaSquarefreeSignedTail

/-- A bounded exponent gives a linear bound on its multiplicative error,
including exponents outside the unit ball. -/
theorem norm_exp_sub_one_le_linear {z : ℂ} {M : ℝ} (hz : ‖z‖ ≤ M) :
    ‖Complex.exp z - 1‖ ≤ (2 + Real.exp M) * ‖z‖ := by
  by_cases h : ‖z‖ ≤ 1
  · exact (Complex.norm_exp_sub_one_le h).trans
      (mul_le_mul_of_nonneg_right (by linarith [Real.exp_pos M] : (2 : ℝ) ≤ 2 + Real.exp M) (norm_nonneg z))
  · have he : ‖Complex.exp z‖ ≤ Real.exp M := by
      rw [Complex.norm_exp]
      exact Real.exp_le_exp.mpr ((Complex.re_le_norm z).trans hz)
    have hb := norm_sub_le (Complex.exp z) (1 : ℂ)
    rw [norm_one] at hb
    nlinarith [Real.exp_pos M]

/-- The whole finite local-log remainder is continuous in frequency.
The small-factor condition keeps each logarithm in its analytic domain. -/
theorem continuous_logRemainder {ι : Type*} (Q : Finset ι) (q : ι → ℂ)
    (ell : ι → ℝ) (hq : ∀ p ∈ Q, ‖q p‖ ≤ 1 / 4) :
    Continuous (logRemainder Q q ell) := by
  unfold logRemainder
  apply continuous_finsetSum
  intro p hp
  apply Continuous.sub
  · apply Continuous.clog (by fun_prop)
    intro xi
    exact local_character_mem_slitPlane (q p) (hq p hp) (ell p) xi
  · fun_prop

/-- The multiplicative nonlinear factor has a genuine integrable
frequency quotient whenever the already-controlled log remainder is bounded. -/
theorem integrable_exp_logRemainder_sub_one_div {ι : Type*} (Q : Finset ι)
    (q : ι → ℂ) (ell : ι → ℝ) (hq : ∀ p ∈ Q, ‖q p‖ ≤ 1 / 4)
    {M : ℝ} (hM : ∀ xi, ‖logRemainder Q q ell xi‖ ≤ M) :
    IntegrableOn (fun xi : ℝ =>
      (Complex.exp (logRemainder Q q ell xi) - 1) / (xi : ℂ) ^ 2) (Ioi 0) := by
  apply ((integrable_logRemainder_div Q q ell hq).norm.const_mul (2 + Real.exp M)).mono'
  · have hc : ContinuousOn (fun xi : ℝ =>
        (Complex.exp (logRemainder Q q ell xi) - 1) / (xi : ℂ) ^ 2) (Ioi 0) := by
      apply ((Complex.continuous_exp.comp (continuous_logRemainder Q q ell hq)).sub
        continuous_const).continuousOn.div (by fun_prop)
      intro xi hxi
      exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt hxi))
    exact hc.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [] with xi
    rw [norm_div, norm_div]
    have h := div_le_div_of_nonneg_right (norm_exp_sub_one_le_linear (hM xi)) (norm_nonneg ((xi : ℂ) ^ 2))
    simpa only [mul_div_assoc] using h

/-- Exponentiating the controlled log remainder keeps a finite integrated
cost. The first-order prime exponential is a separate retained factor. -/
theorem integral_norm_exp_logRemainder_sub_one_div_le {ι : Type*} (Q : Finset ι)
    (q : ι → ℂ) (ell : ι → ℝ) (hq : ∀ p ∈ Q, ‖q p‖ ≤ 1 / 4)
    {M : ℝ} (hM : ∀ xi, ‖logRemainder Q q ell xi‖ ≤ M) :
    (∫ xi : ℝ in Ioi 0,
      ‖(Complex.exp (logRemainder Q q ell xi) - 1) / (xi : ℂ) ^ 2‖) ≤
      (2 + Real.exp M) * (Real.pi * ∑ p ∈ Q, ‖q p‖ ^ 2 * |ell p|) := by
  calc
    _ ≤ ∫ xi : ℝ in Ioi 0, (2 + Real.exp M) *
        ‖logRemainder Q q ell xi / (xi : ℂ) ^ 2‖ := by
      apply integral_mono_ae (integrable_exp_logRemainder_sub_one_div Q q ell hq hM).norm
        ((integrable_logRemainder_div Q q ell hq).norm.const_mul _)
      filter_upwards [] with xi
      rw [norm_div, norm_div]
      have h := div_le_div_of_nonneg_right (norm_exp_sub_one_le_linear (hM xi)) (norm_nonneg ((xi : ℂ) ^ 2))
      simpa only [mul_div_assoc] using h
    _ = (2 + Real.exp M) * ∫ xi : ℝ in Ioi 0,
        ‖logRemainder Q q ell xi / (xi : ℂ) ^ 2‖ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_norm_logRemainder_div_le Q q ell hq) (by positivity)

/-- The actual nonlinear multiplicative factor, after subtraction of one,
has an integrated cost independent of the finite prime cutoff. No
first-order prime-phase or factorial-filter bound is assumed or concluded. -/
theorem integral_norm_actual_nonlinearFactor_sub_one_div_le (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, 16 ≤ p) {s : ℂ} (hs : 1 / 2 < s.re) :
    (∫ xi : ℝ in Ioi 0,
      ‖(Complex.exp (logRemainder Q (zetaPrimeFeature s) (fun p => Real.log p) xi) - 1) /
        (xi : ℂ) ^ 2‖) ≤
      (2 + Real.exp (4 * ∑' n, zetaPrimeExpWeight (2 * s.re) n)) *
        (Real.pi * (s.re - 1 / 2)⁻¹ * ∑' n, zetaPrimeExpWeight (s.re + 1 / 2) n) := by
  have hM (xi : ℝ) : ‖logRemainder Q (zetaPrimeFeature s) (fun p => Real.log p) xi‖ ≤
      4 * ∑' n, zetaPrimeExpWeight (2 * s.re) n := by
    rw [logRemainder, Finset.sum_sub_distrib]
    exact norm_sum_actual_prime_character_error_le Q
      (fun p => Complex.exp (((Real.log p * xi : ℝ) : ℂ) * Complex.I)) hQ
      (fun p _hp => (Complex.norm_exp_ofReal_mul_I _).le) hs
  have h := integral_norm_exp_logRemainder_sub_one_div_le Q (zetaPrimeFeature s)
    (fun p => Real.log p) (fun p hp => norm_primeFeature_le_quarter hs.le (hQ p hp)) hM
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hb := mul_le_mul_of_nonneg_left (actual_prime_square_log_sum_le Q hs) Real.pi_pos.le
  simpa only [mul_assoc] using hb

end
end RiemannGaussian.ZetaPrimeNonlinearFactor
