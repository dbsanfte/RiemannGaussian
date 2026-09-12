/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianStripBound
import RiemannGaussian.ZetaStripPhaseFamily

/-!
# Convergence and frequency costs of the complete Gaussian strip allowance

The full smoothed pole, rational correction and complex completion difference
are summable for every summable nonnegative coefficient family. The actual
shifted xi mass is summable under the existing logarithmic frequency moment;
no first-frequency moment or finite support is imposed. Its exact complete
divisor response remains available before the elementary frequency estimate.
-/

namespace RiemannGaussian.ZetaGaussianPhaseAllowance
noncomputable section
open Complex
open ZetaAngularPhaseAllowance
open GaussianComplexHalfMoments

/-- The whole complex Gaussian transform has a uniform zero-damping majorant
on the closed right half-plane. -/
theorem norm_transform_le {B : ℝ} (hB : 0 < B) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖transform B z‖ ≤ GaussianFermiLaplaceOrder.halfGaussian B 0 := by
  have h := GaussianLaplacePoleRemainder.norm_moment_le_zero hB 0 hz
  change ‖transform B z‖ ≤ (transform B 0).re at h
  rw [← Complex.ofReal_zero, transform_real, Complex.ofReal_re] at h
  exact h

/-- Every original complex smoothed-pole channel is summable on the same
Gaussian scale, including when the center shift is zero. -/
theorem summable_transform {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    {B x : ℝ} (hB : 0 < B) (hx : 0 ≤ x) (t : ℝ) :
    Summable (fun n => (a n : ℂ) * transform B ((x : ℂ) + I * (ω n * t))) := by
  apply (hs.mul_right (GaussianFermiLaplaceOrder.halfGaussian B 0)).of_norm_bounded
  intro n
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha n)]
  exact mul_le_mul_of_nonneg_left (norm_transform_le hB (by simpa using hx)) (ha n)

/-- The exact complex pole has a uniform bound on each positive vertical line. -/
theorem norm_pole_le {x : ℝ} (hx : 0 < x) (t : ℝ) :
    ‖(1 / ((x : ℂ) + I * t) : ℂ)‖ ≤ 1 / x := by
  have hn : x ≤ ‖(x : ℂ) + I * t‖ := by simpa using Complex.re_le_norm ((x : ℂ) + I * t)
  rw [norm_div, norm_one]
  exact one_div_le_one_div_of_le hx hn

/-- The full complex rational channels are summable without any frequency restriction. -/
theorem summable_pole {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    {x : ℝ} (hx : 0 < x) (t : ℝ) :
    Summable (fun n => (a n : ℂ) * (1 / ((x : ℂ) + I * (ω n * t)))) := by
  apply (hs.mul_right (1 / x)).of_norm_bounded
  intro n
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha n)]
  simpa only [Complex.ofReal_mul] using
    mul_le_mul_of_nonneg_left (norm_pole_le hx (ω n * t)) (ha n)

/-- The complete complex Archimedean differences remain summable before projection. -/
theorem summable_completion {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    {B σ : ℝ} (hB : 0 < B) (hσ : 0 < σ) (t : ℝ) :
    Summable (fun n => (a n : ℂ) *
      (ZetaGaussianCompletionAverage.response B ((σ : ℂ) + I * (ω n * t)) -
        zetaGlobalRegularCorrection ((σ : ℂ) + I * (ω n * t)))) := by
  apply (hs.mul_right (4 * B / GaussianPolynomialTransport.mass B)).of_norm_bounded
  intro n
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha n)]
  exact mul_le_mul_of_nonneg_left
    (ZetaGaussianCompletionAverage.norm_response_sub_center_le hB
      (s := (σ : ℂ) + I * (ω n * t)) (by simpa using hσ)) (ha n)

/-- A real-axis Euler value and half a logarithm bound the actual xi mass. -/
def xiAllowance (σ t : ℝ) : ℝ :=
  1 / (σ - 1) + (-logDeriv riemannZeta (σ : ℂ)).re + Real.log (σ + |t|) / 2

/-- The complete xi response on the closed Euler half-plane is nonnegative,
by its actual full multiplicity-weighted Poisson sum. -/
theorem xi_nonneg {s : ℂ} (hs : 1 ≤ s.re) : 0 ≤ (logDeriv riemannXi s).re := by
  rw [← tsum_zetaGlobalPoissonSummand hs]
  exact tsum_nonneg (zetaGlobalPoissonSummand_nonneg hs)

/-- The actual shifted xi response has a height-logarithmic majorant at
every Euler abscissa, with no small-shift condition. -/
theorem xi_le_allowance {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    (logDeriv riemannXi ((σ : ℂ) + I * t)).re ≤ xiAllowance σ t := by
  have he := congrArg Complex.re (zeta_global_complex_budget
    (s := (σ : ℂ) + I * t) (by simpa using hσ))
  have hr := re_zetaGlobalRegularCorrection_le_half_log hσ.le t
  have hd := norm_neg_logDeriv_riemannZeta_re_le_real_axis hσ t
  rw [Real.norm_eq_abs] at hd
  have hp : (1 / ((σ : ℂ) + I * t - 1) : ℂ).re ≤ 1 / (σ - 1) := by
    have hc : (σ : ℂ) + I * t - 1 = ((σ - 1 : ℝ) : ℂ) + I * t := by push_cast; ring
    rw [hc]
    exact (Complex.re_le_norm _).trans (norm_pole_le (by linarith : 0 < σ - 1) t)
  simp only [Complex.add_re] at he
  unfold xiAllowance
  linarith [neg_le_abs (-logDeriv riemannZeta ((σ : ℂ) + I * t)).re]

/-- Increasing a nonconstant phase frequency costs only half its logarithm
in the complete xi allowance. -/
theorem xiAllowance_mul_le {σ ω : ℝ} (hσ : 0 < σ) (hω : 1 ≤ ω) (t : ℝ) :
    xiAllowance σ (ω * t) ≤ xiAllowance σ t + Real.log ω / 2 := by
  have hw : 0 < ω := by linarith
  have hh : σ + |ω * t| ≤ ω * (σ + |t|) := by
    rw [abs_mul, abs_of_pos hw]
    nlinarith
  have h := Real.log_le_log (by positivity : 0 < σ + |ω * t|) hh
  rw [Real.log_mul hw.ne' (by positivity : σ + |t| ≠ 0)] at h
  unfold xiAllowance
  linarith

/-- The actual complete xi mass is summable under precisely the existing
nonconstant logarithmic frequency moment. -/
theorem summable_xi {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n => tail a n * Real.log (ω n)))
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    Summable (fun n => tail a n * (logDeriv riemannXi ((σ : ℂ) + I * (ω n * t))).re) := by
  apply (((tail_summable ha hs).mul_right (xiAllowance σ t)).add (hlog.div_const 2)).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (tail_nonneg ha n)
    (xi_nonneg (by simpa using hσ.le)))]
  by_cases hn : n = 0
  · simp [tail, hn]
  · have h := mul_le_mul_of_nonneg_left
      ((xi_le_allowance hσ (ω n * t)).trans
        (xiAllowance_mul_le (by linarith : 0 < σ) (hω n hn) t)) (tail_nonneg ha n)
    simp only [Complex.ofReal_mul] at h
    nlinarith only [h]

/-- The exact full shifted-xi family retains its original response before
the common half-logarithmic frequency estimate is applied. -/
theorem tsum_xi_le {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n => tail a n * Real.log (ω n)))
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    (∑' n, tail a n * (logDeriv riemannXi ((σ : ℂ) + I * (ω n * t))).re) ≤
      mass a * xiAllowance σ t + frequencyCost a ω / 2 := by
  have h := (summable_xi ha hs hω hlog hσ t).tsum_le_tsum
    (fun n => show tail a n * (logDeriv riemannXi ((σ : ℂ) + I * (ω n * t))).re ≤
      tail a n * xiAllowance σ t + (tail a n * Real.log (ω n)) / 2 from by
      by_cases hn : n = 0
      · simp [tail, hn]
      · have h := mul_le_mul_of_nonneg_left
          ((xi_le_allowance hσ (ω n * t)).trans
            (xiAllowance_mul_le (by linarith : 0 < σ) (hω n hn) t)) (tail_nonneg ha n)
        simp only [Complex.ofReal_mul] at h
        nlinarith only [h])
    (((tail_summable ha hs).mul_right (xiAllowance σ t)).add (hlog.div_const 2))
  simpa only [Summable.tsum_add ((tail_summable ha hs).mul_right (xiAllowance σ t))
    (hlog.div_const 2), tsum_mul_right, tsum_div_const, mass, frequencyCost] using h

/-- The original right-line pole and signed completion response, before
their arithmetic and zero contributions are separated. -/
def rightResponse (σ t : ℝ) : ℝ :=
  (1 / ((σ : ℂ) + I * t - 1) + zetaGlobalRegularCorrection ((σ : ℂ) + I * t)).re

/-- The actual Euler prime work and full xi response recover the same
complex right-line pole and completion after real projection. -/
theorem rightResponse_eq {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    rightResponse σ t = (-logDeriv riemannZeta ((σ : ℂ) + I * t)).re +
      (logDeriv riemannXi ((σ : ℂ) + I * t)).re := by
  simpa only [rightResponse, Complex.add_re] using
    (congrArg Complex.re (zeta_global_complex_budget
      (s := (σ : ℂ) + I * t) (by simpa using hσ))).symm

/-- The original signed right-line response is summable because both its
actual arithmetic and complete zero channels are genuinely summable. -/
theorem summable_rightResponse {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n => tail a n * Real.log (ω n)))
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    Summable (fun n => tail a n * rightResponse σ (ω n * t)) := by
  have hd := summable_zetaPhase_logDeriv (ω := ω) (tail_nonneg ha) (tail_summable ha hs) hσ t
  have hx := summable_xi ha hs hω hlog hσ t
  simpa only [rightResponse_eq hσ, mul_add, Complex.ofReal_mul] using hd.add hx

/-- The entire nonconstant xi family keeps the full right-line prime work
on the left. Only the constant channel's Euler value remains on the right. -/
theorem tsum_xi_add_arithmetic_eq {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hω0 : ω 0 = 0) (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n => tail a n * Real.log (ω n)))
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    (∑' n, tail a n * (logDeriv riemannXi ((σ : ℂ) + I * (ω n * t))).re) +
      (∑' m, zetaPhasePrimeWeight σ m * zetaPhaseKernel a ω (t * Real.log m)) =
      a 0 * (-logDeriv riemannZeta (σ : ℂ)).re +
        ∑' n, tail a n * rightResponse σ (ω n * t) := by
  have hd := summable_zetaPhase_logDeriv (ω := ω) ha hs hσ t
  have hdt := summable_zetaPhase_logDeriv (ω := ω) (tail_nonneg ha) (tail_summable ha hs) hσ t
  have hx := summable_xi ha hs hω hlog hσ t
  rw [(hasSum_zetaPhase_arithmetic (ω := ω) ha hs hσ t).tsum_eq,
    hd.tsum_eq_add_tsum_ite 0, hω0, zero_mul]
  simp only [Complex.ofReal_zero, mul_zero, add_zero]
  have he : (∑' n, tail a n * rightResponse σ (ω n * t)) =
      (∑' n, tail a n * (-logDeriv riemannZeta ((σ : ℂ) + I * ((ω n * t : ℝ) : ℂ))).re) +
        ∑' n, tail a n * (logDeriv riemannXi ((σ : ℂ) + I * (ω n * t))).re := by
    simpa only [rightResponse_eq hσ, mul_add, Complex.ofReal_mul] using hdt.tsum_add hx
  rw [he]
  simp only [tail, ite_mul, zero_mul]
  ring

/-- At every nonconstant working height, the right-line pole decays
quadratically and the complete signed completion costs half a logarithm. -/
theorem rightResponse_mul_le {σ ω t : ℝ} (hσ : 1 < σ) (hω : 1 ≤ ω) (ht : t ≠ 0) :
    rightResponse σ (ω * t) ≤
      (σ - 1) / t ^ 2 + Real.log (σ + |t|) / 2 + Real.log ω / 2 := by
  have hw : 0 < ω := by linarith
  have hp : (1 / ((σ : ℂ) + I * (ω * t) - 1) : ℂ).re ≤ (σ - 1) / t ^ 2 := by
    have he : (σ : ℂ) + I * (ω * t) - 1 = ((σ - 1 : ℝ) : ℂ) + I * ((ω * t : ℝ) : ℂ) := by
      push_cast
      ring
    rw [he, zetaPole_real_part]
    apply div_le_div_of_nonneg_left (by linarith : 0 ≤ σ - 1) (sq_pos_of_ne_zero ht)
    nlinarith [sq_nonneg (σ - 1), mul_self_le_mul_self (show 0 ≤ (1 : ℝ) by norm_num) hω,
      sq_nonneg t, mul_nonneg (show 0 ≤ ω ^ 2 - 1 by nlinarith) (sq_nonneg t)]
  have hr := re_zetaGlobalRegularCorrection_le_half_log hσ.le (ω * t)
  have hl := xiAllowance_mul_le (by linarith : 0 < σ) hω t
  unfold xiAllowance at hl
  simp only [rightResponse, Complex.add_re, Complex.ofReal_mul] at hp hr ⊢
  linarith

/-- Coupling the full Euler prime kernel improves the shifted-xi allowance:
the real-axis Euler cost is paid only by the constant coefficient. The
nonnegative arithmetic work is still retained explicitly on the left. -/
theorem tsum_xi_add_arithmetic_le {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hω0 : ω 0 = 0) (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n => tail a n * Real.log (ω n)))
    {σ t : ℝ} (hσ : 1 < σ) (ht : t ≠ 0) :
    (∑' n, tail a n * (logDeriv riemannXi ((σ : ℂ) + I * (ω n * t))).re) +
      (∑' m, zetaPhasePrimeWeight σ m * zetaPhaseKernel a ω (t * Real.log m)) ≤
      a 0 * (-logDeriv riemannZeta (σ : ℂ)).re +
        mass a * ((σ - 1) / t ^ 2 + Real.log (σ + |t|) / 2) + frequencyCost a ω / 2 := by
  rw [tsum_xi_add_arithmetic_eq ha hs hω0 hω hlog hσ t]
  have hb := (tail_summable ha hs).mul_right ((σ - 1) / t ^ 2 + Real.log (σ + |t|) / 2)
  have h := (summable_rightResponse ha hs hω hlog hσ t).tsum_le_tsum
    (fun n => show tail a n * rightResponse σ (ω n * t) ≤
      tail a n * ((σ - 1) / t ^ 2 + Real.log (σ + |t|) / 2) +
        (tail a n * Real.log (ω n)) / 2 from by
      by_cases hn : n = 0
      · simp [tail, hn]
      · have h := mul_le_mul_of_nonneg_left (rightResponse_mul_le hσ (hω n hn) ht) (tail_nonneg ha n)
        nlinarith only [h]) (hb.add (hlog.div_const 2))
  rw [hb.tsum_add (hlog.div_const 2), tsum_mul_right, tsum_div_const] at h
  unfold mass frequencyCost
  linarith

end
end RiemannGaussian.ZetaGaussianPhaseAllowance
