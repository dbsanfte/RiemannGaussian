/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeFermiMomentComparison

/-!
# Exact spectral transport of the full ordinary-prime moment

The Gaussian Fermi probability density acts on the entire complex moment,
with its polynomial, factorial orders and prime exclusions unchanged.
Absolute convergence in the Euler half-plane pays the infinite
sum-integral interchange. The result is the Gaussian Fermi multiplier at
the explicitly shifted abscissa, including its factor of two.

For the actual margin parameter, the input line is `1 + m_F(H)` and the
output line is the original `3/2`. Positivity of the averaging density
does not assert positivity of the complex prime moment being averaged.
-/

namespace RiemannGaussian.SquarefreeEulerQuadratic
noncomputable section
open Complex Filter MeasureTheory Topology
open scoped Classical
open EtaGammaSmoothing GaussianFermiSpectralWeight GaussianFermiDerivativeBounds
open GaussianFermiZeroPair

/-- The original Fermi-weighted ordinary-prime moment with a Gaussian
regulator. The complex polynomial and original prime support are retained. -/
def gaussianFermiPrimeLogResponse (a B : ℝ) (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ)
    (N : ℕ) (s : ℂ) : ℂ :=
  ∑' n, primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N s n *
    ((window B (Real.log n) * fermi (-a * Real.log n) : ℝ) : ℂ)

/-- A vertical shift rotates the full kernel without changing any
factorial coefficient or the original polynomial. -/
theorem primeFilterKernel_imaginary_shift (p : Polynomial ℂ) (N : ℕ) (s : ℂ)
    (y x : ℝ) :
    zetaPrimeFilterKernel p N (s - I * y) x =
      zetaPrimeFilterKernel p N s x * Complex.exp (I * (y : ℂ) * (Real.log x : ℂ)) := by
  rw [sub_eq_add_neg, zetaPrimeFilterKernel_add_parameter]
  congr 2
  ring

/-- The entire complex kernel has exactly the same norm on a vertical
line; no coefficientwise estimate is needed for this identity. -/
theorem norm_primeFilterKernel_imaginary_shift (p : Polynomial ℂ) (N : ℕ) (s : ℂ)
    (y x : ℝ) :
    ‖zetaPrimeFilterKernel p N (s - I * y) x‖ = ‖zetaPrimeFilterKernel p N s x‖ := by
  rw [primeFilterKernel_imaginary_shift, norm_mul, Complex.norm_exp]
  simp

/-- Each literal complex prime term is integrable against the actual
spectral density. Its norm is bounded by the density times a fixed norm. -/
theorem integrable_density_primeLogTerm {a B : ℝ} (ha : 0 ≤ a) (hB : 0 < B)
    (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ) (N : ℕ) (s : ℂ) (n : ℕ) :
    Integrable (fun y : ℝ => (density a B y : ℂ) *
      (primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N (s - I * y) n)) := by
  have hm : AEStronglyMeasurable (fun y : ℝ => (density a B y : ℂ) *
      (primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N (s - I * y) n)) := by
    apply Continuous.aestronglyMeasurable
    simp_rw [primeFilterKernel_imaginary_shift]
    have hd := continuous_density hB a
    fun_prop
  apply (((integrable_density ha hB).norm).mul_const
    ‖primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N s n‖).mono' hm
  filter_upwards with y
  simp only [norm_mul, Complex.norm_real, norm_primeFilterKernel_imaginary_shift]
  exact le_rfl

/-- The integrated norm of each term is its original full complex norm,
because the positive spectral density has exactly unit mass. -/
theorem integral_norm_density_primeLogTerm {a B : ℝ} (ha : 0 < a) (hB : 0 < B)
    (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ) (N : ℕ) (s : ℂ) (n : ℕ) :
    (∫ y : ℝ, ‖(density a B y : ℂ) *
      (primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N (s - I * y) n)‖) =
      ‖primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N s n‖ := by
  calc
    _ = ∫ y : ℝ, density a B y *
        ‖primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N s n‖ := by
      apply integral_congr_ae
      filter_upwards with y
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (density_nonneg ha hB y)]
      simp only [norm_mul, norm_primeFilterKernel_imaginary_shift]
    _ = _ := by rw [integral_mul_const, integral_density ha.le hB, one_mul]

/-- The complete family of integral norms is summable on the Euler
half-plane, with the original cutoff and ordinary-prime sieve unchanged. -/
theorem summable_integral_norm_density_primeLogTerm {a B : ℝ} (ha : 0 < a) (hB : 0 < B)
    (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime)
    (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => ∫ y : ℝ, ‖(density a B y : ℂ) *
      (primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N (s - I * y) n)‖) := by
  simp_rw [integral_norm_density_primeLogTerm ha hB]
  exact (summable_primeLogResponse p D S hS N hs).norm

/-- The full original complex moment is integrable against the spectral
density. The counting-measure argument records absolute integrability
before the infinite prime series is interchanged with the integral. -/
theorem integrable_density_primeLogResponse {a B : ℝ} (ha : 0 < a) (hB : 0 < B)
    (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime)
    (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun y : ℝ => (density a B y : ℂ) *
      primeLogResponse p D S N (s - I * y)) := by
  have hd := continuous_density hB a
  have hmeas : Measurable (fun q : ℕ × ℝ => (density a B q.2 : ℂ) *
      (primeCorrectionCoefficient D S q.1 * zetaPrimeFilterKernel p N (s - I * q.2) q.1)) := by
    apply measurable_from_prod_countable_right
    intro n
    apply Continuous.measurable
    simp_rw [primeFilterKernel_imaginary_shift]
    fun_prop
  have hp : Integrable (fun q : ℕ × ℝ => (density a B q.2 : ℂ) *
      (primeCorrectionCoefficient D S q.1 * zetaPrimeFilterKernel p N (s - I * q.2) q.1))
      (Measure.count.prod volume) := by
    apply (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall (integrable_density_primeLogTerm ha.le hB p D S N s), ?_⟩
    apply integrable_count_iff.mpr
    simpa only [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)] using
      summable_integral_norm_density_primeLogTerm ha hB p D S hS N hs
  apply hp.integral_prod_right.congr
  filter_upwards [hp.prod_left_ae] with y hy
  simpa [primeLogResponse, tsum_mul_left] using integral_countable hy

/-- The centered signal separates into its Gaussian regulator, its
horizontal shift and its original Fermi multiplier, with exact signs. -/
theorem signal_eq_window_shift_fermi (a B x : ℝ) :
    signal a B x = window B x * Real.exp (-(a / 2) * x) * fermi (-a * x) := by
  unfold signal damped window
  rw [← Real.exp_add]
  congr 2
  ring

/-- The characteristic function evaluates the integral of each original
prime term exactly, including the half-parameter shift and factor two. -/
theorem integral_density_primeLogTerm {a B : ℝ} (ha : 0 ≤ a) (hB : 0 < B)
    (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ) (N : ℕ) (s : ℂ) (n : ℕ) :
    (∫ y : ℝ, (density a B y : ℂ) *
      (primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N (s - I * y) n)) =
      2 * (primeCorrectionCoefficient D S n *
        zetaPrimeFilterKernel p N (s + ((a / 2 : ℝ) : ℂ)) n *
          ((window B (Real.log n) * fermi (-a * Real.log n) : ℝ) : ℂ)) := by
  calc
    _ = (primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N s n) *
        ∫ y : ℝ, (density a B y : ℂ) *
          Complex.exp (I * (y : ℂ) * (Real.log n : ℂ)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      rw [primeFilterKernel_imaginary_shift]
      ring
    _ = _ := by
      rw [integral_density_mul_cexp ha hB, signal_eq_window_shift_fermi,
        zetaPrimeFilterKernel_add_parameter]
      push_cast
      ring

/-- Exact transport of the entire complex prime moment through the
Gaussian Fermi probability density. Every factorial order, polynomial
coefficient and ordinary-prime exclusion stays inside the same average. -/
theorem integral_density_primeLogResponse {a B : ℝ} (ha : 0 < a) (hB : 0 < B)
    (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime)
    (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    (∫ y : ℝ, (density a B y : ℂ) * primeLogResponse p D S N (s - I * y)) =
      2 * gaussianFermiPrimeLogResponse a B p D S N (s + ((a / 2 : ℝ) : ℂ)) := by
  have h := (hasSum_integral_of_summable_integral_norm
    (integrable_density_primeLogTerm ha.le hB p D S N s)
    (summable_integral_norm_density_primeLogTerm ha hB p D S hS N hs)).tsum_eq
  simp_rw [integral_density_primeLogTerm ha.le hB] at h
  simpa only [gaussianFermiPrimeLogResponse, tsum_mul_left, primeLogResponse] using h.symm

/-- At the actual margin parameter, the input line is `1 + m_F(H)`
and the output is exactly the original `3/2` sampling line. Positivity
of the margin discharges convergence for every polynomial and sieve. -/
theorem integral_margin_density_primeLogResponse (H : ℝ) {B : ℝ} (hB : 0 < B)
    (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime)
    (N : ℕ) (t : ℝ) :
    (∫ y : ℝ, (density (1 - 2 * zetaFermiZeroMargin H) B y : ℂ) *
      primeLogResponse p D S N (1 + (zetaFermiZeroMargin H : ℂ) + I * t - I * y)) =
      2 * gaussianFermiPrimeLogResponse (1 - 2 * zetaFermiZeroMargin H) B p D S N
        (3 / 2 + I * t) := by
  have hm := zetaFermiZeroMargin_bounds H
  have h := integral_density_primeLogResponse (by linarith : 0 < 1 - 2 * zetaFermiZeroMargin H)
    hB p D S hS N (s := 1 + (zetaFermiZeroMargin H : ℂ) + I * t)
    (by simpa using (show (1 : ℝ) < 1 + zetaFermiZeroMargin H by linarith))
  convert h using 1
  congr 2
  push_cast
  ring

/-- A nonnegative Gaussian width contracts each complete Fermi-weighted
prime term. The original complex coefficient is kept inside its norm. -/
theorem norm_gaussianFermiPrimeLogTerm_le (a : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ) (N : ℕ) (s : ℂ) (n : ℕ) :
    ‖primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N s n *
      ((window B (Real.log n) * fermi (-a * Real.log n) : ℝ) : ℂ)‖ ≤
      ‖primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N s n *
        (fermi (-a * Real.log n) : ℂ)‖ := by
  have hw0 : 0 ≤ window B (Real.log n) := (Real.exp_pos _).le
  have hw1 : window B (Real.log n) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hB) (sq_nonneg _)
  have he : primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N s n *
      ((window B (Real.log n) * fermi (-a * Real.log n) : ℝ) : ℂ) =
      (primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N s n *
        (fermi (-a * Real.log n) : ℂ)) * (window B (Real.log n) : ℂ) := by
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0]
  exact mul_le_of_le_one_right (norm_nonneg _) hw1

/-- The regulated ordinary-prime series converges absolutely, including
zero Gaussian width, wherever the original Euler moment converges. -/
theorem summable_gaussianFermiPrimeLogResponse (a : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime)
    (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n => primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N s n *
      ((window B (Real.log n) * fermi (-a * Real.log n) : ℝ) : ℂ)) :=
  (summable_fermiPrimeLogResponse a p D S hS N hs).norm.of_norm_bounded
    (norm_gaussianFermiPrimeLogTerm_le a hB p D S N s)

/-- Removing the Gaussian regulator recovers the unchanged Fermi moment
for each fixed moment order. This does not interchange the zero-width
limit with the separate limit of growing moment orders. -/
theorem tendsto_gaussianFermiPrimeLogResponse (a : ℝ) (p : Polynomial ℂ)
    (D : ℕ) (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) (N : ℕ) {s : ℂ} (hs : 1 < s.re)
    {ι : Type*} {l : Filter ι} {B : ι → ℝ} (hB : ∀ᶠ j in l, 0 ≤ B j)
    (hlim : Tendsto B l (𝓝 0)) :
    Tendsto (fun j => gaussianFermiPrimeLogResponse a (B j) p D S N s) l
      (𝓝 (fermiPrimeLogResponse a p D S N s)) := by
  apply tendsto_tsum_of_dominated_convergence
    (summable_fermiPrimeLogResponse a p D S hS N hs).norm
  · intro n
    have hw : Tendsto (fun j => window (B j) (Real.log n)) l (𝓝 1) := by
      simpa only [window, neg_zero, zero_mul, Real.exp_zero, Function.comp_def] using
        (Real.continuous_exp.tendsto _).comp (hlim.neg.mul_const ((Real.log n) ^ 2))
    have hc := ((Complex.continuous_ofReal.tendsto 1).comp hw).mul_const
      (fermi (-a * Real.log n) : ℂ)
    simpa only [Complex.ofReal_one, one_mul, Complex.ofReal_mul, Function.comp_def] using
      hc.const_mul (primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N s n)
  · filter_upwards [hB] with j hj n
    exact norm_gaussianFermiPrimeLogTerm_le a hj p D S N s n

/-- The full positive-density averages recover twice the original Fermi
moment as their Gaussian width tends to zero. Convergence of both the
integral and the infinite prime series has been discharged. -/
theorem tendsto_integral_density_primeLogResponse {a : ℝ} (ha : 0 < a)
    (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime)
    (N : ℕ) {s : ℂ} (hs : 1 < s.re) {ι : Type*} {l : Filter ι} {B : ι → ℝ}
    (hB : ∀ᶠ j in l, 0 < B j) (hlim : Tendsto B l (𝓝 0)) :
    Tendsto (fun j => ∫ y : ℝ, (density a (B j) y : ℂ) *
      primeLogResponse p D S N (s - I * y)) l
      (𝓝 (2 * fermiPrimeLogResponse a p D S N (s + ((a / 2 : ℝ) : ℂ)))) := by
  have hs' : 1 < (s + ((a / 2 : ℝ) : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have h := (tendsto_gaussianFermiPrimeLogResponse a p D S hS N hs'
    (hB.mono fun _ hj => hj.le) hlim).const_mul (2 : ℂ)
  apply h.congr'
  filter_upwards [hB] with j hj
  exact (integral_density_primeLogResponse ha hj p D S hS N hs).symm

end
end RiemannGaussian.SquarefreeEulerQuadratic
