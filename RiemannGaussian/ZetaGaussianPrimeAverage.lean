/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianVerticalAverage
import RiemannGaussian.GaussianFermiPrimeComparison

/-!
# Gaussian vertical averaging of the actual complex Euler series

The original von Mangoldt Dirichlet terms retain their complete phase.
Their normalized Gaussian average is exactly the ordinary Gaussian prime
series, with genuine absolute convergence and the infinite sum-integral
exchange proved before projection to the existing real arithmetic sum.
The Euler identity is stated only on its genuine half-plane of convergence.
-/

namespace RiemannGaussian.ZetaGaussianPrimeAverage
noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology
open GaussianVerticalAverage
open GaussianFermiZeroPair (window)

/-- The literal von Mangoldt Dirichlet summand, before smoothing. -/
def base (σ t : ℝ) (n : ℕ) : ℂ :=
  LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + I * t) n

/-- The original complex prime-power term with its physical Gaussian damping. -/
def term (σ B t : ℝ) (n : ℕ) : ℂ := base σ t n * (window B (Real.log n) : ℂ)

/-- The complete complex Gaussian prime series, retaining its imaginary part. -/
def primeSum (σ B t : ℝ) : ℂ := ∑' n : ℕ, term σ B t n

/-- The literal unsmoothed summand retains the full complex logarithmic phase. -/
theorem base_eq_phase (σ t : ℝ) (n : ℕ) :
    base σ t n = (zetaPhasePrimeWeight σ n : ℂ) *
      Complex.exp (-(I * ((t * Real.log n : ℝ) : ℂ))) :=
  vonMangoldt_LSeries_term_eq_phase σ t n

/-- A vertical displacement changes only the original prime phase. -/
theorem base_shift (σ t y : ℝ) (n : ℕ) :
    base σ (t - y) n = base σ t n * Complex.exp (I * (y : ℂ) * (Real.log n : ℂ)) := by
  rw [base_eq_phase, base_eq_phase]
  have he : -(I * (((t - y) * Real.log n : ℝ) : ℂ)) =
      -(I * ((t * Real.log n : ℝ) : ℂ)) + I * (y : ℂ) * (Real.log n : ℂ) := by
    push_cast
    ring
  simp only [he, Complex.exp_add, mul_assoc]

/-- The norm of each actual Euler term is exactly its positive real amplitude. -/
theorem norm_base (σ t : ℝ) (n : ℕ) : ‖base σ t n‖ = zetaPhasePrimeWeight σ n := by
  rw [base_eq_phase]
  simp only [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (zetaPhasePrimeWeight_nonneg σ n), Complex.neg_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, neg_zero, Real.exp_zero, mul_one]

/-- The entire complex Gaussian term has its original positive amplitude as norm. -/
theorem norm_term (σ B t : ℝ) (n : ℕ) :
    ‖term σ B t n‖ = zetaPhasePrimeWeight σ n * window B (Real.log n) := by
  rw [term, norm_mul, norm_base, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (show 0 < window B (Real.log n) from Real.exp_pos _)]

/-- The real projection is exactly the previously defined ordinary Gaussian sum's atom. -/
theorem term_re (σ B t : ℝ) (n : ℕ) :
    (term σ B t n).re = GaussianFermiPrimeComparison.ordinarySummand σ B t n := by
  rw [term, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [base, vonMangoldt_LSeries_term_re]
  unfold GaussianFermiPrimeComparison.ordinarySummand zetaPhasePrimeWeight
  ring

/-- The full complex Gaussian series is absolutely convergent throughout
every closed half-plane above two thirds, including the line Re(s)=1. -/
theorem summable_term {σ₀ σ B : ℝ} (hσ₀ : 2 / 3 < σ₀) (hσ : σ₀ ≤ σ)
    (hB : 0 < B) (t : ℝ) : Summable (term σ B t) := by
  apply (GaussianFermiPrimeComparison.summable_ordinarySummand hσ₀ hσ hB 0).of_norm_bounded
  intro n
  simp only [norm_term, GaussianFermiPrimeComparison.ordinarySummand,
    zero_mul, Real.cos_zero, mul_one, le_refl]

/-- Genuine complex convergence justifies projection to the full existing real prime sum. -/
theorem primeSum_re {σ₀ σ B : ℝ} (hσ₀ : 2 / 3 < σ₀) (hσ : σ₀ ≤ σ)
    (hB : 0 < B) (t : ℝ) :
    (primeSum σ B t).re = GaussianFermiPrimeComparison.ordinarySum σ B t := by
  rw [primeSum, Complex.re_tsum (summable_term hσ₀ hσ hB t)]
  simp only [term_re, GaussianFermiPrimeComparison.ordinarySum]

/-- Every actual prime term is integrable against the normalized vertical density. -/
theorem integrable_base {B : ℝ} (hB : 0 < B) (σ t : ℝ) (n : ℕ) :
    Integrable (fun y : ℝ => (density B y : ℂ) * base σ (t - y) n) := by
  have h := (integrable_phase hB (Real.log n)).const_mul (base σ t n)
  simp only [base_shift]
  convert! h using 1
  funext y
  ring

/-- Each original complex Dirichlet term acquires exactly Gaussian logarithmic damping. -/
theorem average_base {B : ℝ} (hB : 0 < B) (σ t : ℝ) (n : ℕ) :
    average B (fun y => base σ (t - y) n) = term σ B t n := by
  simp only [base_shift]
  rw [average_const_mul, average_phase hB]
  rfl

/-- The full integrated absolute mass of one Euler term is its original amplitude. -/
theorem integral_norm_base {B : ℝ} (hB : 0 < B) (σ t : ℝ) (n : ℕ) :
    (∫ y : ℝ, ‖(density B y : ℂ) * base σ (t - y) n‖) = zetaPhasePrimeWeight σ n := by
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (density_pos hB _), norm_base, integral_mul_const, integral_density hB, one_mul]

/-- The complete original Euler logarithmic derivative is genuinely
integrable against the Gaussian, with the full complex norm controlled. -/
theorem integrable_neg_logDeriv {σ B : ℝ} (hσ : 1 < σ) (hB : 0 < B) (t : ℝ) :
    Integrable (fun y : ℝ => (density B y : ℂ) *
      (-logDeriv riemannZeta ((σ : ℂ) + I * (t - y)))) := by
  have he (y : ℝ) : (∑' n : ℕ, (density B y : ℂ) * base σ (t - y) n) =
      (density B y : ℂ) * (-logDeriv riemannZeta ((σ : ℂ) + I * (t - y))) := by
    rw [tsum_mul_left, neg_logDeriv_riemannZeta_eq_vonMangoldt (by simpa using hσ)]
    simp only [base, Complex.ofReal_sub]
  have hm : AEStronglyMeasurable (fun y : ℝ => ∑' n : ℕ, (density B y : ℂ) * base σ (t - y) n) :=
    AEStronglyMeasurable.tsum (fun n => (integrable_base hB σ t n).aestronglyMeasurable)
  apply ((integrable_density hB).mul_const (-logDeriv riemannZeta (σ : ℂ)).re).mono'
    (hm.congr (Eventually.of_forall he))
  filter_upwards with y
  rw [← he]
  have hs : Summable (base σ (t - y)) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  have h := norm_tsum_le_tsum_norm (hs.mul_left (density B y : ℂ)).norm
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (density_pos hB y), norm_base, tsum_mul_left,
    (hasSum_zetaPhasePrimeWeight hσ).tsum_eq] at h
  simpa only [tsum_mul_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (density_pos hB y)] using h

/-- The infinite prime sum and Gaussian integral commute on the actual
Euler half-plane; the complete complex series is retained on both sides. -/
theorem average_neg_logDeriv {σ B : ℝ} (hσ : 1 < σ) (hB : 0 < B) (t : ℝ) :
    average B (fun y => -logDeriv riemannZeta ((σ : ℂ) + I * (t - y))) = primeSum σ B t := by
  have hsum : Summable (fun n : ℕ => ∫ y : ℝ, ‖(density B y : ℂ) * base σ (t - y) n‖) := by
    simp only [integral_norm_base hB]
    exact (hasSum_zetaPhasePrimeWeight hσ).summable
  have h := integral_tsum_of_summable_integral_norm (integrable_base hB σ t) hsum
  have he (y : ℝ) : (∑' n : ℕ, (density B y : ℂ) * base σ (t - y) n) =
      (density B y : ℂ) * (-logDeriv riemannZeta ((σ : ℂ) + I * (t - y))) := by
    rw [tsum_mul_left, neg_logDeriv_riemannZeta_eq_vonMangoldt (by simpa using hσ)]
    simp only [base, Complex.ofReal_sub]
  have hb (n : ℕ) : (∫ y : ℝ, (density B y : ℂ) * base σ (t - y) n) = term σ B t n :=
    average_base hB σ t n
  simp only [hb, he] at h
  exact h.symm

end
end RiemannGaussian.ZetaGaussianPrimeAverage
