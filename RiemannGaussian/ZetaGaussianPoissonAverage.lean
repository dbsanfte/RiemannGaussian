/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianComplexPoleAverage
import RiemannGaussian.ZetaGaussianLaplaceMass

/-!
# The complete Gaussian average of the actual xi Poisson mass

The full complex pole identity evaluates every actual zero before real
projection. The resulting integrated absolute masses are precisely the
already summable Gaussian divisor contributions. A counting-measure
product argument therefore proves both integrability of the entire xi
response and the complete zero sum-integral exchange, including Re(s)=1.
-/

namespace RiemannGaussian.ZetaGaussianPoissonAverage
noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology
open GaussianVerticalAverage

/-- One actual Poisson term under the original normalized vertical Gaussian. -/
def weightedPoisson (B : ℝ) (s : ℂ) (ρ : NontrivialZetaZero) (y : ℝ) : ℝ :=
  density B y * zetaGlobalPoissonSummand (s - I * y) ρ

private theorem displacement_re {s : ℂ} (hs : 1 ≤ s.re) (ρ : NontrivialZetaZero) (y : ℝ) :
    0 < (s - I * y - ρ.1).re := by
  simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
  linarith [NontrivialZetaZero.re_lt_one ρ]

private theorem continuous_weightedPoisson (B : ℝ) {s : ℂ} (hs : 1 ≤ s.re)
    (ρ : NontrivialZetaZero) : Continuous (weightedPoisson B s ρ) := by
  have hn (y : ℝ) : Complex.normSq (s - I * y - ρ.1) ≠ 0 :=
    (Complex.normSq_pos.mpr (Complex.ne_zero_of_re_pos (displacement_re hs ρ y))).ne'
  unfold weightedPoisson zetaGlobalPoissonSummand density
  apply Continuous.mul
  · fun_prop
  · apply Continuous.div
    · fun_prop
    · fun_prop
    · exact hn

/-- Every weighted actual Poisson contribution has a proved nonnegative sign. -/
theorem weightedPoisson_nonneg {B : ℝ} (hB : 0 < B) {s : ℂ} (hs : 1 ≤ s.re)
    (ρ : NontrivialZetaZero) (y : ℝ) : 0 ≤ weightedPoisson B s ρ y :=
  mul_nonneg (density_pos hB y).le (zetaGlobalPoissonSummand_nonneg (by simpa using hs) ρ)

/-- Each original weighted Poisson atom is genuinely integrable, by the
full complex pole average rather than a scalar surrogate. -/
theorem integrable_weightedPoisson {B : ℝ} (hB : 0 < B) {s : ℂ} (hs : 1 ≤ s.re)
    (ρ : NontrivialZetaZero) : Integrable (weightedPoisson B s ρ) := by
  have hi := (GaussianComplexPoleAverage.integrable_pole hB
    (ZetaGaussianPoleRemainder.re_displacement_pos hs ρ)).re
  apply (hi.const_mul (analyticZetaZeroMultiplicity ρ : ℝ)).congr
  filter_upwards with y
  have he : s - ρ.1 - I * y = s - I * y - ρ.1 := by ring
  simp only [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.inv_re, he, Complex.sub_re, Complex.I_re, Complex.I_im,
    mul_zero, weightedPoisson, zetaGlobalPoissonSummand]
  ring

/-- The integral of one actual zero contribution is its complete
multiplicity-weighted Gaussian transform, including its original imaginary displacement. -/
theorem integral_weightedPoisson {B : ℝ} (hB : 0 < B) {s : ℂ} (hs : 1 ≤ s.re)
    (ρ : NontrivialZetaZero) :
    (∫ y : ℝ, weightedPoisson B s ρ y) = ZetaGaussianLaplaceMass.mass B s ρ := by
  have h := GaussianComplexPoleAverage.integral_poisson hB
    (ZetaGaussianPoleRemainder.re_displacement_pos hs ρ)
  have he (y : ℝ) : weightedPoisson B s ρ y = (analyticZetaZeroMultiplicity ρ : ℝ) *
      (density B y * ((s - ρ.1).re / Complex.normSq (s - ρ.1 - I * y))) := by
    have he : s - ρ.1 - I * y = s - I * y - ρ.1 := by ring
    simp only [weightedPoisson, zetaGlobalPoissonSummand, he, Complex.sub_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, sub_zero]
    ring
  simp only [he, integral_const_mul, h, ZetaGaussianLaplaceMass.mass]

/-- The full series of integrated absolute masses is already the proved
Gaussian zero mass; no unknown divisor majorant is introduced. -/
theorem summable_integral_norm {B : ℝ} (hB : 0 < B) {s : ℂ} (hs : 1 ≤ s.re) :
    Summable (fun ρ : NontrivialZetaZero => ∫ y : ℝ, ‖weightedPoisson B s ρ y‖) := by
  simp only [Real.norm_of_nonneg (weightedPoisson_nonneg hB hs _ _), integral_weightedPoisson hB hs]
  exact ZetaGaussianLaplaceMass.summable_mass hB hs

/-- The complete real Poisson series can be integrated term by term,
with every actual zero and analytic multiplicity included. -/
theorem tsum_integral_weightedPoisson {B : ℝ} (hB : 0 < B) {s : ℂ} (hs : 1 ≤ s.re) :
    (∑' ρ : NontrivialZetaZero, ∫ y : ℝ, weightedPoisson B s ρ y) =
      ∫ y : ℝ, ∑' ρ : NontrivialZetaZero, weightedPoisson B s ρ y :=
  integral_tsum_of_summable_integral_norm (integrable_weightedPoisson hB hs)
    (summable_integral_norm hB hs)

/-- The counting-measure product proves integrability of the full sum itself. -/
theorem integrable_tsum_weightedPoisson {B : ℝ} (hB : 0 < B) {s : ℂ} (hs : 1 ≤ s.re) :
    Integrable (fun y : ℝ => ∑' ρ : NontrivialZetaZero, weightedPoisson B s ρ y) := by
  have hm : Measurable (fun p : NontrivialZetaZero × ℝ => weightedPoisson B s p.1 p.2) := by
    apply measurable_from_prod_countable_right
    intro ρ
    exact (continuous_weightedPoisson B hs ρ).measurable
  have hp : Integrable (fun p : NontrivialZetaZero × ℝ => weightedPoisson B s p.1 p.2)
      (Measure.count.prod volume) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall (integrable_weightedPoisson hB hs), ?_⟩
    apply integrable_count_iff.mpr
    simpa only [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)] using
      summable_integral_norm hB hs
  apply hp.integral_prod_right.congr
  filter_upwards [hp.prod_left_ae] with y hy
  simpa using integral_countable hy

/-- The original complete xi response is the literal sum of its weighted Poisson atoms. -/
theorem tsum_weightedPoisson (B : ℝ) {s : ℂ} (hs : 1 ≤ s.re) (y : ℝ) :
    (∑' ρ : NontrivialZetaZero, weightedPoisson B s ρ y) =
      density B y * (logDeriv riemannXi (s - I * y)).re := by
  simp only [weightedPoisson, tsum_mul_left,
    tsum_zetaGlobalPoissonSummand (show 1 ≤ (s - I * y).re by simpa using hs)]

/-- The actual real xi logarithmic derivative is Gaussian-integrable on
the complete closed Euler half-plane, including its boundary. -/
theorem integrable_logDeriv_xi {B : ℝ} (hB : 0 < B) {s : ℂ} (hs : 1 ≤ s.re) :
    Integrable (fun y : ℝ => density B y * (logDeriv riemannXi (s - I * y)).re) :=
  (integrable_tsum_weightedPoisson hB hs).congr (Eventually.of_forall (tsum_weightedPoisson B hs))

/-- The full Gaussian xi average is exactly the actual complete Gaussian zero mass. -/
theorem integral_logDeriv_xi {B : ℝ} (hB : 0 < B) {s : ℂ} (hs : 1 ≤ s.re) :
    (∫ y : ℝ, density B y * (logDeriv riemannXi (s - I * y)).re) =
      ∑' ρ : NontrivialZetaZero, ZetaGaussianLaplaceMass.mass B s ρ := by
  have h := tsum_integral_weightedPoisson hB hs
  simpa only [integral_weightedPoisson hB hs, tsum_weightedPoisson B hs] using h.symm

/-- The exact averaged xi response retains its unsmoothed center and the
real part of the complete original complex cubic remainder. -/
theorem integral_logDeriv_xi_eq_center_add_remainder {B : ℝ} (hB : 0 < B)
    {s : ℂ} (hs : 1 ≤ s.re) :
    (∫ y : ℝ, density B y * (logDeriv riemannXi (s - I * y)).re) =
      (logDeriv riemannXi s).re +
        (∑' ρ : NontrivialZetaZero, ZetaGaussianPoleRemainder.term B s ρ).re := by
  rw [integral_logDeriv_xi hB hs, ZetaGaussianLaplaceMass.tsum_mass_eq hB hs]

end
end RiemannGaussian.ZetaGaussianPoissonAverage
