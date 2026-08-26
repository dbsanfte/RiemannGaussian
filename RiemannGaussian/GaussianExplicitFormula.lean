import RiemannGaussian.GaussianComplexHeat
import RiemannGaussian.GaussianDigammaGrowth
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Arithmetic Gaussian explicit-formula interface

This file fixes the normalization of the prime and Archimedean sides used by
the exact certificates.  It first proves absolute convergence of the
Gaussian-weighted von Mangoldt series; the eventual identification with the
canonical multiplicity-weighted zero sum is the remaining explicit-formula
theorem.
-/

namespace RiemannGaussian

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

/-- The positive comparison series used for the Gaussian prime sum. -/
theorem summable_vonMangoldt_div_sq :
    Summable (fun n : ℕ =>
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2) := by
  have hL := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (2 : ℂ)) (by norm_num)
  have hnorm := hL.norm
  refine hnorm.congr fun n => ?_
  rw [LSeries.norm_term_eq]
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn]
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    norm_num [Real.rpow_two]

/-- One real prime-power summand in the translated-Gaussian explicit
formula, before its common normalization. -/
def gaussianPrimeSummand (ε t : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / Real.sqrt n *
    Real.exp (-(Real.log n) ^ 2 / (4 * ε)) *
      Real.cos (t * Real.log n)

lemma gaussian_log_weight_le_inv_sq
    {ε x : ℝ} (hε : 0 < ε) (hx : 0 < x)
    (hlog : 8 * ε ≤ Real.log x) :
    Real.exp (-(Real.log x) ^ 2 / (4 * ε)) ≤ 1 / x ^ 2 := by
  have hlog0 : 0 ≤ Real.log x := by linarith
  have hexponent : -(Real.log x) ^ 2 / (4 * ε) ≤
      -2 * Real.log x := by
    have hden : 0 < 4 * ε := mul_pos (by norm_num) hε
    rw [div_le_iff₀ hden]
    nlinarith [mul_nonneg hlog0 (sub_nonneg.mpr hlog)]
  calc
    Real.exp (-(Real.log x) ^ 2 / (4 * ε)) ≤
        Real.exp (-2 * Real.log x) := Real.exp_le_exp.mpr hexponent
    _ = 1 / x ^ 2 := by
      rw [show -2 * Real.log x = -(2 * Real.log x) by ring,
        Real.exp_neg,
        show 2 * Real.log x = Real.log x + Real.log x by ring,
        Real.exp_add, Real.exp_log hx]
      simp [one_div, pow_two]

/-- For positive width, the arithmetic Gaussian prime series is absolutely
summable for every real center. -/
theorem summable_gaussianPrimeSummand
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Summable (gaussianPrimeSummand ε t) := by
  have hlogNat : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ n : ℕ in atTop, 8 * ε ≤ Real.log (n : ℝ) :=
    hlogNat.eventually_ge_atTop (8 * ε)
  apply summable_vonMangoldt_div_sq.of_norm_bounded_eventually_nat
  filter_upwards [hevent] with n hnlog
  have hnlog0 : 0 < Real.log (n : ℝ) := lt_of_lt_of_le (by positivity) hnlog
  have hn1 : 1 < (n : ℝ) :=
    (Real.log_pos_iff (Nat.cast_nonneg n)).mp hnlog0
  have hn0 : 0 < (n : ℝ) := zero_lt_one.trans hn1
  have hsqrt1 : 1 ≤ Real.sqrt (n : ℝ) := by
    rw [Real.one_le_sqrt]
    exact hn1.le
  have hweight := gaussian_log_weight_le_inv_sq hε hn0 hnlog
  have hΛ0 : 0 ≤ ArithmeticFunction.vonMangoldt n := by positivity
  have hsqrt0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hinvSqrt : 0 ≤ (Real.sqrt (n : ℝ))⁻¹ := inv_nonneg.mpr hsqrt0
  have hcoef0 : 0 ≤
      ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ) :=
    div_nonneg hΛ0 hsqrt0
  rw [Real.norm_eq_abs, gaussianPrimeSummand, abs_mul, abs_mul,
    abs_of_nonneg hcoef0, abs_of_pos (Real.exp_pos _)]
  calc
    ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ) *
          Real.exp (-(Real.log (n : ℝ)) ^ 2 / (4 * ε)) *
        |Real.cos (t * Real.log (n : ℝ))| ≤
        ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ) *
          Real.exp (-(Real.log (n : ℝ)) ^ 2 / (4 * ε)) := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
          (mul_nonneg hcoef0 (Real.exp_nonneg _))
    _ ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ) *
          (1 / (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hweight hcoef0
    _ ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2 := by
      have hdiv : ArithmeticFunction.vonMangoldt n /
          Real.sqrt (n : ℝ) ≤ ArithmeticFunction.vonMangoldt n := by
        rw [div_eq_mul_inv]
        exact mul_le_of_le_one_right hΛ0 (inv_le_one_of_one_le₀ hsqrt1)
      simpa [div_eq_mul_inv, mul_assoc] using
        mul_le_mul_of_nonneg_right hdiv (inv_nonneg.mpr (sq_nonneg _))

/-- Absolutely convergent Gaussian-smoothed von Mangoldt sum. -/
def gaussianPrimeSum (ε t : ℝ) : ℝ :=
  ∑' n : ℕ, gaussianPrimeSummand ε t n

/-- Prime-power term in the normalization used by the certificate ledgers. -/
def gaussianPrimeContribution (ε t : ℝ) : ℝ :=
  2 / Real.sqrt (Real.pi * ε) * gaussianPrimeSum ε t

theorem gaussianPrimeSummand_neg_center (ε t : ℝ) (n : ℕ) :
    gaussianPrimeSummand ε (-t) n = gaussianPrimeSummand ε t n := by
  unfold gaussianPrimeSummand
  rw [neg_mul, Real.cos_neg]

theorem gaussianPrimeSum_neg_center (ε t : ℝ) :
    gaussianPrimeSum ε (-t) = gaussianPrimeSum ε t := by
  unfold gaussianPrimeSum
  apply tsum_congr
  exact gaussianPrimeSummand_neg_center ε t

theorem gaussianPrimeContribution_neg_center (ε t : ℝ) :
    gaussianPrimeContribution ε (-t) =
      gaussianPrimeContribution ε t := by
  simp [gaussianPrimeContribution, gaussianPrimeSum_neg_center]

/-- Real Archimedean density on the completed-zeta critical line. -/
def riemannArchimedeanDensity (r : ℝ) : ℝ :=
  (Complex.digamma (1 / 4 + Complex.I * (r / 2))).re

theorem continuous_riemannArchimedeanDensity :
    Continuous riemannArchimedeanDensity :=
  Complex.continuous_re.comp continuous_digamma_quarter_line

/-- The Archimedean density is integrable against every translated
positive-width Gaussian. -/
theorem integrable_translatedGaussian_mul_riemannArchimedeanDensity
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Integrable (fun r : ℝ =>
      translatedGaussian ε t r * riemannArchimedeanDensity r) := by
  simpa only [translatedGaussian, riemannArchimedeanDensity] using
    integrable_translatedGaussian_mul_re_digamma_quarter hε t

/-- The even Gaussian used by the arithmetic certificates therefore has a
genuinely convergent Archimedean integral. -/
theorem integrable_symmetricGaussian_mul_riemannArchimedeanDensity
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Integrable (fun r : ℝ =>
      symmetricGaussian ε t r * riemannArchimedeanDensity r) := by
  have hfirst :=
    integrable_translatedGaussian_mul_riemannArchimedeanDensity hε t
  have hsecondCenter :=
    integrable_translatedGaussian_mul_riemannArchimedeanDensity hε (-t)
  have hsecond : Integrable (fun r : ℝ =>
      translatedGaussian ε t (-r) * riemannArchimedeanDensity r) := by
    apply hsecondCenter.congr
    filter_upwards with r
    unfold translatedGaussian
    congr 2
    ring
  rw [show
    (fun r : ℝ =>
      symmetricGaussian ε t r * riemannArchimedeanDensity r) =
      fun r : ℝ =>
        translatedGaussian ε t r * riemannArchimedeanDensity r +
          translatedGaussian ε t (-r) * riemannArchimedeanDensity r by
    funext r
    unfold symmetricGaussian
    ring]
  exact hfirst.add hsecond

/-- Digamma integral in the Gaussian explicit formula. -/
def gaussianDigammaIntegral (ε t : ℝ) : ℝ :=
  (1 / Real.pi) *
    ∫ r : ℝ in Ioi 0,
      symmetricGaussian ε t r * riemannArchimedeanDensity r

/-- Archimedean and elementary boundary terms in the exact normalization of
the research certificates. -/
def gaussianArchimedeanContribution (ε t : ℝ) : ℝ :=
  4 * Real.exp (ε / 4 - ε * t ^ 2) * Real.cos (ε * t) -
    Real.log Real.pi / Real.sqrt (Real.pi * ε) +
      gaussianDigammaIntegral ε t

/-- The fully arithmetic Gaussian expression whose explicit-formula
identification with the canonical zero sum remains to be proved. -/
def gaussianArithmeticExplicitFormula (ε t : ℝ) : ℝ :=
  gaussianArchimedeanContribution ε t -
    gaussianPrimeContribution ε t

lemma symmetricGaussian_neg_center (ε t r : ℝ) :
    symmetricGaussian ε (-t) r = symmetricGaussian ε t r := by
  have hfirst : translatedGaussian ε (-t) r =
      translatedGaussian ε t (-r) := by
    unfold translatedGaussian
    congr 1
    ring
  have hsecond : translatedGaussian ε (-t) (-r) =
      translatedGaussian ε t r := by
    unfold translatedGaussian
    congr 1
    ring
  simp only [symmetricGaussian, hfirst, hsecond, add_comm]

theorem gaussianDigammaIntegral_neg_center (ε t : ℝ) :
    gaussianDigammaIntegral ε (-t) = gaussianDigammaIntegral ε t := by
  unfold gaussianDigammaIntegral
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [symmetricGaussian_neg_center]

theorem gaussianArchimedeanContribution_neg_center (ε t : ℝ) :
    gaussianArchimedeanContribution ε (-t) =
      gaussianArchimedeanContribution ε t := by
  simp only [gaussianArchimedeanContribution,
    gaussianDigammaIntegral_neg_center, neg_sq, mul_neg, Real.cos_neg]

theorem gaussianArithmeticExplicitFormula_neg_center (ε t : ℝ) :
    gaussianArithmeticExplicitFormula ε (-t) =
      gaussianArithmeticExplicitFormula ε t := by
  unfold gaussianArithmeticExplicitFormula
  rw [
    gaussianArchimedeanContribution_neg_center,
    gaussianPrimeContribution_neg_center]

/-- The one remaining analytic identification, stated with all convergence,
multiplicity, and normalization choices fixed by the preceding files. -/
def GaussianArithmeticExplicitFormulaIdentified : Prop :=
  ∀ ε t : ℝ, 0 < ε →
    gaussianArithmeticExplicitFormula ε t =
      canonicalZetaSymmetricGaussianZeroSum ε t

/-- Once the explicit-formula identification is supplied, the arithmetic
expression inherits the exact Gaussian heat propagation law. -/
theorem gaussianArithmeticExplicitFormula_heat_convolution
    (hExplicit : GaussianArithmeticExplicitFormulaIdentified)
    {a ε : ℝ} (hε : 0 < ε) (hεa : ε < a) (t : ℝ) :
    gaussianArithmeticExplicitFormula ε t =
      heatConvolution a (heatParameter a ε)
        (gaussianArithmeticExplicitFormula a) t := by
  have ha : 0 < a := hε.trans hεa
  calc
    gaussianArithmeticExplicitFormula ε t =
        canonicalZetaSymmetricGaussianZeroSum ε t :=
      hExplicit ε t hε
    _ = heatConvolution a (heatParameter a ε)
        (canonicalZetaSymmetricGaussianZeroSum a) t :=
      canonicalZetaSymmetricGaussianZeroSum_heat_convolution_unconditional
        hε hεa t
    _ = heatConvolution a (heatParameter a ε)
        (gaussianArithmeticExplicitFormula a) t :=
      congrArg
        (fun f : ℝ → ℝ => heatConvolution a (heatParameter a ε) f t)
        (funext fun s => (hExplicit a s ha).symm)

/-- Under the explicit-formula identification, nonnegativity of the
arithmetic expression at one width propagates to every smaller width. -/
theorem gaussianArithmeticExplicitFormula_nonnegative_of_larger_width
    (hExplicit : GaussianArithmeticExplicitFormulaIdentified)
    {a ε : ℝ} (hε : 0 < ε) (hεa : ε < a)
    (haNonnegative :
      ∀ s : ℝ, 0 ≤ gaussianArithmeticExplicitFormula a s)
    (t : ℝ) :
    0 ≤ gaussianArithmeticExplicitFormula ε t := by
  rw [hExplicit ε t hε]
  apply canonicalZetaSymmetricGaussianZeroSum_nonnegative_of_larger_width
    hε hεa
  intro s
  rw [← hExplicit a s (hε.trans hεa)]
  exact haNonnegative s

/-- Once the arithmetic explicit formula is identified, its all-width
nonnegativity is exactly RH. -/
theorem gaussianArithmeticExplicitFormula_nonnegative_iff_RH
    (hExplicit : GaussianArithmeticExplicitFormulaIdentified) :
    ZetaSymmetricGaussianZeroSumNonnegative
        gaussianArithmeticExplicitFormula ↔
      RiemannHypothesis := by
  rw [← canonicalZetaSymmetricGaussianZeroSum_nonnegative_iff_RH]
  constructor
  · intro h ε t hε
    rw [← hExplicit ε t hε]
    exact h ε t hε
  · intro h ε t hε
    rw [hExplicit ε t hε]
    exact h ε t hε

end

end RiemannGaussian
