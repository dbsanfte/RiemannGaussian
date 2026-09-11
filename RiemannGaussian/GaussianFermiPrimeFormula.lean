/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiCosineAverage
import RiemannGaussian.GaussianFermiZeroMixture
import RiemannGaussian.GaussianPositivityCertificate

/-!
# The literal Fermi prime series in the full zero formula

The exact characteristic function evaluates each prime-power frequency.
Absolute convergence justifies interchanging the infinite prime series and
the spectral integral. The resulting explicit formula retains the original
cosine phase and has a literal positive Fermi amplitude, with no unspecified
arithmetic remainder.
-/

namespace RiemannGaussian.GaussianFermiPrimeFormula

noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology
open GaussianFermiSpectralWeight GaussianFermiCosineAverage GaussianFermiZeroPair
open GaussianFermiZeroMixture GaussianFermiZeroTail

/-- One literal prime-power term, with its original logarithmic phase. -/
def primeSummand (a B t : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / Real.sqrt n * signal a B (Real.log n) *
    Real.cos (t * Real.log n)

/-- The original Fermi-weighted von Mangoldt series. -/
def primeSum (a B t : ℝ) : ℝ := ∑' n : ℕ, primeSummand a B t n

/-- Every Gaussian prime-power term is integrable against the actual
spectral density. No estimate has removed its cosine phase. -/
theorem integrable_density_primeSummand {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (ε t : ℝ) (n : ℕ) :
    Integrable (fun y : ℝ => density a c y * gaussianPrimeSummand ε (t - y) n) := by
  apply ((integrable_density_cosine ha hc t (Real.log n)).const_mul
    (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
      Real.exp (-(Real.log n) ^ 2 / (4 * ε)))).congr
  filter_upwards with y
  unfold gaussianPrimeSummand
  ring

/-- Each integrated norm has a common summable Gaussian prime majorant. -/
theorem integral_norm_density_primeSummand_le {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (ε t : ℝ) (n : ℕ) :
    (∫ y : ℝ, ‖density a c y * gaussianPrimeSummand ε (t - y) n‖) ≤
      (∫ y : ℝ, |density a c y|) * gaussianPrimeSummand ε 0 n := by
  calc
    _ ≤ ∫ y : ℝ, |density a c y| * gaussianPrimeSummand ε 0 n := by
      apply integral_mono (integrable_density_primeSummand ha hc ε t n).norm
        ((integrable_density ha hc).abs.mul_const _)
      intro y
      dsimp only
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left
        (abs_gaussianPrimeSummand_le_zero_center ε (t - y) n) (abs_nonneg _)
    _ = _ := integral_mul_const _ _

/-- The entire family of prime integral norms is summable. -/
theorem summable_integral_norm_density_primeSummand {a c ε : ℝ} (ha : 0 ≤ a)
    (hc : 0 < c) (hε : 0 < ε) (t : ℝ) :
    Summable (fun n : ℕ => ∫ y : ℝ,
      ‖density a c y * gaussianPrimeSummand ε (t - y) n‖) := by
  exact ((summable_gaussianPrimeSummand hε 0).mul_left
    (∫ y : ℝ, |density a c y|)).of_nonneg_of_le
      (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (integral_norm_density_primeSummand_le ha hc ε t)

/-- The density-weighted full Gaussian prime series is itself absolutely
integrable, with the counting-measure interchange justified. -/
theorem integrable_density_primeSum {a c ε : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (hε : 0 < ε) (t : ℝ) :
    Integrable (fun y : ℝ => density a c y * gaussianPrimeSum ε (t - y)) := by
  have hd := continuous_density hc a
  have hmeas : Measurable (fun p : ℕ × ℝ =>
      density a c p.2 * gaussianPrimeSummand ε (t - p.2) p.1) := by
    apply measurable_from_prod_countable_right
    intro n
    have hcont : Continuous (fun y : ℝ => density a c y *
        gaussianPrimeSummand ε (t - y) n) := by
      unfold gaussianPrimeSummand
      fun_prop
    exact hcont.measurable
  have hprod : Integrable (fun p : ℕ × ℝ =>
      density a c p.2 * gaussianPrimeSummand ε (t - p.2) p.1)
      (Measure.count.prod volume) := by
    apply (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall (integrable_density_primeSummand ha hc ε t), ?_⟩
    apply integrable_count_iff.mpr
    simpa only [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)] using
      summable_integral_norm_density_primeSummand ha hc hε t
  apply hprod.integral_prod_right.congr
  filter_upwards [hprod.prod_left_ae] with y hy
  simpa [gaussianPrimeSum, tsum_mul_left] using integral_countable hy

/-- The exact Gaussian scale conversion at every real time. -/
theorem reciprocal_gaussian_weight {b : ℝ} (hb : 0 < b) (x : ℝ) :
    Real.exp (-x ^ 2 / (4 * (1 / (4 * b)))) = window b x := by
  unfold window
  congr 1
  field_simp

/-- Integrating one Gaussian prime-power term produces exactly twice its
literal Fermi term, with the two scales recombined. -/
theorem integral_density_primeSummand {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hc : 0 < c) (t : ℝ) (n : ℕ) :
    (∫ y : ℝ, density a c y * gaussianPrimeSummand (1 / (4 * b)) (t - y) n) =
      2 * primeSummand a (b + c) t n := by
  calc
    _ = (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        Real.exp (-(Real.log n) ^ 2 / (4 * (1 / (4 * b))))) *
          ∫ y : ℝ, density a c y * Real.cos ((t - y) * Real.log n) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      unfold gaussianPrimeSummand
      ring
    _ = _ := by
      rw [integral_density_cosine ha hc, reciprocal_gaussian_weight hb]
      unfold primeSummand
      rw [← signal_split a b c]
      ring

/-- `HasSum` records both the literal Fermi prime-series convergence and
its exact equality with the Gaussian prime average. -/
theorem hasSum_primeSummand_average {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hc : 0 < c) (t : ℝ) :
    HasSum (primeSummand a (b + c) t)
      ((1 / 2 : ℝ) * ∫ y : ℝ, density a c y * gaussianPrimeSum (1 / (4 * b)) (t - y)) := by
  have hε : 0 < 1 / (4 * b) := by positivity
  have hs := (hasSum_integral_of_summable_integral_norm
    (integrable_density_primeSummand ha hc (1 / (4 * b)) t)
    (summable_integral_norm_density_primeSummand ha hc hε t)).mul_left (1 / 2 : ℝ)
  have hsum : (fun y : ℝ => ∑' n : ℕ,
      density a c y * gaussianPrimeSummand (1 / (4 * b)) (t - y) n) =
      fun y : ℝ => density a c y * gaussianPrimeSum (1 / (4 * b)) (t - y) := by
    funext y
    rw [tsum_mul_left]
    rfl
  rw [hsum] at hs
  apply hs.congr_fun
  intro n
  rw [integral_density_primeSummand ha hb hc]
  ring

/-- Every positive-width literal Fermi prime series is absolutely
convergent, independently of a particular Gaussian split. -/
theorem summable_primeSummand {a B : ℝ} (ha : 0 ≤ a) (hB : 0 < B) (t : ℝ) :
    Summable (primeSummand a B t) := by
  have hhalf : 0 < B / 2 := by positivity
  simpa only [add_halves] using (hasSum_primeSummand_average ha hhalf hhalf t).summable

/-- The full prime average evaluates to the original Fermi prime series. -/
theorem integral_density_primeSum {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hc : 0 < c) (t : ℝ) :
    (∫ y : ℝ, density a c y * gaussianPrimeSum (1 / (4 * b)) (t - y)) =
      2 * primeSum a (b + c) t := by
  have h := (hasSum_primeSummand_average ha hb hc t).tsum_eq
  change primeSum a (b + c) t = _ at h
  linarith

/-- The square-root conversion between the two Gaussian conventions. -/
theorem sqrt_scale_ratio (b : ℝ) :
    Real.sqrt (Real.pi / b) = 2 * Real.sqrt (Real.pi * (1 / (4 * b))) := by
  have he : Real.pi / b = 4 * (Real.pi * (1 / (4 * b))) := by ring
  rw [he, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

/-- The normalized Gaussian prime contribution becomes exactly the
literal Fermi series; no normalization constant is absorbed into a bound. -/
theorem normalized_prime_average {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hc : 0 < c) (t : ℝ) :
    (Real.sqrt (Real.pi / b) / 8) *
      (∫ y : ℝ, density a c y * gaussianPrimeContribution (1 / (4 * b)) (t - y)) =
      primeSum a (b + c) t := by
  have hr : Real.sqrt (Real.pi * (1 / (4 * b))) ≠ 0 := by positivity
  have he : (fun y : ℝ => density a c y *
      gaussianPrimeContribution (1 / (4 * b)) (t - y)) =
      fun y : ℝ => (2 / Real.sqrt (Real.pi * (1 / (4 * b)))) *
        (density a c y * gaussianPrimeSum (1 / (4 * b)) (t - y)) := by
    funext y
    unfold gaussianPrimeContribution
    ring
  rw [he, integral_const_mul, integral_density_primeSum ha hb hc, sqrt_scale_ratio b]
  field_simp
  ring

/-- The averaged Gaussian prime contribution is absolutely integrable. -/
theorem integrable_density_primeContribution {a c ε : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (hε : 0 < ε) (t : ℝ) :
    Integrable (fun y : ℝ => density a c y * gaussianPrimeContribution ε (t - y)) := by
  apply ((integrable_density_primeSum ha hc hε t).const_mul
    (2 / Real.sqrt (Real.pi * ε))).congr
  filter_upwards with y
  unfold gaussianPrimeContribution
  ring

/-- The actual Archimedean average is integrable, by the independently
proved arithmetic and prime integrability statements. -/
theorem integrable_density_archimedean {a c ε : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (hε : 0 < ε) (t : ℝ) :
    Integrable (fun y : ℝ => density a c y * gaussianArchimedeanContribution ε (t - y)) := by
  apply ((integrable_density_arithmetic ha hc hε t).add
    (integrable_density_primeContribution ha hc hε t)).congr
  filter_upwards with y
  dsimp only [Pi.add_apply]
  unfold gaussianArithmeticExplicitFormula
  ring

/-- The full multiplicity-aware zero side equals the actual Archimedean
average minus the literal convergent Fermi prime series. -/
theorem zero_side_eq_archimedean_sub_prime {b c σ : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hσ : 1 / 2 ≤ σ) (t : ℝ) :
    (∑' ρ : NontrivialZetaZero, contribution (b + c) σ t ρ) =
      (Real.sqrt (Real.pi / b) / 8) *
        (∫ y : ℝ, density (2 * σ - 1) c y *
          gaussianArchimedeanContribution (1 / (4 * b)) (t - y)) -
      primeSum (2 * σ - 1) (b + c) t := by
  have ha : 0 ≤ 2 * σ - 1 := by linarith
  have hε : 0 < 1 / (4 * b) := by positivity
  rw [zero_side_eq_arithmetic_average hb hc hσ]
  simp_rw [gaussianArithmeticExplicitFormula, mul_sub]
  rw [integral_sub (integrable_density_archimedean ha hc hε t)
    (integrable_density_primeContribution ha hc hε t), mul_sub,
    normalized_prime_average ha hb hc]

/-- The vanishing zero-side allowance gives a uniform upper bound for the
literal Fermi prime sum by its Archimedean average plus that allowance. -/
theorem exists_uniform_prime_archimedean_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (H b c t : ℝ), 1 ≤ H → 0 < b → 0 < c →
      zetaPoleReserveZeroMargin H ^ 2 ≤ b + c → b + c ≤ 1 → 2 * |t| ≤ H →
      primeSum (2 * (1 - zetaPoleReserveZeroMargin H) - 1) (b + c) t ≤
        (Real.sqrt (Real.pi / b) / 8) *
          (∫ y : ℝ, density (2 * (1 - zetaPoleReserveZeroMargin H) - 1) c y *
            gaussianArchimedeanContribution (1 / (4 * b)) (t - y)) +
        K * (Real.log (H + 2) / Real.sqrt H) := by
  obtain ⟨K, hK, hbound⟩ := GaussianFermiMovingAllowance.exists_uniform_zero_side_bound
  refine ⟨K, hK, ?_⟩
  intro H b c t hH hb hc hscale hsum ht
  have hσ : 1 / 2 ≤ 1 - zetaPoleReserveZeroMargin H := by
    linarith [(zetaPoleReserveZeroMargin_bounds H).2]
  have h := (hbound H (b + c) t hH hscale hsum ht).2
  rw [zero_side_eq_archimedean_sub_prime hb hc hσ t] at h
  linarith

end
end RiemannGaussian.GaussianFermiPrimeFormula
