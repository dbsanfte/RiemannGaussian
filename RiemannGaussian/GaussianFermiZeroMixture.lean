/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiZeroInterchange
import RiemannGaussian.GaussianFermiMovingAllowance

/-!
# The actual Fermi zero side as a Gaussian explicit-formula average

The exact complex Gaussian mixture passes through the full analytic zeta
divisor by the proved summable integral-norm bound. This connects the
original physical reflected pair to the existing unconditional arithmetic
Gaussian explicit formula, retaining every normalization and multiplicity.
-/

namespace RiemannGaussian.GaussianFermiZeroMixture

noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology
open FermiLaplaceReflection GaussianFermiZeroPair GaussianFermiPairDecay
open GaussianFermiSpectralWeight GaussianFermiGaussianMixture
open GaussianFermiZeroTail GaussianFermiZeroInterchange

/-- At an actual complex point, the centered Gaussian atom is the original
Gaussian spectral summand. The evaluation abscissa cancels exactly. -/
theorem gaussianAtom_zero_eq {b : ℝ} (hb : 0 < b) (σ t y : ℝ) (ρ : ℂ) :
    gaussianAtom b (((σ : ℂ) + (t : ℂ) * I - ρ) -
        ((2 * σ - 1) / 2 : ℝ) - (y : ℂ) * I) =
      (Real.sqrt (Real.pi / b) : ℂ) *
        complexTranslatedGaussian (1 / (4 * b)) (t - y) (zetaSpectralCoordinate ρ) := by
  unfold gaussianAtom complexTranslatedGaussian zetaSpectralCoordinate
  congr 2
  push_cast
  have hbC : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  field_simp
  ring_nf
  simp [Complex.I_sq]
  ring

/-- One original physical reflected contribution equals its exact real
Gaussian average, including its analytic multiplicity and the paired
normalization. -/
theorem contribution_eq_integral {b c σ : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hσ : 1 / 2 ≤ σ) (t : ℝ) (ρ : NontrivialZetaZero) :
    contribution (b + c) σ t ρ = (Real.sqrt (Real.pi / b) / 4) *
      (∫ y : ℝ, zeroIntegrand (2 * σ - 1) c (1 / (4 * b)) t ρ y).re := by
  have ha : 0 ≤ 2 * σ - 1 := by linarith
  have he : ((2 * σ - 1 : ℝ) : ℂ) -
      starRingEnd ℂ ((σ : ℂ) + (t : ℂ) * I - ρ.1) =
      (σ : ℂ) + (t : ℂ) * I - (1 - starRingEnd ℂ ρ.1) := by
    push_cast
    simp only [map_sub, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have havg : (analyticZetaZeroMultiplicity ρ : ℂ) *
      (∫ y : ℝ, (density (2 * σ - 1) c y : ℂ) *
        gaussianAtom b (((σ : ℂ) + (t : ℂ) * I - ρ.1) -
          ((2 * σ - 1) / 2 : ℝ) - (y : ℂ) * I)) =
      (Real.sqrt (Real.pi / b) : ℂ) *
        (∫ y : ℝ, zeroIntegrand (2 * σ - 1) c (1 / (4 * b)) t ρ y) := by
    rw [← integral_const_mul, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    rw [gaussianAtom_zero_eq hb]
    unfold zeroIntegrand zetaGaussianDistinctZeroSummand
    ring
  have hre := congrArg Complex.re havg
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hre
  unfold contribution
  rw [← he, physical_pair_re_eq, pair_eq_gaussian_average ha hb hc]
  push_cast at hre
  norm_num [Complex.mul_re] at hre ⊢
  linear_combination hre / 4

/-- The density-weighted arithmetic Gaussian explicit formula is
absolutely integrable. Its identification with the canonical zero sum is
the repository's already unconditional theorem. -/
theorem integrable_density_arithmetic {a c ε : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (hε : 0 < ε) (t : ℝ) :
    Integrable (fun y : ℝ => density a c y * gaussianArithmeticExplicitFormula ε (t - y)) := by
  have hi := (integrable_density_canonical ha hc hε t).re
  have hir : Integrable (fun y : ℝ => density a c y * canonicalZetaGaussianZeroSum ε (t - y)) := by
    convert hi using 1
    funext y
    simp
  apply (hir.const_mul 2).congr
  filter_upwards with y
  rw [gaussianArithmeticExplicitFormula_eq_canonical hε, canonicalZetaSymmetricGaussianZeroSum]
  ring

/-- The complete original Fermi zero side has this actual arithmetic
Gaussian average as its sum. `HasSum` includes convergence and retains all
analytic multiplicities, for every positive split of the Gaussian scale. -/
theorem hasSum_contribution_arithmetic_average {b c σ : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hσ : 1 / 2 ≤ σ) (t : ℝ) :
    HasSum (contribution (b + c) σ t)
      ((Real.sqrt (Real.pi / b) / 8) *
        ∫ y : ℝ, density (2 * σ - 1) c y *
          gaussianArithmeticExplicitFormula (1 / (4 * b)) (t - y)) := by
  have ha : 0 ≤ 2 * σ - 1 := by linarith
  have hε : 0 < 1 / (4 * b) := by positivity
  have hs := (Complex.hasSum_re (hasSum_integral_zeroIntegrand ha hc hε t)).mul_left
    (Real.sqrt (Real.pi / b) / 4)
  have hq : HasSum (contribution (b + c) σ t)
      ((Real.sqrt (Real.pi / b) / 4) *
        (∫ y : ℝ, (density (2 * σ - 1) c y : ℂ) *
          (canonicalZetaGaussianZeroSum (1 / (4 * b)) (t - y) : ℂ)).re) := by
    exact hs.congr_fun fun ρ => contribution_eq_integral hb hc hσ t ρ
  have hir := integrable_density_canonical ha hc hε t
  have hre : (∫ y : ℝ, ((density (2 * σ - 1) c y : ℂ) *
      (canonicalZetaGaussianZeroSum (1 / (4 * b)) (t - y) : ℂ)).re) =
      (∫ y : ℝ, (density (2 * σ - 1) c y : ℂ) *
        (canonicalZetaGaussianZeroSum (1 / (4 * b)) (t - y) : ℂ)).re := integral_re hir
  have hre' : (∫ y : ℝ, density (2 * σ - 1) c y *
      canonicalZetaGaussianZeroSum (1 / (4 * b)) (t - y)) =
      (∫ y : ℝ, (density (2 * σ - 1) c y : ℂ) *
        (canonicalZetaGaussianZeroSum (1 / (4 * b)) (t - y) : ℂ)).re := by
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero] using hre
  have har : (∫ y : ℝ, density (2 * σ - 1) c y *
      gaussianArithmeticExplicitFormula (1 / (4 * b)) (t - y)) =
      2 * ∫ y : ℝ, density (2 * σ - 1) c y *
        canonicalZetaGaussianZeroSum (1 / (4 * b)) (t - y) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    rw [gaussianArithmeticExplicitFormula_eq_canonical hε, canonicalZetaSymmetricGaussianZeroSum]
    ring
  rw [har]
  convert hq using 1
  rw [← hre']
  ring

/-- The original multiplicity-weighted Fermi zero side equals a concrete
average of the unconditional arithmetic Gaussian explicit formula. -/
theorem zero_side_eq_arithmetic_average {b c σ : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hσ : 1 / 2 ≤ σ) (t : ℝ) :
    (∑' ρ : NontrivialZetaZero, contribution (b + c) σ t ρ) =
      (Real.sqrt (Real.pi / b) / 8) *
        ∫ y : ℝ, density (2 * σ - 1) c y *
          gaussianArithmeticExplicitFormula (1 / (4 * b)) (t - y) :=
  (hasSum_contribution_arithmetic_average hb hc hσ t).tsum_eq

/-- The earlier vanishing whole-zero allowance now bounds the exact
arithmetic average, uniformly over every positive split of each admissible
Gaussian scale and every ordinate in the half-height band. -/
theorem exists_uniform_arithmetic_average_lower_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (H b c t : ℝ), 1 ≤ H → 0 < b → 0 < c →
      zetaPoleReserveZeroMargin H ^ 2 ≤ b + c → b + c ≤ 1 → 2 * |t| ≤ H →
      -(K * (Real.log (H + 2) / Real.sqrt H)) ≤
        (Real.sqrt (Real.pi / b) / 8) *
          ∫ y : ℝ, density (2 * (1 - zetaPoleReserveZeroMargin H) - 1) c y *
            gaussianArithmeticExplicitFormula (1 / (4 * b)) (t - y) := by
  obtain ⟨K, hK, hbound⟩ := GaussianFermiMovingAllowance.exists_uniform_zero_side_bound
  refine ⟨K, hK, ?_⟩
  intro H b c t hH hb hc hscale hsum ht
  have hσ : 1 / 2 ≤ 1 - zetaPoleReserveZeroMargin H := by
    linarith [(zetaPoleReserveZeroMargin_bounds H).2]
  have h := (hbound H (b + c) t hH hscale hsum ht).2
  rwa [zero_side_eq_arithmetic_average hb hc hσ t] at h

end
end RiemannGaussian.GaussianFermiZeroMixture
