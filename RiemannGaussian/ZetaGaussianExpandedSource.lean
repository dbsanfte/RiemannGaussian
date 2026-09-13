/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianExpandedScale

/-!
# The selected-zero source at smaller Gaussian dilations

For `q ≥ 9/100`, the wider physical strip pays at most two units for the
cotangent correction. The exact Gaussian homogeneity and multiplicity
then retain the original `48000*q` selected source. The positive Poisson
reserve is retained in the statement.
-/

namespace RiemannGaussian.ZetaGaussianExpandedSource
noncomputable section
open ZetaGaussianScaledBandBudget (width shift gaussianScale)
open ZetaGaussianExpandedScale GaussianFermiLaplaceOrder
open ZetaGaussianStripExplicit ZetaGaussianStripPhaseFamily ZetaStripEulerConstraint
open ZetaAngularPhaseAllowance DerivativeOrderComparison

/-- A selected zero within the scaled width retains the complete source
at least `48000*q`, including multiplicity and the Poisson reserve. -/
theorem selected_source_lower {a₁ q : ℝ} (ha₁ : 79 / 250 ≤ a₁) (hq : 9 / 100 ≤ q)
    (ρ : NontrivialZetaZero) (hnear : 1 - ρ.1.re ≤ width q) :
    48000 * q ≤ a₁ * ((analyticZetaZeroMultiplicity ρ : ℝ) *
      (halfGaussian (gaussianScale q) (1 + shift q - ρ.1.re) -
        Real.pi ^ 2 * (1 + shift q - ρ.1.re) / (8 * halfWidth 9 (shift q) ^ 2)) +
      factor 9 (gaussianScale q) (shift q) * ((analyticZetaZeroMultiplicity ρ : ℝ) /
        (1 + shift q + halfWidth 9 (shift q) - ρ.1.re))) := by
  have hq0 : 0 < q := by linarith
  obtain ⟨hx, hxu⟩ := shift_bounds hq
  obtain ⟨hu, huu⟩ := width_bounds hq
  have hB := (gaussianScale_bounds hq).1
  have hη := halfWidth_pos 9 hx
  have hηl := (geometry hq).1
  have hd : 0 < 1 + shift q - ρ.1.re := by linarith [ρ.re_lt_one]
  have hdu : 1 + shift q - ρ.1.re ≤ shift q + width q := by linarith
  have hG : 152000 * q ≤ halfGaussian (gaussianScale q) (1 + shift q - ρ.1.re) :=
    (source_lower hq0).trans (halfGaussian_antitone hB hdu)
  have hpi : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hcot : Real.pi ^ 2 * (1 + shift q - ρ.1.re) / (8 * halfWidth 9 (shift q) ^ 2) ≤ 2 := by
    calc
      _ ≤ 16 * (1 / 40500000 + 1 / 40500) / (8 * (1 / 200 : ℝ) ^ 2) := by
        gcongr
        linarith
      _ ≤ 2 := by norm_num [GaussianStripProfile.shift, GaussianStripProfile.width]
  have hm : (1 : ℝ) ≤ (analyticZetaZeroMultiplicity ρ : ℝ) := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive ρ
  have hbase : 151977 * q ≤ halfGaussian (gaussianScale q) (1 + shift q - ρ.1.re) -
      Real.pi ^ 2 * (1 + shift q - ρ.1.re) / (8 * halfWidth 9 (shift q) ^ 2) := by linarith
  have hweighted := mul_le_mul hm hbase (by positivity : (0 : ℝ) ≤ 151977 * q) (by linarith)
  have hreserve : 0 ≤ factor 9 (gaussianScale q) (shift q) * ((analyticZetaZeroMultiplicity ρ : ℝ) /
      (1 + shift q + halfWidth 9 (shift q) - ρ.1.re)) := by
    have hden : 0 < 1 + shift q + halfWidth 9 (shift q) - ρ.1.re := by linarith
    unfold factor
    positivity
  have htotal : 151977 * q ≤ (analyticZetaZeroMultiplicity ρ : ℝ) *
      (halfGaussian (gaussianScale q) (1 + shift q - ρ.1.re) -
        Real.pi ^ 2 * (1 + shift q - ρ.1.re) / (8 * halfWidth 9 (shift q) ^ 2)) +
      factor 9 (gaussianScale q) (shift q) * ((analyticZetaZeroMultiplicity ρ : ℝ) /
        (1 + shift q + halfWidth 9 (shift q) - ρ.1.re)) := by nlinarith only [hweighted, hreserve]
  have h := mul_le_mul ha₁ htotal (by positivity : (0 : ℝ) ≤ 151977 * q) (by linarith)
  nlinarith only [h, hq]

end
end RiemannGaussian.ZetaGaussianExpandedSource
