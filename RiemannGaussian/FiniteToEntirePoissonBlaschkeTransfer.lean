import RiemannGaussian.FiniteToEntireProperTimeActionTransfer
import RiemannGaussian.RiemannXiHyperbolicDefectPoissonEquivalence

/-!
# Transferring the finite Hardy obstruction to Poisson and Blaschke mass

At a noncolliding upper observation point, the complete logarithmic defect is
bounded by an explicit gap coefficient times the complete Poisson defect.  The
Poisson defect is exactly the observation height times the complete elementary
Blaschke derivative variation.  This file transports the canonical finite
Hardy alternative through both facts.

Under failure of RH, Lean therefore obtains an explicit positive normalized
Poisson threshold and an explicit positive normalized Blaschke-variation
threshold.  Either both thresholds survive in the complete spectral masses,
or the finite polynomial upper-height masses cross every nonnegative bound
infinitely often.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The finite comparison coefficient supplied by a positive uniform gap from
an upper observation point to the spectral divisor. -/
def riemannXiUpperHyperbolicGapCoefficient (z : ℂ) (delta : ℝ) : ℝ :=
  1 + 2 * z.im / delta ^ 2

/-- A logarithmic lower bound normalized into a Poisson-mass lower bound. -/
def riemannXiUpperHyperbolicPoissonThreshold
    (D : ℝ) (z : ℂ) (delta : ℝ) : ℝ :=
  D / riemannXiUpperHyperbolicGapCoefficient z delta

/-- A logarithmic lower bound normalized further into an elementary Blaschke
derivative-variation lower bound. -/
def riemannXiUpperBlaschkeVariationThreshold
    (D : ℝ) (z : ℂ) (delta : ℝ) : ℝ :=
  D / (riemannXiUpperHyperbolicGapCoefficient z delta * (2 * z.im))

/-- A complete logarithmic-defect alternative transfers to explicit positive
Poisson and Blaschke-variation thresholds at any noncolliding upper point. -/
theorem exists_gap_poisson_blaschke_thresholds_or_height_unbounded
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0)
    {D : ℝ} (hD : 0 < D) (height : ℕ → ℝ)
    (halternative :
      ENNReal.ofReal D ≤ riemannXiUpperHyperbolicLogDefectMass z ∨
        ∀ M : ℝ, 0 ≤ M → ∃ᶠ n in atTop, M < height n) :
    ∃ delta : ℝ, 0 < delta ∧
      (∀ rho : NontrivialZetaZero,
        delta ≤ ‖z - zetaSpectralCoordinate rho.1‖) ∧
      0 < riemannXiUpperHyperbolicPoissonThreshold D z delta ∧
      0 < riemannXiUpperBlaschkeVariationThreshold D z delta ∧
      ((ENNReal.ofReal
            (riemannXiUpperHyperbolicPoissonThreshold D z delta) ≤
          riemannXiUpperHyperbolicPoissonDefectMass z ∧
        ENNReal.ofReal
            (riemannXiUpperBlaschkeVariationThreshold D z delta) ≤
          riemannXiUpperBlaschkeDerivativeVariationMass z) ∨
        ∀ M : ℝ, 0 ≤ M → ∃ᶠ n in atTop, M < height n) := by
  obtain ⟨delta, hdelta, hgap⟩ :=
    exists_uniform_zetaSpectralCoordinate_gap_of_ne_zero hxi
  let C : ℝ := riemannXiUpperHyperbolicGapCoefficient z delta
  have hC : 0 < C := by
    dsimp [C, riemannXiUpperHyperbolicGapCoefficient]
    positivity
  have htwoIm : 0 < 2 * z.im := by positivity
  have hCtwoIm : 0 < C * (2 * z.im) := mul_pos hC htwoIm
  have hpoissonThreshold :
      0 < riemannXiUpperHyperbolicPoissonThreshold D z delta := by
    rw [riemannXiUpperHyperbolicPoissonThreshold]
    change 0 < D / C
    exact div_pos hD hC
  have hvariationThreshold :
      0 < riemannXiUpperBlaschkeVariationThreshold D z delta := by
    rw [riemannXiUpperBlaschkeVariationThreshold]
    change 0 < D / (C * (2 * z.im))
    exact div_pos hD hCtwoIm
  refine ⟨delta, hdelta, hgap, hpoissonThreshold,
    hvariationThreshold, ?_⟩
  rcases halternative with hlog | hunbounded
  · left
    have hlogToPoisson :
        riemannXiUpperHyperbolicLogDefectMass z ≤
          ENNReal.ofReal C *
            riemannXiUpperHyperbolicPoissonDefectMass z := by
      simpa [C, riemannXiUpperHyperbolicGapCoefficient] using
        riemannXiUpperHyperbolicLogDefectMass_le_gapCoefficient_mul_poissonMass
          hz hdelta hgap
    have hraw :
        ENNReal.ofReal D ≤ ENNReal.ofReal C *
          riemannXiUpperHyperbolicPoissonDefectMass z :=
      hlog.trans hlogToPoisson
    have hCneZero : ENNReal.ofReal C ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr hC
    have hCneTop : ENNReal.ofReal C ≠ ⊤ := ENNReal.ofReal_ne_top
    have hpoisson :
        ENNReal.ofReal
            (riemannXiUpperHyperbolicPoissonThreshold D z delta) ≤
          riemannXiUpperHyperbolicPoissonDefectMass z := by
      rw [riemannXiUpperHyperbolicPoissonThreshold]
      change ENNReal.ofReal (D / C) ≤
        riemannXiUpperHyperbolicPoissonDefectMass z
      rw [ENNReal.ofReal_div_of_pos hC]
      exact (ENNReal.div_le_iff' hCneZero hCneTop).2 hraw
    have hvariationRaw :
        ENNReal.ofReal D ≤ ENNReal.ofReal (C * (2 * z.im)) *
          riemannXiUpperBlaschkeDerivativeVariationMass z := by
      calc
        ENNReal.ofReal D ≤ ENNReal.ofReal C *
            riemannXiUpperHyperbolicPoissonDefectMass z := hraw
        _ = ENNReal.ofReal C *
            (ENNReal.ofReal (2 * z.im) *
              riemannXiUpperBlaschkeDerivativeVariationMass z) := by
          rw [riemannXiUpperHyperbolicPoissonDefectMass_eq_two_im_mul_variationMass
            hz]
        _ = ENNReal.ofReal (C * (2 * z.im)) *
            riemannXiUpperBlaschkeDerivativeVariationMass z := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hC.le]
    have hCtwoImNeZero : ENNReal.ofReal (C * (2 * z.im)) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr hCtwoIm
    have hCtwoImNeTop : ENNReal.ofReal (C * (2 * z.im)) ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    have hvariation :
        ENNReal.ofReal
            (riemannXiUpperBlaschkeVariationThreshold D z delta) ≤
          riemannXiUpperBlaschkeDerivativeVariationMass z := by
      rw [riemannXiUpperBlaschkeVariationThreshold]
      change ENNReal.ofReal (D / (C * (2 * z.im))) ≤
        riemannXiUpperBlaschkeDerivativeVariationMass z
      rw [ENNReal.ofReal_div_of_pos hCtwoIm]
      exact
        (ENNReal.div_le_iff' hCtwoImNeZero hCtwoImNeTop).2 hvariationRaw
    exact ⟨hpoisson, hvariation⟩
  · exact Or.inr hunbounded

/-- Under failure of RH, the canonical finite Hardy frontier yields explicit
positive complete Poisson and Blaschke-variation thresholds, unless its finite
upper-height masses are unbounded along every nonnegative level. -/
theorem exists_canonicalFiniteHardyFrontier_poisson_blaschke_or_height_unbounded_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z : ℂ, 0 < z.im ∧
      riemannXiSpectral z ≠ 0 ∧ ∃ delta : ℝ, 0 < delta ∧
      (∀ rho : NontrivialZetaZero,
        delta ≤ ‖z - zetaSpectralCoordinate rho.1‖) ∧
      ∃ B : ℕ → ℝ[X],
        TendstoLocallyUniformlyOn
          (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
          riemannXiSpectral atTop Set.univ ∧
        (∀ n, CanonicalFiniteHardyFrontier (B n) eta z) ∧
        0 < -2 * Real.log (pairHyperbolicThreshold eta z.im) ∧
        (∀ (a error : ℝ), 0 < a → 0 < error →
          ∃ T : ℝ, a ≤ T ∧
            ∀ᶠ n in atTop,
              (-2 * Real.log (pairHyperbolicThreshold eta z.im) -
                  (∫ tau in a..T,
                    riemannXiUpperHyperbolicHeatSum z tau) - error) /
                    (4 * a * z.im) <
                realPolynomialUpperHeightMass (B n)) ∧
        0 < riemannXiUpperHyperbolicPoissonThreshold
          (-2 * Real.log (pairHyperbolicThreshold eta z.im)) z delta ∧
        0 < riemannXiUpperBlaschkeVariationThreshold
          (-2 * Real.log (pairHyperbolicThreshold eta z.im)) z delta ∧
        ((ENNReal.ofReal
              (riemannXiUpperHyperbolicPoissonThreshold
                (-2 * Real.log (pairHyperbolicThreshold eta z.im)) z delta) ≤
            riemannXiUpperHyperbolicPoissonDefectMass z ∧
          ENNReal.ofReal
              (riemannXiUpperBlaschkeVariationThreshold
                (-2 * Real.log (pairHyperbolicThreshold eta z.im)) z delta) ≤
            riemannXiUpperBlaschkeDerivativeVariationMass z) ∨
          ∀ M : ℝ, 0 ≤ M → ∃ᶠ n in atTop,
            M < realPolynomialUpperHeightMass (B n)) := by
  obtain ⟨eta, heta, z, hz, hxi, B, hlimit, hfrontier,
      hpositive, hobstruction, halternative⟩ :=
    exists_canonicalFiniteHardyFrontier_logDefect_or_height_unbounded_of_not_rh
      hRH
  obtain ⟨delta, hdelta, hgap, hpoissonPositive,
      hvariationPositive, htransferred⟩ :=
    exists_gap_poisson_blaschke_thresholds_or_height_unbounded
      hz hxi hpositive (fun n ↦ realPolynomialUpperHeightMass (B n))
        halternative
  exact ⟨eta, heta, z, hz, hxi, delta, hdelta, hgap, B,
    hlimit, hfrontier, hpositive, hobstruction, hpoissonPositive,
    hvariationPositive, htransferred⟩

end

end RiemannGaussian
