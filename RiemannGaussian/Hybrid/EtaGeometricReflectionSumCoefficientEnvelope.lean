import RiemannGaussian.Hybrid.EtaGeometricReflectionSumMetricModeBound

/-!
# Completion-coefficient envelope for upper eta correlations

The two-colour metric prefix matrix now has a simultaneous quantitative
entrywise bound.  This module contracts that information against the exact
cutoff-dependent completion coefficients, without replacing those
coefficients by constants or suppressing their reflected/original colours.

Lean first proves a finite triangle bound for the exact `2 × 2` coefficient
contraction.  It then divides the checked gap-times-entry estimates by their
strictly positive raw-mode gaps and obtains an explicit moving envelope for
the original unweighted upper--upper reflection-sum correlation.  The bound
holds eventually and simultaneously for every ordered pair in the complete
finite upper zero window.

This is a direct quantitative upper bound on the actual complex correlation
entering the certificate reserve.  Comparing its square with the checked atom
coercivity and aggregating the resulting reserves remain the next steps.
-/

open Complex Matrix Finset Filter Topology
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian

noncomputable section

/-- Positive phase-and-radius gap of one reflected/original colour pair. -/
def pairedEtaGeometricUpperRawRelativeModeGap
    (q : ℕ) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    (i j : Fin 2) : ℝ :=
  ‖star (etaGeometricDecayMode q
        (pairedEtaGeometricUpperReflectionPairZero zeta i).val) *
      etaGeometricDecayMode q
        (pairedEtaGeometricUpperReflectionPairZero rho j).val - 1‖

/-- Every colour-resolved raw relative-mode gap is strictly positive. -/
theorem pairedEtaGeometricUpperRawRelativeModeGap_pos
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    (i j : Fin 2) :
    0 < pairedEtaGeometricUpperRawRelativeModeGap q zeta rho i j := by
  exact pairedEtaGeometricUpperRawRelativeMode_gap_pos hq zeta rho i j

/-- Triangle envelope of the exact four-entry metric coefficient
contraction, before applying any arithmetic estimate to its matrix entries. -/
def pairedEtaGeometricCriticalUpperMetricCoefficientTriangleEnvelope
    (q : ℕ) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    (n M : ℕ) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2,
    ‖pairedEtaGeometricUpperCompletionCoefficientVector q zeta n i‖ *
      ‖pairedEtaGeometricUpperCompletionCoefficientVector q rho n j‖ *
        ‖pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix
          q zeta rho n M i j‖

/-- The norm of the exact metric coefficient contraction is bounded by its
fully colour-resolved four-term triangle envelope. -/
theorem norm_pairedEtaGeometricCriticalUpperMetricCoefficientContraction_le
    (q : ℕ) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    (n M : ℕ) :
    ‖pairedEtaGeometricCriticalUpperMetricCoefficientContraction
        q zeta rho n M‖ ≤
      pairedEtaGeometricCriticalUpperMetricCoefficientTriangleEnvelope
        q zeta rho n M := by
  unfold pairedEtaGeometricCriticalUpperMetricCoefficientContraction
    pairedEtaGeometricCriticalUpperMetricCoefficientTriangleEnvelope
  calc
    ‖∑ i : Fin 2, ∑ j : Fin 2,
        star (pairedEtaGeometricUpperCompletionCoefficientVector q zeta n i) *
          pairedEtaGeometricUpperCompletionCoefficientVector q rho n j *
            pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix
              q zeta rho n M i j‖ ≤
      ∑ i : Fin 2, ‖∑ j : Fin 2,
        star (pairedEtaGeometricUpperCompletionCoefficientVector q zeta n i) *
          pairedEtaGeometricUpperCompletionCoefficientVector q rho n j *
            pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix
              q zeta rho n M i j‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 2, ∑ j : Fin 2,
        ‖star (pairedEtaGeometricUpperCompletionCoefficientVector q zeta n i) *
          pairedEtaGeometricUpperCompletionCoefficientVector q rho n j *
            pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix
              q zeta rho n M i j‖ := by
      apply Finset.sum_le_sum
      intro i _hi
      exact norm_sum_le _ _
    _ = ∑ i : Fin 2, ∑ j : Fin 2,
        ‖pairedEtaGeometricUpperCompletionCoefficientVector q zeta n i‖ *
          ‖pairedEtaGeometricUpperCompletionCoefficientVector q rho n j‖ *
            ‖pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix
              q zeta rho n M i j‖ := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      rw [norm_mul, norm_mul, norm_star]

/-- Explicit coefficient-and-gap envelope obtained by substituting the
eventual constant-two matrix-entry bound with positive slack. -/
def pairedEtaGeometricUpperReflectionSumCorrelationGapEnvelope
    (q : ℕ) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    (n : ℕ) (ε : ℝ) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2,
    ‖pairedEtaGeometricUpperCompletionCoefficientVector q zeta n i‖ *
      ‖pairedEtaGeometricUpperCompletionCoefficientVector q rho n j‖ *
        ((2 + ε) /
          pairedEtaGeometricUpperRawRelativeModeGap q zeta rho i j)

/-- Once every metric entry satisfies its gap bound, the four-term triangle
envelope is bounded by the explicit completion-coefficient gap envelope. -/
theorem pairedEtaGeometricCriticalUpperMetricCoefficientTriangleEnvelope_le_gapEnvelope
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    (n M : ℕ) {ε : ℝ}
    (hentry : ∀ i j : Fin 2,
      ‖pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix
          q zeta rho n M i j‖ *
        pairedEtaGeometricUpperRawRelativeModeGap q zeta rho i j < 2 + ε) :
    pairedEtaGeometricCriticalUpperMetricCoefficientTriangleEnvelope
        q zeta rho n M ≤
      pairedEtaGeometricUpperReflectionSumCorrelationGapEnvelope
        q zeta rho n ε := by
  unfold pairedEtaGeometricCriticalUpperMetricCoefficientTriangleEnvelope
    pairedEtaGeometricUpperReflectionSumCorrelationGapEnvelope
  apply Finset.sum_le_sum
  intro i _hi
  apply Finset.sum_le_sum
  intro j _hj
  apply mul_le_mul_of_nonneg_left
  · exact le_of_lt ((lt_div_iff₀
      (pairedEtaGeometricUpperRawRelativeModeGap_pos hq zeta rho i j)).2
        (hentry i j))
  · exact mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- The original unweighted complex reflection-sum correlation is eventually
bounded by the explicit moving completion-coefficient gap envelope. -/
theorem eventually_spectralUpperZetaZeroWindow_geometricUpperReflectionSumCorrelation_norm_le_gapEnvelope
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) (T : ℝ)
    (M : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      ∀ zeta rho : ↥(spectralUpperZetaZeroWindow T),
        ‖pairedEtaGeometricUpperReflectionSumCorrelation
            q zeta rho n M‖ ≤
          pairedEtaGeometricUpperReflectionSumCorrelationGapEnvelope
            q zeta rho n ε := by
  have hmatrix :=
    eventually_spectralUpperZetaZeroWindow_geometricCriticalMetricPrefixCorrelationMatrix_mul_gap_lt
      hqOdd hq T M hε
  filter_upwards [hmatrix, eventually_ge_atTop (1 : ℕ)] with n hmatrixN hn
  intro zeta rho
  rw [pairedEtaGeometricUpperReflectionSumCorrelation_eq_metricCoefficientContraction
    hqOdd hq zeta rho hn M]
  exact
    (norm_pairedEtaGeometricCriticalUpperMetricCoefficientContraction_le
      q zeta rho n M).trans
    (pairedEtaGeometricCriticalUpperMetricCoefficientTriangleEnvelope_le_gapEnvelope
      hq zeta rho n M (hmatrixN zeta rho))

/-- The real packed upper--upper frame correlation inherits the same explicit
moving envelope. -/
theorem eventually_spectralUpperZetaZeroWindow_geometricFrameCorrelation_upper_upper_abs_le_gapEnvelope
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) (T : ℝ)
    (M : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      ∀ zeta rho : ↥(spectralUpperZetaZeroWindow T),
        |(star (pairedEtaReflectionEvenFrameVector
            (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
            T (Sum.inr zeta)) ⬝ᵥ
          pairedEtaReflectionEvenFrameVector
            (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
            T (Sum.inr rho)).re| ≤
          pairedEtaGeometricUpperReflectionSumCorrelationGapEnvelope
            q zeta rho n ε := by
  have hcorr :=
    eventually_spectralUpperZetaZeroWindow_geometricUpperReflectionSumCorrelation_norm_le_gapEnvelope
      hqOdd hq T M hε
  filter_upwards [hcorr] with n hcorrN
  intro zeta rho
  rw [pairedEtaReflectionEvenFrameCorrelation_upper_upper_eq_re]
  exact (Complex.abs_re_le_norm
    (pairedEtaGeometricUpperReflectionSumCorrelation
      q zeta rho n M)).trans (hcorrN zeta rho)

end

end RiemannGaussian
