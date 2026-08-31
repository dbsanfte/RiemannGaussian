import RiemannGaussian.Hybrid.EtaGeometricReflectionSumCorrelationLedger

/-!
# Metric correlation matrix for completed eta reflection sums

The common critical coordinate tilt is useful because every completed upper
reflection sum becomes a two-column combination of normalized literal eta
prefixes.  The tilt is not unitary, however, so ordinary correlations in the
tilted coordinates are not the correlations used by the certificate.

This module retains the missing metric exactly.  For any nonvanishing finite
diagonal weight, Lean defines its inverse squared-modulus metric and proves
that metric correlation after weighting is exactly the original Hermitian
correlation.  It then applies this identity to the critical eta tilt.

Each upper atom is indexed by its two zero/reflection colours.  Their four
metric prefix correlations form a literal `2 × 2` matrix, while the exact
completion coefficients form two colour vectors.  Lean proves that the
original unweighted upper--upper correlation is exactly the corresponding
coefficient contraction of this matrix.  Finally every matrix entry is shown
to converge to the matching metric correlation of the explicit shifted
geometric modes.  Thus neither the tilt metric, complex phase, completion
coefficients, nor reflection colour is discarded at the correlation frontier.

This is an exact representation and finite-dimensional convergence theorem;
it does not supply the still-open quantitative aggregate estimate.
-/

open Complex Matrix Finset Filter Topology
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian

noncomputable section

/-- Hermitian correlation after applying a fixed diagonal metric to the first
finite complex vector. -/
def finiteComplexDiagonalMetricCorrelation
    {m : Type*} [Fintype m] (metric v w : m → ℂ) : ℂ :=
  star w ⬝ᵥ finiteComplexPointwiseWeightedVector metric v

/-- Inverse squared-modulus metric associated with a diagonal coordinate
weight. -/
def finiteComplexDiagonalWeightRecoveryMetric
    {m : Type*} (weight : m → ℂ) : m → ℂ := fun j ↦
  (star (weight j) * weight j)⁻¹

/-- A nonvanishing diagonal weighting is exactly undone inside its recovery
metric correlation. -/
theorem finiteComplexDiagonalMetricCorrelation_weighted_recover
    {m : Type*} [Fintype m] (weight v w : m → ℂ)
    (hweight : ∀ j, weight j ≠ 0) :
    finiteComplexDiagonalMetricCorrelation
        (finiteComplexDiagonalWeightRecoveryMetric weight)
        (finiteComplexPointwiseWeightedVector weight v)
        (finiteComplexPointwiseWeightedVector weight w) =
      star w ⬝ᵥ v := by
  unfold finiteComplexDiagonalMetricCorrelation
    finiteComplexDiagonalWeightRecoveryMetric
    finiteComplexPointwiseWeightedVector dotProduct
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [Pi.star_apply]
  field_simp [hweight j, star_ne_zero.mpr (hweight j)]
  rw [star_mul]
  ring

/-- Metric correlation is sesquilinear on two explicit channel sums, with
all four coefficient phases retained. -/
theorem finiteComplexDiagonalMetricCorrelation_twoChannel_eq
    {m : Type*} [Fintype m] (metric : m → ℂ)
    (v₀ v₁ w₀ w₁ : m → ℂ) (c₀ c₁ d₀ d₁ : ℂ) :
    finiteComplexDiagonalMetricCorrelation metric
        (c₀ • v₀ + c₁ • v₁) (d₀ • w₀ + d₁ • w₁) =
      star d₀ * c₀ * finiteComplexDiagonalMetricCorrelation metric v₀ w₀ +
        star d₀ * c₁ * finiteComplexDiagonalMetricCorrelation metric v₁ w₀ +
        star d₁ * c₀ * finiteComplexDiagonalMetricCorrelation metric v₀ w₁ +
        star d₁ * c₁ * finiteComplexDiagonalMetricCorrelation metric v₁ w₁ := by
  have hstar :
      star (d₀ • w₀ + d₁ • w₁) =
        star d₀ • star w₀ + star d₁ • star w₁ := by
    ext j
    simp [Pi.star_apply]
  have hmetric :
      finiteComplexPointwiseWeightedVector metric (c₀ • v₀ + c₁ • v₁) =
        c₀ • finiteComplexPointwiseWeightedVector metric v₀ +
          c₁ • finiteComplexPointwiseWeightedVector metric v₁ := by
    ext j
    simp [finiteComplexPointwiseWeightedVector]
    ring
  unfold finiteComplexDiagonalMetricCorrelation
  rw [hstar, hmetric]
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul]
  ring

/-- Every coordinate of a critical eta tilt is nonzero at a positive base. -/
theorem etaGeometricCriticalCoordinateTilt_ne_zero
    {q M : ℕ} (hq : 0 < q) (j : Fin M) :
    etaGeometricCriticalCoordinateTilt q M j ≠ 0 := by
  unfold etaGeometricCriticalCoordinateTilt
  apply pow_ne_zero
  apply Complex.cpow_ne_zero_iff.mpr
  left
  exact_mod_cast hq.ne'

/-- Exact recovery metric for the common critical coordinate tilt. -/
def etaGeometricCriticalCoordinateRecoveryMetric
    (q M : ℕ) : Fin M → ℂ :=
  finiteComplexDiagonalWeightRecoveryMetric
    (etaGeometricCriticalCoordinateTilt q M)

/-- Correlation in the original recovered upper channels is exactly critical
tilt correlation with the explicit recovery metric inserted. -/
theorem pairedEtaGeometricUpperReflectionSumCorrelation_eq_criticalTiltedMetric
    {q : ℕ} (hq : 0 < q) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    (n M : ℕ) :
    pairedEtaGeometricUpperReflectionSumCorrelation q zeta rho n M =
      finiteComplexDiagonalMetricCorrelation
        (etaGeometricCriticalCoordinateRecoveryMetric q M)
        (pairedEtaGeometricCriticalTiltedUpperFrameRecoveredVector
          q T rho n M)
        (pairedEtaGeometricCriticalTiltedUpperFrameRecoveredVector
          q T zeta n M) := by
  rw [pairedEtaGeometricCriticalTiltedUpperFrameRecoveredVector_eq_pointwiseWeighted,
    pairedEtaGeometricCriticalTiltedUpperFrameRecoveredVector_eq_pointwiseWeighted]
  exact (finiteComplexDiagonalMetricCorrelation_weighted_recover
    (etaGeometricCriticalCoordinateTilt q M)
    (pairedEtaGeometricUpperFrameRecoveredVector q T rho n M)
    (pairedEtaGeometricUpperFrameRecoveredVector q T zeta n M)
    (etaGeometricCriticalCoordinateTilt_ne_zero hq)).symm

/-- The two zero colours of an upper reflection pair: reflected first,
original second. -/
def pairedEtaGeometricUpperReflectionPairZero
    {T : ℝ} (rho : ↥(spectralUpperZetaZeroWindow T)) :
    Fin 2 → NontrivialZetaZero :=
  ![NontrivialZetaZero.conjugatePartner rho.1, rho.1]

/-- Exact two-colour completion coefficients of an upper reflection pair. -/
def pairedEtaGeometricUpperCompletionCoefficientVector
    (q : ℕ) {T : ℝ} (rho : ↥(spectralUpperZetaZeroWindow T))
    (n : ℕ) : Fin 2 → ℂ := fun i ↦
  pairedEtaGeometricCompletedPrefixCoefficient q
    (pairedEtaGeometricUpperReflectionPairZero rho i) n

/-- Two normalized literal eta-prefix columns belonging to an upper
reflection pair at the critical tilt. -/
def pairedEtaGeometricCriticalUpperNormalizedPrefixFamily
    (q : ℕ) {T : ℝ} (rho : ↥(spectralUpperZetaZeroWindow T))
    (n M : ℕ) : Fin 2 → Fin M → ℂ := fun i ↦
  pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector q (1 / 2)
    (pairedEtaGeometricUpperReflectionPairZero rho i) n M

/-- The actual critically tilted recovered channel is the synthesis of its
two normalized prefix colours with the exact moving completion coefficients. -/
theorem pairedEtaGeometricCriticalTiltedUpperFrameRecoveredVector_eq_colourSynthesis
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {T : ℝ}
    (rho : ↥(spectralUpperZetaZeroWindow T))
    {n : ℕ} (hn : 1 ≤ n) (M : ℕ) :
    pairedEtaGeometricCriticalTiltedUpperFrameRecoveredVector q T rho n M =
      ∑ i : Fin 2,
        pairedEtaGeometricUpperCompletionCoefficientVector q rho n i •
          pairedEtaGeometricCriticalUpperNormalizedPrefixFamily
            q rho n M i := by
  rw [Fin.sum_univ_two]
  exact spectralUpperZetaZeroWindow_geometricCriticalTiltedFrame_eq_completedPrefixCombination
    hqOdd hq rho hn M

/-- The `2 × 2` matrix of metric correlations between normalized prefix
colours of two upper reflection pairs. -/
def pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix
    (q : ℕ) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    (n M : ℕ) : Matrix (Fin 2) (Fin 2) ℂ := fun i j ↦
  finiteComplexDiagonalMetricCorrelation
    (etaGeometricCriticalCoordinateRecoveryMetric q M)
    (pairedEtaGeometricCriticalUpperNormalizedPrefixFamily q rho n M j)
    (pairedEtaGeometricCriticalUpperNormalizedPrefixFamily q zeta n M i)

/-- Coefficient contraction of the four-colour metric prefix-correlation
matrix. -/
def pairedEtaGeometricCriticalUpperMetricCoefficientContraction
    (q : ℕ) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    (n M : ℕ) : ℂ :=
  ∑ i : Fin 2, ∑ j : Fin 2,
    star (pairedEtaGeometricUpperCompletionCoefficientVector q zeta n i) *
      pairedEtaGeometricUpperCompletionCoefficientVector q rho n j *
        pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix
          q zeta rho n M i j

/-- The original unweighted upper reflection-sum correlation is exactly the
completion-coefficient contraction of the four metric prefix correlations. -/
theorem pairedEtaGeometricUpperReflectionSumCorrelation_eq_metricCoefficientContraction
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    {n : ℕ} (hn : 1 ≤ n) (M : ℕ) :
    pairedEtaGeometricUpperReflectionSumCorrelation q zeta rho n M =
      pairedEtaGeometricCriticalUpperMetricCoefficientContraction
        q zeta rho n M := by
  rw [pairedEtaGeometricUpperReflectionSumCorrelation_eq_criticalTiltedMetric
      hq.le,
    pairedEtaGeometricCriticalTiltedUpperFrameRecoveredVector_eq_colourSynthesis
      hqOdd hq rho hn M,
    pairedEtaGeometricCriticalTiltedUpperFrameRecoveredVector_eq_colourSynthesis
      hqOdd hq zeta hn M]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  rw [finiteComplexDiagonalMetricCorrelation_twoChannel_eq]
  unfold pairedEtaGeometricCriticalUpperMetricCoefficientContraction
  rw [Fin.sum_univ_two]
  unfold pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  ring

/-- Full Hermitian Gram reserve written solely in terms of the three metric
coefficient contractions for two upper atoms. -/
def pairedEtaGeometricCriticalUpperMetricCoefficientGramReserve
    (q : ℕ) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    (n M : ℕ) : ℝ :=
  (pairedEtaGeometricCriticalUpperMetricCoefficientContraction
      q rho rho n M).re *
      (pairedEtaGeometricCriticalUpperMetricCoefficientContraction
        q zeta zeta n M).re -
    ‖pairedEtaGeometricCriticalUpperMetricCoefficientContraction
      q zeta rho n M‖ ^ 2

/-- The coefficient-contraction Gram reserve is exactly the Hermitian Gram
reserve of the original recovered complex reflection sums. -/
theorem pairedEtaGeometricCriticalUpperMetricCoefficientGramReserve_eq_hermitian
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    {n : ℕ} (hn : 1 ≤ n) (M : ℕ) :
    pairedEtaGeometricCriticalUpperMetricCoefficientGramReserve
        q zeta rho n M =
      finiteComplexVectorHermitianGramReserve
        (pairedEtaGeometricUpperFrameRecoveredVector q T rho n M)
        (pairedEtaGeometricUpperFrameRecoveredVector q T zeta n M) := by
  have hcross :=
    pairedEtaGeometricUpperReflectionSumCorrelation_eq_metricCoefficientContraction
      hqOdd hq zeta rho hn M
  have hselfRho :=
    pairedEtaGeometricUpperReflectionSumCorrelation_eq_metricCoefficientContraction
      hqOdd hq rho rho hn M
  have hselfZeta :=
    pairedEtaGeometricUpperReflectionSumCorrelation_eq_metricCoefficientContraction
      hqOdd hq zeta zeta hn M
  unfold pairedEtaGeometricCriticalUpperMetricCoefficientGramReserve
    finiteComplexVectorHermitianGramReserve
  rw [← hselfRho, ← hselfZeta, ← hcross]
  unfold pairedEtaGeometricUpperReflectionSumCorrelation
  rw [star_dot_self_eq_finiteComplexVectorNormSq,
    star_dot_self_eq_finiteComplexVectorNormSq]
  simp

/-- The metric coefficient-contraction Gram reserve is nonnegative because
it is an exact coordinate representation of a Hermitian Gram determinant. -/
theorem pairedEtaGeometricCriticalUpperMetricCoefficientGramReserve_nonneg
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    {n : ℕ} (hn : 1 ≤ n) (M : ℕ) :
    0 ≤ pairedEtaGeometricCriticalUpperMetricCoefficientGramReserve
      q zeta rho n M := by
  rw [pairedEtaGeometricCriticalUpperMetricCoefficientGramReserve_eq_hermitian
    hqOdd hq zeta rho hn M]
  exact finiteComplexVectorHermitianGramReserve_nonneg _ _

/-- The actual multiplicity-weighted upper-pair certificate summand is an
exact positive weight times the metric coefficient Gram reserve plus the
square of the contraction's imaginary part. -/
theorem pairedEtaGeometricUpperPairWeightedDecorrelationReserve_eq_metricContractionLedger
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    {n : ℕ} (hn : 1 ≤ n) (M : ℕ) :
    pairedEtaGeometricUpperPairWeightedDecorrelationReserve
        q zeta rho n M =
      pairedEtaReflectionEvenFrameWeight T (Sum.inr rho) *
        pairedEtaReflectionEvenFrameWeight T (Sum.inr zeta) *
          (pairedEtaGeometricCriticalUpperMetricCoefficientGramReserve
              q zeta rho n M +
            (pairedEtaGeometricCriticalUpperMetricCoefficientContraction
              q zeta rho n M).im ^ 2) := by
  rw [pairedEtaGeometricUpperPairWeightedDecorrelationReserve_eq,
    ← pairedEtaGeometricCriticalUpperMetricCoefficientGramReserve_eq_hermitian
      hqOdd hq zeta rho hn M,
    pairedEtaGeometricUpperReflectionSumCorrelation_eq_metricCoefficientContraction
      hqOdd hq zeta rho hn M]

/-- Shifted geometric-mode family retaining both colours of an upper
reflection pair. -/
def pairedEtaGeometricCriticalUpperShiftedModeFamily
    (q : ℕ) {T : ℝ} (rho : ↥(spectralUpperZetaZeroWindow T))
    (M : ℕ) : Fin 2 → Fin M → ℂ := fun i ↦
  finiteGeometricPhaseVector M
    (etaGeometricShiftedMode q (1 / 2)
      (pairedEtaGeometricUpperReflectionPairZero rho i).val)

/-- Limiting `2 × 2` recovery-metric correlation matrix of the explicit
shifted geometric modes. -/
def pairedEtaGeometricCriticalUpperMetricModeCorrelationMatrix
    (q : ℕ) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    (M : ℕ) : Matrix (Fin 2) (Fin 2) ℂ := fun i j ↦
  finiteComplexDiagonalMetricCorrelation
    (etaGeometricCriticalCoordinateRecoveryMetric q M)
    (pairedEtaGeometricCriticalUpperShiftedModeFamily q rho M j)
    (pairedEtaGeometricCriticalUpperShiftedModeFamily q zeta M i)

/-- Every colour entry of the literal metric prefix matrix converges to the
matching explicit shifted-mode metric correlation. -/
theorem tendsto_pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    (M : ℕ) :
    Tendsto (fun n : ℕ ↦
      pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix
        q zeta rho n M) atTop
      (nhds (pairedEtaGeometricCriticalUpperMetricModeCorrelationMatrix
        q zeta rho M)) := by
  change Tendsto
    (fun n i j ↦
      pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix
        q zeta rho n M i j) atTop
    (nhds (fun i j ↦
      pairedEtaGeometricCriticalUpperMetricModeCorrelationMatrix
        q zeta rho M i j))
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  unfold pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix
    pairedEtaGeometricCriticalUpperMetricModeCorrelationMatrix
    finiteComplexDiagonalMetricCorrelation dotProduct
  apply tendsto_finsetSum
  intro k _hk
  exact
    (tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector_apply_shifted
      hqOdd hq (1 / 2)
      (pairedEtaGeometricUpperReflectionPairZero zeta i) M k).star.mul
    (Filter.Tendsto.const_mul
      (etaGeometricCriticalCoordinateRecoveryMetric q M k)
      (tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector_apply_shifted
        hqOdd hq (1 / 2)
        (pairedEtaGeometricUpperReflectionPairZero rho j) M k))

/-- Consequently the literal packed upper--upper frame correlation is the
real part of the exact metric matrix contraction, with all colours and
completion coefficients retained. -/
theorem pairedEtaReflectionEvenFrameCorrelation_upper_upper_eq_metricCoefficientContraction_re
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    {n : ℕ} (hn : 1 ≤ n) (M : ℕ) :
    star (pairedEtaReflectionEvenFrameVector
        (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
        T (Sum.inr zeta)) ⬝ᵥ
      pairedEtaReflectionEvenFrameVector
        (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
        T (Sum.inr rho) =
      ((pairedEtaGeometricCriticalUpperMetricCoefficientContraction
        q zeta rho n M).re : ℂ) := by
  rw [pairedEtaReflectionEvenFrameCorrelation_upper_upper_eq_re,
    pairedEtaGeometricUpperReflectionSumCorrelation_eq_metricCoefficientContraction
      hqOdd hq zeta rho hn M]

end

end RiemannGaussian
