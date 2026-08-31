import RiemannGaussian.Hybrid.EtaGeometricReflectionSignedAggregateTwoScale

/-!
# Cutoff-independent recovery of the signed eta colour carrier

The adjacent-start tomography initially recovers the bare normalized-prefix
metric by inverting the complete moving coefficient matrix.  That identity is
exact, but its inverse still contains the completion coefficients whose radial
ratio degenerates along late geometric blocks.

This module factors the moving matrix as `Dₙ V`.  The diagonal matrix `Dₙ`
contains every moving completion coefficient, whereas `V` contains only the
two exact one-step modes.  Those modes are distinct for every `q > 1`, so `V`
is nonsingular and independent of the cutoff start.  The same four probes can
therefore be inverted using only `V`, recovering `Dζᴴ K Dρ`.  Its four entries
are precisely the literal coefficient-weighted signed-colour interactions
used by the eta reserve.

Lean transports this recovered matrix through the full ordered sixteen-colour
interaction, pair reserve, upper-window sum, universal scale removal, and the
existing eventual certificate interface.  Thus the scale-free frontier is
expressed entirely through a cutoff-independent two-start inverse without
discarding phase, sign, or colour.  No conditioning bound on the fixed step
matrix, arithmetic threshold inequality, `13/18` improvement, or `18/18`
conclusion is proved here.
-/

open Complex Matrix Finset Filter Topology
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian

noncomputable section

/-- The cutoff-independent matrix whose rows are reflection colours and whose
columns are the zeroth and first powers of their exact step modes. -/
def pairedEtaGeometricUpperTwoStartStepMatrix
    (q : ℕ) {T : ℝ} (rho : ↑(spectralUpperZetaZeroWindow T)) :
    Matrix (Fin 2) (Fin 2) ℂ := fun i k ↦
  pairedEtaGeometricUpperCoefficientStepMode q rho i ^ (k : ℕ)

/-- The determinant of the two-start step matrix is exactly the difference of
the original and reflected step modes. -/
theorem det_pairedEtaGeometricUpperTwoStartStepMatrix
    (q : ℕ) {T : ℝ} (rho : ↑(spectralUpperZetaZeroWindow T)) :
    (pairedEtaGeometricUpperTwoStartStepMatrix q rho).det =
      pairedEtaGeometricUpperCoefficientStepMode q rho 1 -
        pairedEtaGeometricUpperCoefficientStepMode q rho 0 := by
  rw [Matrix.det_fin_two]
  unfold pairedEtaGeometricUpperTwoStartStepMatrix
  simp only [Fin.isValue, Fin.val_zero, pow_zero, Fin.val_one, pow_one,
    one_mul]
  ring

/-- The cutoff-independent step matrix is nonsingular for every `q > 1`. -/
theorem det_pairedEtaGeometricUpperTwoStartStepMatrix_ne_zero
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (rho : ↑(spectralUpperZetaZeroWindow T)) :
    (pairedEtaGeometricUpperTwoStartStepMatrix q rho).det ≠ 0 := by
  rw [det_pairedEtaGeometricUpperTwoStartStepMatrix]
  exact sub_ne_zero.mpr
    (pairedEtaGeometricUpperCoefficientStepMode_ne hq rho).symm

/-- Diagonal matrix containing the two moving completion coefficients at one
geometric block start. -/
def pairedEtaGeometricUpperStartCoefficientDiagonal
    (q : ℕ) {T : ℝ} (rho : ↑(spectralUpperZetaZeroWindow T))
    (n : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal
    (pairedEtaGeometricUpperCompletionCoefficientVector q rho n)

/-- The moving adjacent-start coefficient matrix factors exactly into its
cutoff-dependent coefficient diagonal and cutoff-independent step matrix. -/
theorem pairedEtaGeometricUpperTwoStartColourCoefficientMatrix_eq_diagonal_mul_step
    (q : ℕ) {T : ℝ} (rho : ↑(spectralUpperZetaZeroWindow T))
    (n : ℕ) :
    pairedEtaGeometricUpperTwoStartColourCoefficientMatrix q rho n =
      pairedEtaGeometricUpperStartCoefficientDiagonal q rho n *
        pairedEtaGeometricUpperTwoStartStepMatrix q rho := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [pairedEtaGeometricUpperTwoStartColourCoefficientMatrix,
      pairedEtaGeometricUpperStartCoefficientDiagonal,
      pairedEtaGeometricUpperTwoStartStepMatrix, Matrix.mul_apply,
      pairedEtaGeometricUpperCompletionCoefficientVector_succ]

/-- The literal prefix metric with its left and right moving completion
coefficients retained entrywise. -/
def pairedEtaGeometricCriticalUpperCoefficientWeightedPrefixMetric
    (q : ℕ) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (pairedEtaGeometricUpperStartCoefficientDiagonal q zeta n)ᴴ *
    pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix
      q zeta rho n M *
    pairedEtaGeometricUpperStartCoefficientDiagonal q rho n

/-- Every entry of the coefficient-weighted metric is the corresponding
literal complex signed-colour interaction before taking its real part. -/
theorem pairedEtaGeometricCriticalUpperCoefficientWeightedPrefixMetric_apply
    (q : ℕ) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) (i j : Fin 2) :
    pairedEtaGeometricCriticalUpperCoefficientWeightedPrefixMetric
        q zeta rho n M i j =
      star (pairedEtaGeometricUpperCompletionCoefficientVector q zeta n i) *
        pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix
          q zeta rho n M i j *
        pairedEtaGeometricUpperCompletionCoefficientVector q rho n j := by
  unfold pairedEtaGeometricCriticalUpperCoefficientWeightedPrefixMetric
    pairedEtaGeometricUpperStartCoefficientDiagonal
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

/-- The four adjacent-start probes factor through the coefficient-weighted
metric and the two cutoff-independent step matrices. -/
theorem pairedEtaGeometricCriticalUpperTwoStartMetricPrefixObservation_eq_step
    (q : ℕ) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) :
    pairedEtaGeometricCriticalUpperTwoStartMetricPrefixObservation
        q zeta rho n M =
      (pairedEtaGeometricUpperTwoStartStepMatrix q zeta)ᴴ *
        pairedEtaGeometricCriticalUpperCoefficientWeightedPrefixMetric
          q zeta rho n M *
        pairedEtaGeometricUpperTwoStartStepMatrix q rho := by
  unfold pairedEtaGeometricCriticalUpperTwoStartMetricPrefixObservation
    pairedEtaGeometricUpperTwoStartMetricObservation
    pairedEtaGeometricCriticalUpperCoefficientWeightedPrefixMetric
  rw [pairedEtaGeometricUpperTwoStartColourCoefficientMatrix_eq_diagonal_mul_step,
    pairedEtaGeometricUpperTwoStartColourCoefficientMatrix_eq_diagonal_mul_step,
    Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- The weighted colour metric reconstructed from four probes using only the
cutoff-independent step matrices. -/
def pairedEtaGeometricCriticalUpperTwoStartRecoveredWeightedPrefixMetric
    (q : ℕ) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((pairedEtaGeometricUpperTwoStartStepMatrix q zeta)ᴴ)⁻¹ *
    pairedEtaGeometricCriticalUpperTwoStartMetricPrefixObservation
      q zeta rho n M *
    (pairedEtaGeometricUpperTwoStartStepMatrix q rho)⁻¹

/-- Cutoff-independent two-sided inversion recovers the literal
coefficient-weighted prefix metric exactly. -/
theorem pairedEtaGeometricCriticalUpperTwoStartRecoveredWeightedPrefixMetric_eq
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) :
    pairedEtaGeometricCriticalUpperTwoStartRecoveredWeightedPrefixMetric
        q zeta rho n M =
      pairedEtaGeometricCriticalUpperCoefficientWeightedPrefixMetric
        q zeta rho n M := by
  let L := (pairedEtaGeometricUpperTwoStartStepMatrix q zeta)ᴴ
  let R := pairedEtaGeometricUpperTwoStartStepMatrix q rho
  have hLdet : L.det ≠ 0 := by
    unfold L
    rw [Matrix.det_conjTranspose]
    exact star_ne_zero.mpr
      (det_pairedEtaGeometricUpperTwoStartStepMatrix_ne_zero hq zeta)
  have hRdet : R.det ≠ 0 := by
    unfold R
    exact det_pairedEtaGeometricUpperTwoStartStepMatrix_ne_zero hq rho
  let _ : Invertible L :=
    Matrix.invertibleOfIsUnitDet L (isUnit_iff_ne_zero.mpr hLdet)
  let _ : Invertible R :=
    Matrix.invertibleOfIsUnitDet R (isUnit_iff_ne_zero.mpr hRdet)
  unfold pairedEtaGeometricCriticalUpperTwoStartRecoveredWeightedPrefixMetric
  rw [pairedEtaGeometricCriticalUpperTwoStartMetricPrefixObservation_eq_step]
  change L⁻¹ * (L * _ * R) * R⁻¹ = _
  rw [Matrix.mul_assoc L _ R,
    ← Matrix.mul_assoc L⁻¹ L (_ * R), Matrix.inv_mul_of_invertible,
    Matrix.one_mul, Matrix.mul_assoc _ R R⁻¹,
    Matrix.mul_inv_of_invertible, Matrix.mul_one]

/-- The real part of each recovered entry is exactly the existing signed eta
colour contribution. -/
theorem pairedEtaGeometricCriticalUpperTwoStartRecoveredWeightedPrefixMetric_apply_re
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) (i j : Fin 2) :
    (pairedEtaGeometricCriticalUpperTwoStartRecoveredWeightedPrefixMetric
        q zeta rho n M i j).re =
      pairedEtaGeometricCriticalUpperMetricColourContribution
        q zeta rho n M i j := by
  rw [pairedEtaGeometricCriticalUpperTwoStartRecoveredWeightedPrefixMetric_eq
    hq,
    pairedEtaGeometricCriticalUpperCoefficientWeightedPrefixMetric_apply]
  unfold pairedEtaGeometricCriticalUpperMetricColourContribution
  congr 1
  ring

/-- Sum of all four entries of the recovered coefficient-weighted colour
metric. -/
def pairedEtaGeometricCriticalUpperTwoStartRecoveredCoefficientContraction
    (q : ℕ) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) : ℂ :=
  ∑ i : Fin 2, ∑ j : Fin 2,
    pairedEtaGeometricCriticalUpperTwoStartRecoveredWeightedPrefixMetric
      q zeta rho n M i j

/-- Summing the recovered entries gives exactly the original literal metric
coefficient contraction. -/
theorem pairedEtaGeometricCriticalUpperTwoStartRecoveredCoefficientContraction_eq
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) :
    pairedEtaGeometricCriticalUpperTwoStartRecoveredCoefficientContraction
        q zeta rho n M =
      pairedEtaGeometricCriticalUpperMetricCoefficientContraction
        q zeta rho n M := by
  unfold pairedEtaGeometricCriticalUpperTwoStartRecoveredCoefficientContraction
    pairedEtaGeometricCriticalUpperMetricCoefficientContraction
  rw [pairedEtaGeometricCriticalUpperTwoStartRecoveredWeightedPrefixMetric_eq
    hq]
  simp_rw [pairedEtaGeometricCriticalUpperCoefficientWeightedPrefixMetric_apply]
  simp only [Fin.sum_univ_two]
  ring

/-- One real signed-colour contribution read from the cutoff-independently
recovered weighted metric. -/
def pairedEtaGeometricCriticalUpperTwoStartRecoveredColourContribution
    (q : ℕ) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) (i j : Fin 2) : ℝ :=
  (pairedEtaGeometricCriticalUpperTwoStartRecoveredWeightedPrefixMetric
    q zeta rho n M i j).re

/-- Every recovered real colour contribution equals its original literal
signed-colour contribution. -/
theorem pairedEtaGeometricCriticalUpperTwoStartRecoveredColourContribution_eq
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) (i j : Fin 2) :
    pairedEtaGeometricCriticalUpperTwoStartRecoveredColourContribution
        q zeta rho n M i j =
      pairedEtaGeometricCriticalUpperMetricColourContribution
        q zeta rho n M i j := by
  unfold pairedEtaGeometricCriticalUpperTwoStartRecoveredColourContribution
  exact
    pairedEtaGeometricCriticalUpperTwoStartRecoveredWeightedPrefixMetric_apply_re
      hq zeta rho n M i j

/-- All sixteen ordered products of the four recovered signed-colour
contributions. -/
def pairedEtaGeometricCriticalUpperTwoStartRecoveredOrderedColourInteraction
    (q : ℕ) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, ∑ l : Fin 2,
    pairedEtaGeometricCriticalUpperTwoStartRecoveredColourContribution
        q zeta rho n M i j *
      pairedEtaGeometricCriticalUpperTwoStartRecoveredColourContribution
        q zeta rho n M k l

/-- The recovered sixteen-colour interaction is exactly the existing literal
signed interaction. -/
theorem pairedEtaGeometricCriticalUpperTwoStartRecoveredOrderedColourInteraction_eq
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) :
    pairedEtaGeometricCriticalUpperTwoStartRecoveredOrderedColourInteraction
        q zeta rho n M =
      pairedEtaGeometricCriticalUpperMetricOrderedColourInteraction
        q zeta rho n M := by
  unfold
    pairedEtaGeometricCriticalUpperTwoStartRecoveredOrderedColourInteraction
    pairedEtaGeometricCriticalUpperMetricOrderedColourInteraction
  simp_rw [pairedEtaGeometricCriticalUpperTwoStartRecoveredColourContribution_eq
    hq]

/-- The multiplicity-weighted signed pair reserve computed entirely from the
cutoff-independently recovered two-start colour matrices. -/
def pairedEtaGeometricUpperPairTwoStartRecoveredSignedMetricReserve
    (q : ℕ) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) : ℝ :=
  pairedEtaReflectionEvenFrameWeight T (Sum.inr rho) *
    pairedEtaReflectionEvenFrameWeight T (Sum.inr zeta) *
      ((pairedEtaGeometricCriticalUpperTwoStartRecoveredCoefficientContraction
          q rho rho n M).re *
        (pairedEtaGeometricCriticalUpperTwoStartRecoveredCoefficientContraction
          q zeta zeta n M).re -
        pairedEtaGeometricCriticalUpperTwoStartRecoveredOrderedColourInteraction
          q zeta rho n M)

/-- The recovered two-start pair reserve is exactly the literal signed eta
pair reserve. -/
theorem pairedEtaGeometricUpperPairTwoStartRecoveredSignedMetricReserve_eq
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) :
    pairedEtaGeometricUpperPairTwoStartRecoveredSignedMetricReserve
        q zeta rho n M =
      pairedEtaGeometricUpperPairSignedMetricReserve q zeta rho n M := by
  unfold pairedEtaGeometricUpperPairTwoStartRecoveredSignedMetricReserve
    pairedEtaGeometricUpperPairSignedMetricReserve
  rw [pairedEtaGeometricCriticalUpperTwoStartRecoveredCoefficientContraction_eq
      hq,
    pairedEtaGeometricCriticalUpperTwoStartRecoveredCoefficientContraction_eq
      hq,
    pairedEtaGeometricCriticalUpperTwoStartRecoveredOrderedColourInteraction_eq
      hq]

/-- Complete ordered-distinct upper-window signed reserve reconstructed from
the cutoff-independent two-start inverses. -/
def pairedEtaGeometricUpperWindowTwoStartRecoveredSignedMetricReserve
    (q : ℕ) (T : ℝ) (n M : ℕ) : ℝ :=
  ∑ rho : ↑(spectralUpperZetaZeroWindow T),
    ∑ zeta ∈ (Finset.univ :
        Finset ↑(spectralUpperZetaZeroWindow T)).erase rho,
      pairedEtaGeometricUpperPairTwoStartRecoveredSignedMetricReserve
        q zeta rho n M

/-- The reconstructed upper-window reserve is exactly the existing literal
signed four-colour aggregate. -/
theorem pairedEtaGeometricUpperWindowTwoStartRecoveredSignedMetricReserve_eq
    {q : ℕ} (hq : 1 < q) (T : ℝ) (n M : ℕ) :
    pairedEtaGeometricUpperWindowTwoStartRecoveredSignedMetricReserve
        q T n M =
      pairedEtaGeometricUpperWindowSignedMetricReserve q T n M := by
  unfold pairedEtaGeometricUpperWindowTwoStartRecoveredSignedMetricReserve
    pairedEtaGeometricUpperWindowSignedMetricReserve
  apply Finset.sum_congr rfl
  intro rho _hrho
  apply Finset.sum_congr rfl
  intro zeta _hzeta
  exact
    pairedEtaGeometricUpperPairTwoStartRecoveredSignedMetricReserve_eq
      hq zeta rho n M

/-- The two-start recovered window reserve after removing the universal
`q ^ (-2*n)` coefficient scale. -/
def pairedEtaGeometricUpperWindowCoefficientNormalizedTwoStartRecoveredReserve
    (q : ℕ) (T : ℝ) (n M : ℕ) : ℝ :=
  ((q : ℝ) ^ n) ^ 2 *
    pairedEtaGeometricUpperWindowTwoStartRecoveredSignedMetricReserve
      q T n M

/-- The scale-free two-start recovered reserve is exactly the existing
coefficient-normalized balanced carrier. -/
theorem pairedEtaGeometricUpperWindowCoefficientNormalizedTwoStartRecoveredReserve_eq_balanced
    {q : ℕ} (hq : 1 < q) (T : ℝ) (n M : ℕ) :
    pairedEtaGeometricUpperWindowCoefficientNormalizedTwoStartRecoveredReserve
        q T n M =
      pairedEtaGeometricUpperWindowCoefficientNormalizedBalancedMetricReserve
        q T n M := by
  unfold
    pairedEtaGeometricUpperWindowCoefficientNormalizedTwoStartRecoveredReserve
  rw [pairedEtaGeometricUpperWindowTwoStartRecoveredSignedMetricReserve_eq hq]
  exact
    (pairedEtaGeometricUpperWindowCoefficientNormalizedBalancedMetricReserve_eq_scale_mul_signed
      hq.le T n M).symm

/-- The `13/18` and finite-window `18/18` implications stated using only the
scale-free two-start recovered reserve. -/
def PairedEtaGeometricReflectionEvenLongBlockTwoStartRecoveredReserveTargets
    (q : ℕ) (T : ℝ) (n M : ℕ) : Prop :=
  ((((31 : ℝ) * (spectralZetaZeroWindow T).card - 36) *
        pairedEtaGeometricReflectionEvenCoefficientNormalizedFramePotential
          q T n M <
      36 *
        pairedEtaGeometricUpperWindowCoefficientNormalizedTwoStartRecoveredReserve
          q T n M) →
    (13 : ℝ) / 18 <
      (spectralCriticalZetaZeroWindow T).card /
        (spectralZetaZeroWindow T).card) ∧
  (((((spectralZetaZeroWindow T).card : ℝ) - 1) *
        pairedEtaGeometricReflectionEvenCoefficientNormalizedFramePotential
          q T n M ≤
      pairedEtaGeometricUpperWindowCoefficientNormalizedTwoStartRecoveredReserve
        q T n M) →
    (spectralCriticalZetaZeroWindow T).card =
      (spectralZetaZeroWindow T).card)

/-- The recovered two-start certificate targets are exactly the existing
coefficient-normalized balanced targets. -/
theorem pairedEtaGeometricReflectionEvenLongBlockTwoStartRecoveredReserveTargets_iff_normalizedBalanced
    {q : ℕ} (hq : 1 < q) (T : ℝ) (n M : ℕ) :
    PairedEtaGeometricReflectionEvenLongBlockTwoStartRecoveredReserveTargets
        q T n M ↔
      PairedEtaGeometricReflectionEvenLongBlockCoefficientNormalizedBalancedMetricReserveTargets
        q T n M := by
  unfold
    PairedEtaGeometricReflectionEvenLongBlockTwoStartRecoveredReserveTargets
    PairedEtaGeometricReflectionEvenLongBlockCoefficientNormalizedBalancedMetricReserveTargets
  rw [pairedEtaGeometricUpperWindowCoefficientNormalizedTwoStartRecoveredReserve_eq_balanced
    hq]

/-- Every eligible finite zero window admits one odd prime whose late blocks
expose the exact `13/18` and `18/18` implications through the scale-free,
cutoff-independently recovered two-start carrier. -/
theorem exists_prime_eventually_pairedEtaGeometricReflectionEvenLongBlockTwoStartRecoveredReserveCertificateInterface
    {T : ℝ} (hT : 0 ≤ T)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    {M : ℕ} (hKM : (spectralZetaZeroWindow T).card ≤ M) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ 1 < q ∧
      ∀ᶠ n in atTop,
        PairedEtaGeometricReflectionEvenLongBlockTwoStartRecoveredReserveTargets
          q T n M := by
  obtain ⟨q, hqPrime, hqOdd, hq, hcert⟩ :=
    exists_prime_eventually_pairedEtaGeometricReflectionEvenLongBlockCoefficientNormalizedBalancedMetricReserveCertificateInterface
      hT hwindow hKM
  refine ⟨q, hqPrime, hqOdd, hq, ?_⟩
  filter_upwards [hcert] with n hn
  rw [pairedEtaGeometricReflectionEvenLongBlockTwoStartRecoveredReserveTargets_iff_normalizedBalanced
    hq]
  exact hn

end

end RiemannGaussian
