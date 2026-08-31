import RiemannGaussian.Hybrid.EtaGeometricReflectionSumMetricCorrelation

/-!
# Explicit bounds for the eta reflection-pair metric mode matrix

The preceding metric representation leaves each limiting upper-pair entry as
a recovery-metric correlation of critically shifted geometric modes.  This
module evaluates that metric exactly.  The inverse squared-modulus metric
cancels the common critical tilt, leaving the ordinary correlation of the raw
eta decay modes, hence one explicit finite geometric sum.

Every raw decay mode attached to a nontrivial zeta zero has norm strictly less
than one at a base greater than one.  Lean proves a phase-and-radius sensitive
bound for the resulting geometric sum and transports it back to all four
entries of the literal normalized-prefix metric matrix, simultaneously and
with arbitrary positive asymptotic slack.

This is the first quantitative estimate on the information-preserving
two-colour matrix.  It does not yet control the moving completion-coefficient
contraction or aggregate certificate reserve.
-/

open Complex Matrix Finset Filter Topology
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian

noncomputable section

/-- Raw eta decay-mode family retaining the reflected/original colours of an
upper pair. -/
def pairedEtaGeometricUpperRawDecayModeFamily
    (q : ℕ) {T : ℝ} (rho : ↥(spectralUpperZetaZeroWindow T))
    (M : ℕ) : Fin 2 → Fin M → ℂ := fun i ↦
  finiteGeometricPhaseVector M
    (etaGeometricDecayMode q
      (pairedEtaGeometricUpperReflectionPairZero rho i).val)

/-- A critically shifted geometric vector is pointwise critical tilt times
the corresponding raw decay-mode vector. -/
theorem pairedEtaGeometricCriticalUpperShiftedModeFamily_eq_pointwiseWeighted_raw
    (q : ℕ) {T : ℝ} (rho : ↥(spectralUpperZetaZeroWindow T))
    (M : ℕ) (i : Fin 2) :
    pairedEtaGeometricCriticalUpperShiftedModeFamily q rho M i =
      finiteComplexPointwiseWeightedVector
        (etaGeometricCriticalCoordinateTilt q M)
        (pairedEtaGeometricUpperRawDecayModeFamily q rho M i) := by
  funext j
  unfold pairedEtaGeometricCriticalUpperShiftedModeFamily
    pairedEtaGeometricUpperRawDecayModeFamily
    etaGeometricShiftedMode etaGeometricCriticalCoordinateTilt
    finiteComplexPointwiseWeightedVector finiteGeometricPhaseVector
  rw [mul_pow]

/-- The recovery metric cancels the common critical tilt exactly in every
limiting two-colour matrix entry. -/
theorem pairedEtaGeometricCriticalUpperMetricModeCorrelationMatrix_apply_eq_raw
    {q : ℕ} (hq : 0 < q) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    (M : ℕ) (i j : Fin 2) :
    pairedEtaGeometricCriticalUpperMetricModeCorrelationMatrix
        q zeta rho M i j =
      star (pairedEtaGeometricUpperRawDecayModeFamily q zeta M i) ⬝ᵥ
        pairedEtaGeometricUpperRawDecayModeFamily q rho M j := by
  unfold pairedEtaGeometricCriticalUpperMetricModeCorrelationMatrix
  rw [pairedEtaGeometricCriticalUpperShiftedModeFamily_eq_pointwiseWeighted_raw,
    pairedEtaGeometricCriticalUpperShiftedModeFamily_eq_pointwiseWeighted_raw]
  exact finiteComplexDiagonalMetricCorrelation_weighted_recover
    (etaGeometricCriticalCoordinateTilt q M)
    (pairedEtaGeometricUpperRawDecayModeFamily q rho M j)
    (pairedEtaGeometricUpperRawDecayModeFamily q zeta M i)
    (etaGeometricCriticalCoordinateTilt_ne_zero hq)

/-- Every limiting metric matrix entry is an explicit finite geometric sum
of one raw relative decay mode. -/
theorem pairedEtaGeometricCriticalUpperMetricModeCorrelationMatrix_apply_eq_geomSum
    {q : ℕ} (hq : 0 < q) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    (M : ℕ) (i j : Fin 2) :
    pairedEtaGeometricCriticalUpperMetricModeCorrelationMatrix
        q zeta rho M i j =
      ∑ k ∈ Finset.range M,
        (star (etaGeometricDecayMode q
            (pairedEtaGeometricUpperReflectionPairZero zeta i).val) *
          etaGeometricDecayMode q
            (pairedEtaGeometricUpperReflectionPairZero rho j).val) ^ k := by
  rw [pairedEtaGeometricCriticalUpperMetricModeCorrelationMatrix_apply_eq_raw
    hq]
  exact finiteGeometricPhaseVector_correlation_eq_geomSum _ _ _

/-- Raw eta decay modes of all nontrivial zeros lie strictly inside the unit
disk at every base greater than one. -/
theorem norm_etaGeometricDecayMode_lt_one
    {q : ℕ} (hq : 1 < q) (rho : NontrivialZetaZero) :
    ‖etaGeometricDecayMode q rho.val‖ < 1 := by
  rw [norm_etaGeometricDecayMode hq.le]
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · exact_mod_cast hq
  · linarith [NontrivialZetaZero.zero_lt_re rho]

/-- The relative raw decay ratio from any two colours of two upper pairs lies
strictly inside the unit disk. -/
theorem norm_pairedEtaGeometricUpperRawRelativeMode_lt_one
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T)) (i j : Fin 2) :
    ‖star (etaGeometricDecayMode q
          (pairedEtaGeometricUpperReflectionPairZero zeta i).val) *
        etaGeometricDecayMode q
          (pairedEtaGeometricUpperReflectionPairZero rho j).val‖ < 1 := by
  rw [norm_mul, norm_star]
  have hz := norm_etaGeometricDecayMode_lt_one hq
    (pairedEtaGeometricUpperReflectionPairZero zeta i)
  have hr := norm_etaGeometricDecayMode_lt_one hq
    (pairedEtaGeometricUpperReflectionPairZero rho j)
  have hz0 : 0 ≤ ‖etaGeometricDecayMode q
      (pairedEtaGeometricUpperReflectionPairZero zeta i).val‖ := norm_nonneg _
  nlinarith

/-- Every raw relative mode has a strictly positive gap from one. -/
theorem pairedEtaGeometricUpperRawRelativeMode_gap_pos
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T)) (i j : Fin 2) :
    0 < ‖star (etaGeometricDecayMode q
          (pairedEtaGeometricUpperReflectionPairZero zeta i).val) *
        etaGeometricDecayMode q
          (pairedEtaGeometricUpperReflectionPairZero rho j).val - 1‖ := by
  apply norm_pos_iff.mpr
  rw [sub_ne_zero]
  intro hone
  have hnorm := congrArg norm hone
  rw [norm_one] at hnorm
  have hlt := norm_pairedEtaGeometricUpperRawRelativeMode_lt_one
    hq zeta rho i j
  linarith

/-- A finite geometric sum with ratio in the closed unit disk obeys the same
exact gap-times-norm ceiling two as the unit-circle case. -/
theorem finite_geometric_sum_mul_gap_le_two_of_norm_le_one
    (M : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖∑ k ∈ Finset.range M, z ^ k‖ * ‖z - 1‖ ≤ 2 := by
  rw [← norm_mul, geom_sum_mul]
  calc
    ‖z ^ M - 1‖ ≤ ‖z ^ M‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := by
      apply add_le_add
      · rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg z) hz
      · norm_num
    _ = 2 := by norm_num

/-- Every limiting metric matrix entry satisfies an explicit
phase-and-radius gap bound with constant two. -/
theorem pairedEtaGeometricCriticalUpperMetricModeCorrelationMatrix_mul_gap_le_two
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    (M : ℕ) (i j : Fin 2) :
    ‖pairedEtaGeometricCriticalUpperMetricModeCorrelationMatrix
        q zeta rho M i j‖ *
      ‖star (etaGeometricDecayMode q
            (pairedEtaGeometricUpperReflectionPairZero zeta i).val) *
          etaGeometricDecayMode q
            (pairedEtaGeometricUpperReflectionPairZero rho j).val - 1‖ ≤ 2 := by
  rw [pairedEtaGeometricCriticalUpperMetricModeCorrelationMatrix_apply_eq_geomSum
    hq.le]
  exact finite_geometric_sum_mul_gap_le_two_of_norm_le_one M _
    (norm_pairedEtaGeometricUpperRawRelativeMode_lt_one
      hq zeta rho i j).le

/-- Pointwise convergence of one literal metric prefix-matrix entry to its
explicit raw geometric-sum limit. -/
theorem tendsto_pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix_apply
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    (M : ℕ) (i j : Fin 2) :
    Tendsto (fun n : ℕ ↦
      pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix
        q zeta rho n M i j) atTop
      (nhds (pairedEtaGeometricCriticalUpperMetricModeCorrelationMatrix
        q zeta rho M i j)) := by
  have hmatrix :=
    tendsto_pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix
      hqOdd hq zeta rho M
  change Tendsto
    (fun n i j ↦
      pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix
        q zeta rho n M i j) atTop
    (nhds (fun i j ↦
      pairedEtaGeometricCriticalUpperMetricModeCorrelationMatrix
        q zeta rho M i j)) at hmatrix
  rw [tendsto_pi_nhds] at hmatrix
  specialize hmatrix i
  rw [tendsto_pi_nhds] at hmatrix
  exact hmatrix j

/-- With arbitrary positive slack, all four literal metric prefix
correlations simultaneously inherit the limiting constant-two gap bound. -/
theorem eventually_pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix_mul_gap_lt
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    (M : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ i j : Fin 2,
      ‖pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix
          q zeta rho n M i j‖ *
        ‖star (etaGeometricDecayMode q
              (pairedEtaGeometricUpperReflectionPairZero zeta i).val) *
            etaGeometricDecayMode q
              (pairedEtaGeometricUpperReflectionPairZero rho j).val - 1‖ <
          2 + ε := by
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  let gap :=
    ‖star (etaGeometricDecayMode q
          (pairedEtaGeometricUpperReflectionPairZero zeta i).val) *
        etaGeometricDecayMode q
          (pairedEtaGeometricUpperReflectionPairZero rho j).val - 1‖
  have ht :=
    (tendsto_pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix_apply
      hqOdd hq zeta rho M i j).norm.mul_const gap
  have hlimit :
      ‖pairedEtaGeometricCriticalUpperMetricModeCorrelationMatrix
          q zeta rho M i j‖ * gap < 2 + ε :=
    lt_of_le_of_lt
      (pairedEtaGeometricCriticalUpperMetricModeCorrelationMatrix_mul_gap_le_two
        hq zeta rho M i j)
      (lt_add_of_pos_right 2 hε)
  exact ht.eventually (Iio_mem_nhds hlimit)

/-- The same phase-and-radius bound holds eventually and simultaneously over
the complete finite upper zero window and both reflection colours. -/
theorem eventually_spectralUpperZetaZeroWindow_geometricCriticalMetricPrefixCorrelationMatrix_mul_gap_lt
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) (T : ℝ)
    (M : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      ∀ zeta rho : ↥(spectralUpperZetaZeroWindow T),
        ∀ i j : Fin 2,
          ‖pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix
              q zeta rho n M i j‖ *
            ‖star (etaGeometricDecayMode q
                  (pairedEtaGeometricUpperReflectionPairZero zeta i).val) *
                etaGeometricDecayMode q
                  (pairedEtaGeometricUpperReflectionPairZero rho j).val - 1‖ <
              2 + ε := by
  apply Filter.eventually_all.mpr
  intro zeta
  apply Filter.eventually_all.mpr
  intro rho
  exact
    eventually_pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix_mul_gap_lt
      hqOdd hq zeta rho M hε

end

end RiemannGaussian
