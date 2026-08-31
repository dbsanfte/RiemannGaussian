import RiemannGaussian.Hybrid.EtaGeometricReflectionSumCoercivity
import RiemannGaussian.EtaEnergyFiniteWindowMomentCorrelation

/-!
# Completion-coefficient transport for geometric eta reflection sums

The reciprocal-mode coercivity theorem applies arbitrary complex
coefficients, while the actual reflection-even certificate atom contains two
completed eta channels at cutoff-dependent scales.  This module connects
those interfaces exactly.

For every geometric block it defines the nonzero coefficient containing the
literal xi completion weight, the checked sharp eta-prefix limit, and the
inverse cutoff row scale.  After one common coordinate tilt, the completed
original channel is exactly that coefficient times the normalized literal
eta-prefix column.  The reflected-channel sum is therefore an exact two-column
combination, with neither coefficient discarded or replaced by a norm.

At the critical tilt, Lean finally identifies this same combination with the
complex channel recovered from the two retained coordinates of the actual
upper reflection-even frame atom.  This transports the completion data to the
coercive interface; a uniform perturbative lower bound for the still-finite
prefix columns remains to be proved before aggregation.
-/

open Complex Matrix Finset Filter
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian

noncomputable section

/-- Cutoff-dependent coefficient relating one completed geometric eta channel
to its normalized literal prefix column. -/
def pairedEtaGeometricCompletedPrefixCoefficient
    (q : ℕ) (rho : NontrivialZetaZero) (n : ℕ) : ℂ :=
  pairedEtaTopPrefixFiniteCompletionWeight rho *
    pairedEtaLowerMomentGeometricLimit rho *
      ((((q : ℂ) ^ rho.val) ^ n)⁻¹)

/-- The completed-prefix coefficient is nonzero at every positive base. -/
theorem pairedEtaGeometricCompletedPrefixCoefficient_ne_zero
    {q : ℕ} (hq : 0 < q) (rho : NontrivialZetaZero) (n : ℕ) :
    pairedEtaGeometricCompletedPrefixCoefficient q rho n ≠ 0 := by
  unfold pairedEtaGeometricCompletedPrefixCoefficient
    pairedEtaTopPrefixFiniteCompletionWeight
  have hqComplex : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero
        (pairedEtaXiCompletionFactor_ne_zero
          (NontrivialZetaZero.zero_lt_re rho)
          (NontrivialZetaZero.re_lt_one rho))
        (NontrivialZetaZero.coe_ne_zero rho))
      (pairedEtaLowerMomentGeometricLimit_ne_zero rho))
    (inv_ne_zero (pow_ne_zero n
      (Complex.cpow_ne_zero_iff.mpr (Or.inl hqComplex))))

/-- After a common coordinate tilt, one completed original eta channel is
exactly its explicit coefficient times the normalized literal prefix. -/
theorem pairedEtaGeometric_tiltedOriginalChannel_eq_coefficient_mul_normalizedPrefix
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) (σ : ℝ)
    (rho : NontrivialZetaZero) {n : ℕ} (hn : 1 ≤ n)
    (M : ℕ) (j : Fin M) :
    (((q : ℂ) ^ (σ : ℂ)) ^ (j : ℕ)) *
        pairedEtaTopPrefixFiniteOriginalChannelTerm rho
          (pairedEtaGeometricHyperbolicCutoff q n j) =
      pairedEtaGeometricCompletedPrefixCoefficient q rho n *
        pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector
          q σ rho n M j := by
  rw [originalChannelTerm_eq_completionWeight_mul_centeredMoment]
  unfold pairedEtaTopPrefixFiniteCenteredMoment
  rw [pairedEtaGeometricHyperbolicCutoff_succ hqOdd hq hn]
  unfold pairedEtaGeometricCompletedPrefixCoefficient
    pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector
    pairedEtaLowerMomentGeometricPrefix
  have hqComplex : (q : ℂ) ≠ 0 := by
    have hq0 : q ≠ 0 := by omega
    exact_mod_cast hq0
  have hbase : ((q : ℂ) ^ rho.val) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hqComplex)
  field_simp [pairedEtaLowerMomentGeometricLimit_ne_zero rho,
    pow_ne_zero _ hbase]

/-- Commonly tilted completed reflection-sum channel on a consecutive
geometric cutoff block. -/
def pairedEtaGeometricTiltedReflectionSumVector
    (q : ℕ) (σ : ℝ) (rho : NontrivialZetaZero)
    (n M : ℕ) : Fin M → ℂ := fun j ↦
  (((q : ℂ) ^ (σ : ℂ)) ^ (j : ℕ)) *
    pairedEtaTopPrefixFiniteCutoffFamilyReflectionSumChannel
      (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
      rho j

/-- A commonly tilted completed reflection sum is exactly the two normalized
prefix columns with their distinct explicit completion coefficients. -/
theorem pairedEtaGeometricTiltedReflectionSumVector_eq_completedPrefixCombination
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) (σ : ℝ)
    (rho : NontrivialZetaZero) {n : ℕ} (hn : 1 ≤ n) (M : ℕ) :
    pairedEtaGeometricTiltedReflectionSumVector q σ rho n M =
      pairedEtaGeometricCompletedPrefixCoefficient q
          (NontrivialZetaZero.conjugatePartner rho) n •
        pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector q σ
          (NontrivialZetaZero.conjugatePartner rho) n M +
      pairedEtaGeometricCompletedPrefixCoefficient q rho n •
        pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector
          q σ rho n M := by
  funext j
  unfold pairedEtaGeometricTiltedReflectionSumVector
    pairedEtaTopPrefixFiniteCutoffFamilyReflectionSumChannel
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← pairedEtaGeometric_tiltedOriginalChannel_eq_coefficient_mul_normalizedPrefix
      hqOdd hq σ (NontrivialZetaZero.conjugatePartner rho) hn M j,
    ← pairedEtaGeometric_tiltedOriginalChannel_eq_coefficient_mul_normalizedPrefix
      hqOdd hq σ rho hn M j]
  ring

/-- Critical-tilt specialization of the exact completed reflection-sum
coefficient transport. -/
theorem pairedEtaGeometricCriticalTiltedReflectionSumVector_eq_completedPrefixCombination
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q)
    (rho : NontrivialZetaZero) {n : ℕ} (hn : 1 ≤ n) (M : ℕ) :
    pairedEtaGeometricTiltedReflectionSumVector q (1 / 2) rho n M =
      pairedEtaGeometricCompletedPrefixCoefficient q
          (NontrivialZetaZero.conjugatePartner rho) n •
        pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector q (1 / 2)
          (NontrivialZetaZero.conjugatePartner rho) n M +
      pairedEtaGeometricCompletedPrefixCoefficient q rho n •
        pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector
          q (1 / 2) rho n M := by
  exact pairedEtaGeometricTiltedReflectionSumVector_eq_completedPrefixCombination
    hqOdd hq (1 / 2) rho hn M

/-- Complex channel recovered from the two retained coordinates of an actual
upper reflection-even frame atom, with the common critical coordinate tilt. -/
def pairedEtaGeometricCriticalTiltedUpperFrameRecoveredVector
    (q : ℕ) (T : ℝ) (rho : ↥(spectralUpperZetaZeroWindow T))
    (n M : ℕ) : Fin M → ℂ := fun j ↦
  (((q : ℂ) ^ ((1 / 2 : ℝ) : ℂ)) ^ (j : ℕ)) *
    (pairedEtaReflectionEvenFrameVector
          (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
          T (Sum.inr rho) (j, 0) -
      I * pairedEtaReflectionEvenFrameVector
          (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
          T (Sum.inr rho) (j, 1))

/-- The critically tilted channel recovered from the actual upper frame atom
is exactly the completed reflection-sum vector. -/
theorem pairedEtaGeometricCriticalTiltedUpperFrameRecoveredVector_eq_reflectionSum
    (q : ℕ) (T : ℝ) (rho : ↥(spectralUpperZetaZeroWindow T))
    (n M : ℕ) :
    pairedEtaGeometricCriticalTiltedUpperFrameRecoveredVector
        q T rho n M =
      pairedEtaGeometricTiltedReflectionSumVector
        q (1 / 2) rho.1 n M := by
  funext j
  unfold pairedEtaGeometricCriticalTiltedUpperFrameRecoveredVector
    pairedEtaGeometricTiltedReflectionSumVector
  rw [pairedEtaReflectionEvenFrameVector_upper_recover_reflectionSum]

/-- Every actual upper-window frame atom, after lossless coordinate recovery
and common critical tilt, is exactly the two normalized literal eta-prefix
columns with their nonzero cutoff-dependent completion coefficients. -/
theorem spectralUpperZetaZeroWindow_geometricCriticalTiltedFrame_eq_completedPrefixCombination
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {T : ℝ}
    (rho : ↥(spectralUpperZetaZeroWindow T))
    {n : ℕ} (hn : 1 ≤ n) (M : ℕ) :
    pairedEtaGeometricCriticalTiltedUpperFrameRecoveredVector
        q T rho n M =
      pairedEtaGeometricCompletedPrefixCoefficient q
          (NontrivialZetaZero.conjugatePartner rho.1) n •
        pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector q (1 / 2)
          (NontrivialZetaZero.conjugatePartner rho.1) n M +
      pairedEtaGeometricCompletedPrefixCoefficient q rho.1 n •
        pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector
          q (1 / 2) rho.1 n M := by
  rw [pairedEtaGeometricCriticalTiltedUpperFrameRecoveredVector_eq_reflectionSum]
  exact
    pairedEtaGeometricCriticalTiltedReflectionSumVector_eq_completedPrefixCombination
      hqOdd hq rho.1 hn M

end

end RiemannGaussian
