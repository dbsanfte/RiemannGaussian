import RiemannGaussian.Hybrid.EtaGeometricReflectionSumFiniteCoercivity

/-!
# Absorbing the common critical tilt into the literal eta frame metric

The uniform finite-prefix lower bound is first proved after multiplying every
coordinate by the common critical tilt.  That diagonal map is not unitary, so
its norm cannot be silently identified with the certificate's original packed
norm.  This module transports the estimate through that conditioning cost.

For arbitrary finite complex vectors, Lean bounds the squared norm after
pointwise weighting by the weight energy times the original squared norm.  It
then defines the exact critical coordinate weight and proves its finite energy
strictly positive.  Separately, the squared norm of an actual upper packed
frame atom is identified exactly with the squared norm of its losslessly
recovered complex reflection-sum channel; the half-realification factors
cancel without an estimate.

Combining these facts divides the tilted coercive lower bound by one explicit
positive coordinate-energy factor.  Thus every sufficiently late literal
upper frame atom itself, in the metric used by the certificate, has an
explicit positive lower bound and strictly positive norm.  The remaining
frontier is correlation control between distinct atoms and aggregate reserve.
-/

open Complex Matrix Finset Filter Topology
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian

noncomputable section

/-- Pointwise multiplication of a finite complex vector by complex coordinate
weights. -/
def finiteComplexPointwiseWeightedVector
    {m : Type*} (w v : m → ℂ) : m → ℂ :=
  fun j ↦ w j * v j

/-- Squared Euclidean energy of a finite complex coordinate-weight vector. -/
def finiteComplexVectorWeightEnergy
    {m : Type*} [Fintype m] (w : m → ℂ) : ℝ :=
  ∑ j, ‖w j‖ ^ 2

/-- The squared norm after pointwise weighting is at most weight energy times
the original squared norm. -/
theorem finiteComplexPointwiseWeightedVector_normSq_le
    {m : Type*} [Fintype m] (w v : m → ℂ) :
    finiteComplexVectorNormSq (finiteComplexPointwiseWeightedVector w v) ≤
      finiteComplexVectorWeightEnergy w * finiteComplexVectorNormSq v := by
  unfold finiteComplexVectorNormSq finiteComplexVectorWeightEnergy
    finiteComplexPointwiseWeightedVector
  calc
    ∑ j, ‖w j * v j‖ ^ 2 = ∑ j, ‖w j‖ ^ 2 * ‖v j‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [norm_mul]
      ring
    _ ≤ ∑ j, ‖w j‖ ^ 2 * ∑ k, ‖v k‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _hj
      apply mul_le_mul_of_nonneg_left
      · exact Finset.single_le_sum
          (fun k _hk ↦ sq_nonneg ‖v k‖) (Finset.mem_univ j)
      · positivity
    _ = (∑ j, ‖w j‖ ^ 2) * ∑ k, ‖v k‖ ^ 2 := by
      rw [Finset.sum_mul]

/-- Common critical-half coordinate tilt on a finite geometric block. -/
def etaGeometricCriticalCoordinateTilt
    (q M : ℕ) : Fin M → ℂ := fun j ↦
  (((q : ℂ) ^ ((1 / 2 : ℝ) : ℂ)) ^ (j : ℕ))

/-- Finite squared energy of the common critical coordinate tilt. -/
def etaGeometricCriticalCoordinateTiltEnergy
    (q M : ℕ) : ℝ :=
  finiteComplexVectorWeightEnergy (etaGeometricCriticalCoordinateTilt q M)

/-- Every nonempty critical coordinate-tilt block has positive weight energy. -/
theorem etaGeometricCriticalCoordinateTiltEnergy_pos
    (q : ℕ) {M : ℕ} (hM : 0 < M) :
    0 < etaGeometricCriticalCoordinateTiltEnergy q M := by
  unfold etaGeometricCriticalCoordinateTiltEnergy
    finiteComplexVectorWeightEnergy etaGeometricCriticalCoordinateTilt
  let j : Fin M := ⟨0, hM⟩
  apply Finset.sum_pos'
  · intro k _hk
    positivity
  · refine ⟨j, Finset.mem_univ j, ?_⟩
    simp [j]

/-- Untilted complex reflection-sum channel recovered from the two retained
coordinates of an actual upper frame atom. -/
def pairedEtaGeometricUpperFrameRecoveredVector
    (q : ℕ) (T : ℝ) (rho : ↥(spectralUpperZetaZeroWindow T))
    (n M : ℕ) : Fin M → ℂ := fun j ↦
  pairedEtaReflectionEvenFrameVector
        (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
        T (Sum.inr rho) (j, 0) -
    I * pairedEtaReflectionEvenFrameVector
        (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
        T (Sum.inr rho) (j, 1)

/-- The critically tilted recovered channel is pointwise multiplication of
the original recovered channel by the critical coordinate weights. -/
theorem pairedEtaGeometricCriticalTiltedUpperFrameRecoveredVector_eq_pointwiseWeighted
    (q : ℕ) (T : ℝ) (rho : ↥(spectralUpperZetaZeroWindow T))
    (n M : ℕ) :
    pairedEtaGeometricCriticalTiltedUpperFrameRecoveredVector q T rho n M =
      finiteComplexPointwiseWeightedVector
        (etaGeometricCriticalCoordinateTilt q M)
        (pairedEtaGeometricUpperFrameRecoveredVector q T rho n M) := by
  rfl

/-- The literal packed norm square of an upper frame atom is exactly the norm
square of its recovered complex reflection-sum channel. -/
theorem pairedEtaReflectionEvenFrameAtomNormSq_upper_eq_recovered
    (q : ℕ) (T : ℝ) (rho : ↥(spectralUpperZetaZeroWindow T))
    (n M : ℕ) :
    pairedEtaReflectionEvenFrameAtomNormSq
        (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
        T (Sum.inr rho) =
      finiteComplexVectorNormSq
        (pairedEtaGeometricUpperFrameRecoveredVector q T rho n M) := by
  let cutoff : Fin M → ℕ := fun k ↦
    pairedEtaGeometricHyperbolicCutoff q n k
  have hframe :=
    pairedEtaReflectionEvenFrameVector_upper_eq_half_realification_reflectionSum
      cutoff T rho
  unfold pairedEtaReflectionEvenFrameAtomNormSq
  rw [hframe]
  have hrealification := sum_norm_sq_complexHyperbolicRealification
    (pairedEtaTopPrefixFiniteCutoffFamilyReflectionSumChannel cutoff rho.1)
  unfold pairedEtaGeometricUpperFrameRecoveredVector
  have hrecoverPoint : ∀ j : Fin M,
      pairedEtaReflectionEvenFrameVector cutoff T (Sum.inr rho) (j, 0) -
          I * pairedEtaReflectionEvenFrameVector cutoff T (Sum.inr rho) (j, 1) =
        pairedEtaTopPrefixFiniteCutoffFamilyReflectionSumChannel
          cutoff rho.1 j := by
    intro j
    exact pairedEtaReflectionEvenFrameVector_upper_recover_reflectionSum
      cutoff T rho j
  simp only [finiteComplexVectorNormSq, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun j _hj ↦ congrArg (fun z : ℂ ↦ ‖z‖ ^ 2)
    (hrecoverPoint j))]
  calc
    ∑ x, ‖(1 / 2 : ℂ) *
        complexHyperbolicRealification
          (pairedEtaTopPrefixFiniteCutoffFamilyReflectionSumChannel
            cutoff rho.1) x‖ ^ 2 =
      (1 / 4 : ℝ) * ∑ x,
        ‖complexHyperbolicRealification
          (pairedEtaTopPrefixFiniteCutoffFamilyReflectionSumChannel
            cutoff rho.1) x‖ ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _hx
        rw [norm_mul]
        norm_num
        ring
    _ = _ := by rw [hrealification]; ring

/-- The tilted recovered-channel norm is bounded by critical weight energy
times the literal upper frame-atom norm. -/
theorem pairedEtaGeometricCriticalTiltedUpperFrameRecoveredVector_normSq_le
    (q : ℕ) (T : ℝ) (rho : ↥(spectralUpperZetaZeroWindow T))
    (n M : ℕ) :
    finiteComplexVectorNormSq
        (pairedEtaGeometricCriticalTiltedUpperFrameRecoveredVector
          q T rho n M) ≤
      etaGeometricCriticalCoordinateTiltEnergy q M *
        pairedEtaReflectionEvenFrameAtomNormSq
          (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
          T (Sum.inr rho) := by
  rw [pairedEtaGeometricCriticalTiltedUpperFrameRecoveredVector_eq_pointwiseWeighted,
    pairedEtaReflectionEvenFrameAtomNormSq_upper_eq_recovered]
  exact finiteComplexPointwiseWeightedVector_normSq_le _ _

/-- After paying the explicit coordinate-energy conditioning cost, every late
literal upper frame atom inherits the moving-coefficient coercive lower bound. -/
theorem eventually_spectralUpperZetaZeroWindow_geometricFrameAtomNormSq_coercive
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {T : ℝ}
    (rho : ↥(spectralUpperZetaZeroWindow T))
    {M : ℕ} (hM : 1 < M) :
    ∀ᶠ n in atTop,
      (finiteReciprocalRadialPhaseCoercivity M
            ‖etaGeometricShiftedMode q (1 / 2) rho.1.val‖
            (etaGeometricNormalizedMode q rho.1.val) / 2 *
          (‖pairedEtaGeometricCompletedPrefixCoefficient q rho.1 n‖ ^ 2 +
            ‖pairedEtaGeometricCompletedPrefixCoefficient q
              (NontrivialZetaZero.conjugatePartner rho.1) n‖ ^ 2)) /
          etaGeometricCriticalCoordinateTiltEnergy q M ≤
        pairedEtaReflectionEvenFrameAtomNormSq
          (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
          T (Sum.inr rho) := by
  have htilted :=
    eventually_spectralUpperZetaZeroWindow_geometricCriticalTiltedFrame_coercive
      hqOdd hq rho hM
  have henergy := etaGeometricCriticalCoordinateTiltEnergy_pos q (by omega : 0 < M)
  filter_upwards [htilted] with n hn
  apply (div_le_iff₀ henergy).2
  have hweight :=
    pairedEtaGeometricCriticalTiltedUpperFrameRecoveredVector_normSq_le
      q T rho n M
  exact hn.trans (by simpa [mul_comm] using hweight)

/-- Every sufficiently late literal upper frame atom has strictly positive
squared norm in the original certificate metric. -/
theorem eventually_spectralUpperZetaZeroWindow_geometricFrameAtomNormSq_pos
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {T : ℝ}
    (rho : ↥(spectralUpperZetaZeroWindow T))
    {M : ℕ} (hM : 1 < M) :
    ∀ᶠ n in atTop,
      0 < pairedEtaReflectionEvenFrameAtomNormSq
        (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
        T (Sum.inr rho) := by
  have hbound :=
    eventually_spectralUpperZetaZeroWindow_geometricFrameAtomNormSq_coercive
      hqOdd hq rho hM
  have hκ : 0 < finiteReciprocalRadialPhaseCoercivity M
      ‖etaGeometricShiftedMode q (1 / 2) rho.1.val‖
      (etaGeometricNormalizedMode q rho.1.val) / 2 := by
    exact half_pos
      (spectralUpperZetaZeroWindow_criticalShiftedReflectionCoercivity_pos
        hq rho hM)
  have henergy := etaGeometricCriticalCoordinateTiltEnergy_pos q (by omega : 0 < M)
  filter_upwards [hbound] with n hn
  have hcoefficient :
      0 < ‖pairedEtaGeometricCompletedPrefixCoefficient q rho.1 n‖ ^ 2 +
        ‖pairedEtaGeometricCompletedPrefixCoefficient q
          (NontrivialZetaZero.conjugatePartner rho.1) n‖ ^ 2 := by
    apply add_pos_of_pos_of_nonneg
    · exact sq_pos_of_pos (norm_pos_iff.mpr
        (pairedEtaGeometricCompletedPrefixCoefficient_ne_zero
          hq.le rho.1 n))
    · positivity
  exact (div_pos (mul_pos hκ hcoefficient) henergy).trans_le hn

end

end RiemannGaussian
