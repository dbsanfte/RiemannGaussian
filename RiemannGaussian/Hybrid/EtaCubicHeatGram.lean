import RiemannGaussian.EtaCubicHeatLimit

/-!
# Mixed cubic-phase eta heat matrices and their limiting Gram

Every mixed entry of the actual continuous phase matrix has the joint
critical limit. The limiting matrix has an independent integral-of-squares
formula and is positive semidefinite for real and complex coefficients.
All convergence statements concern a fixed family of phase probes.
-/

open Complex Filter MeasureTheory Set Topology Matrix
open scoped Classical ENNReal NNReal Interval Topology BigOperators ComplexOrder

namespace RiemannGaussian

noncomputable section

/-- The full limiting mixed matrix, retaining both phase parameter differences. -/
def pairedEtaCubicHeatProfileGram {ι : Type*} (lambda : ℝ) (kappa alpha : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j ↦ pairedEtaCubicHeatProfile lambda (kappa j - kappa i) (alpha j - alpha i)

/-- The actual continuous cubic-phase Gram at the moving critical tilt. -/
def pairedEtaSupportGapCubicPhaseGram {ι : Type*} (lambda h : ℝ) (kappa alpha : ι → ℝ) : Matrix ι ι ℝ :=
  pairedEtaSupportGapPhaseGram (pairedEtaMovingCriticalTilt lambda (Real.log (1 / h))) h
    (fun i ↦ pairedEtaCriticalCubicPhase (kappa i) (alpha i) h (Real.log (1 / h)))

/-- The limiting mixed profile matrix is real symmetric. -/
theorem pairedEtaCubicHeatProfileGram_isHermitian {ι : Type*} (lambda : ℝ) (kappa alpha : ι → ℝ) :
    (pairedEtaCubicHeatProfileGram lambda kappa alpha).IsHermitian := by
  apply Matrix.IsHermitian.ext_iff.mpr
  intro i j
  simp only [star_trivial, pairedEtaCubicHeatProfileGram, pairedEtaCubicHeatProfile]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun v ↦ by
    dsimp only
    congr 1
    unfold pairedEtaCubicBoundaryProfile
    apply intervalIntegral.integral_congr
    intro z _
    dsimp only
    rw [show v * (kappa i - kappa j + 3 * (alpha i - alpha j) * z ^ 2) =
      -(v * (kappa j - kappa i + 3 * (alpha j - alpha i) * z ^ 2)) by ring, Real.cos_neg]

/-- The inner logarithmic integral of the complete cosine phase energy
equals the full finite sum of mixed boundary entries. -/
theorem integral_cubic_finiteCosinePhaseEnergy {ι : Type*} [Fintype ι]
    (lambda v : ℝ) (kappa alpha c : ι → ℝ) :
    (∫ z in 0..1, Real.exp (-2 * lambda * z) *
      finiteCosinePhaseEnergy (fun i ↦ v * (kappa i + 3 * alpha i * z ^ 2)) c) =
      ∑ i, ∑ j, (c i * c j) * pairedEtaCubicBoundaryProfile lambda (kappa j - kappa i) (alpha j - alpha i) v := by
  let F : ι → ι → ℝ → ℝ := fun i j z ↦ (c i * c j) *
    (Real.exp (-2 * lambda * z) *
      Real.cos (v * ((kappa j - kappa i) + 3 * (alpha j - alpha i) * z ^ 2)))
  have hi : ∀ i j, IntervalIntegrable (F i j) volume 0 1 := fun i j ↦
    (by fun_prop : Continuous (F i j)).intervalIntegrable _ _
  have hfun : (fun z : ℝ ↦ Real.exp (-2 * lambda * z) *
      finiteCosinePhaseEnergy (fun i ↦ v * (kappa i + 3 * alpha i * z ^ 2)) c) =
      (fun z ↦ ∑ i, ∑ j, F i j z) := by
    funext z
    simp only [finiteCosinePhaseEnergy, Finset.mul_sum, F]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [show v * (kappa j + 3 * alpha j * z ^ 2) - v * (kappa i + 3 * alpha i * z ^ 2) =
      v * (kappa j - kappa i + 3 * (alpha j - alpha i) * z ^ 2) by ring]
    ring
  have hsum (i : ι) : IntervalIntegrable (fun z ↦ ∑ j, F i j z) volume 0 1 := by
    exact (by fun_prop : Continuous (fun z ↦ ∑ j, F i j z)).intervalIntegrable _ _
  rw [hfun, intervalIntegral.integral_finsetSum (fun i _ ↦ hsum i)]
  simp_rw [intervalIntegral.integral_finsetSum (fun j _ ↦ hi _ j), F,
    intervalIntegral.integral_const_mul]
  rfl

/-- Genuine integrability of the full limiting mixed quadratic form. -/
theorem integrableOn_cubic_finiteCosinePhaseEnergy {ι : Type*} [Fintype ι]
    (lambda : ℝ) (kappa alpha c : ι → ℝ) :
    IntegrableOn (fun v ↦ (v * Real.exp (-(1 / 4) * v ^ 2)) *
      (∫ z in 0..1, Real.exp (-2 * lambda * z) *
        finiteCosinePhaseEnergy (fun i ↦ v * (kappa i + 3 * alpha i * z ^ 2)) c)) (Ioi 0) := by
  have hi := integrable_finsetSum Finset.univ fun i _ ↦ integrable_finsetSum Finset.univ fun j _ ↦
    (integrableOn_pairedEtaCubicHeatProfile_kernel lambda (kappa j - kappa i) (alpha j - alpha i)).const_mul (c i * c j)
  apply hi.congr
  exact Eventually.of_forall fun v ↦ by
    dsimp only
    rw [integral_cubic_finiteCosinePhaseEnergy]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- The complete limiting matrix energy is the double integral of the
finite cosine phase energy, retaining every mixed term. -/
theorem pairedEtaCubicHeatProfileGram_energy_eq_integral {ι : Type*} [Fintype ι]
    (lambda : ℝ) (kappa alpha c : ι → ℝ) :
    finiteRealMatrixEnergy (pairedEtaCubicHeatProfileGram lambda kappa alpha) c =
      (1 / Real.sqrt Real.pi) * ∫ v in Ioi 0,
        (v * Real.exp (-(1 / 4) * v ^ 2)) *
          (∫ z in 0..1, Real.exp (-2 * lambda * z) *
            finiteCosinePhaseEnergy (fun i ↦ v * (kappa i + 3 * alpha i * z ^ 2)) c) := by
  let F : ι → ι → ℝ → ℝ := fun i j v ↦ (c i * c j) *
    (v * Real.exp (-(1 / 4) * v ^ 2) *
      pairedEtaCubicBoundaryProfile lambda (kappa j - kappa i) (alpha j - alpha i) v)
  have hi : ∀ i j, IntegrableOn (F i j) (Ioi 0) := fun i j ↦
    (integrableOn_pairedEtaCubicHeatProfile_kernel lambda (kappa j - kappa i) (alpha j - alpha i)).const_mul _
  have hfun : (fun v : ℝ ↦ (v * Real.exp (-(1 / 4) * v ^ 2)) *
      (∫ z in 0..1, Real.exp (-2 * lambda * z) *
        finiteCosinePhaseEnergy (fun i ↦ v * (kappa i + 3 * alpha i * z ^ 2)) c)) =
      (fun v ↦ ∑ i, ∑ j, F i j v) := by
    funext v
    rw [integral_cubic_finiteCosinePhaseEnergy]
    simp only [Finset.mul_sum, F]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hfun, integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hi i j)]
  simp_rw [integral_finsetSum _ (fun j _ ↦ hi _ j), F, integral_const_mul]
  simp only [finiteRealMatrixEnergy, pairedEtaCubicHeatProfileGram, pairedEtaCubicHeatProfile,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The limiting mixed matrix retains the explicit cosine and sine
squares of every finite real coefficient family. -/
theorem pairedEtaCubicHeatProfileGram_energy_eq_squares {ι : Type*} [Fintype ι]
    (lambda : ℝ) (kappa alpha c : ι → ℝ) :
    finiteRealMatrixEnergy (pairedEtaCubicHeatProfileGram lambda kappa alpha) c =
      (1 / Real.sqrt Real.pi) * ∫ v in Ioi 0,
        (v * Real.exp (-(1 / 4) * v ^ 2)) *
          (∫ z in 0..1, Real.exp (-2 * lambda * z) *
            ((∑ i, c i * Real.cos (v * (kappa i + 3 * alpha i * z ^ 2))) ^ 2 +
              (∑ i, c i * Real.sin (v * (kappa i + 3 * alpha i * z ^ 2))) ^ 2)) := by
  rw [pairedEtaCubicHeatProfileGram_energy_eq_integral]
  simp_rw [finiteCosinePhaseEnergy_eq_squares]

/-- The limiting real matrix is positive semidefinite by its own
integral-of-squares representation, without zero-spacing assumptions. -/
theorem pairedEtaCubicHeatProfileGram_posSemidef {ι : Type*} [Fintype ι]
    (lambda : ℝ) (kappa alpha : ι → ℝ) :
    (pairedEtaCubicHeatProfileGram lambda kappa alpha).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (pairedEtaCubicHeatProfileGram_isHermitian lambda kappa alpha)
  intro c
  rw [← finiteRealMatrixEnergy_eq_dotProduct, pairedEtaCubicHeatProfileGram_energy_eq_integral]
  apply mul_nonneg (by positivity)
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  apply mul_nonneg (mul_nonneg hv.le (Real.exp_pos _).le)
  apply intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1)
  intro z _
  exact mul_nonneg (Real.exp_pos _).le (finiteCosinePhaseEnergy_nonneg _ c)

/-- Positive semidefiniteness also holds for arbitrary complex coefficients. -/
theorem pairedEtaCubicHeatProfileGram_complex_posSemidef {ι : Type*} [Fintype ι]
    (lambda : ℝ) (kappa alpha : ι → ℝ) :
    ((pairedEtaCubicHeatProfileGram lambda kappa alpha).map Complex.ofReal).PosSemidef :=
  posSemidef_complex_ofReal (pairedEtaCubicHeatProfileGram_posSemidef lambda kappa alpha)

/-- Entrywise convergence of every mixed cubic phase channel of the actual
continuous eta matrix. Finite families retain the whole fixed matrix. -/
theorem pairedEtaSupportGapCubicPhaseGram_tendsto {ι : Type*}
    (lambda : ℝ) (kappa alpha : ι → ℝ) :
    Tendsto (fun h : ℝ ↦ (h * Real.log (1 / h))⁻¹ • pairedEtaSupportGapCubicPhaseGram lambda h kappa alpha)
      (𝓝[>] 0) (𝓝 (pairedEtaCubicHeatProfileGram lambda kappa alpha)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have hfun : (fun h : ℝ ↦ ((h * Real.log (1 / h))⁻¹ •
      pairedEtaSupportGapCubicPhaseGram lambda h kappa alpha) i j) =
      (fun h ↦ pairedEtaSupportGapGaussianLeakage
        (pairedEtaMovingCriticalTilt lambda (Real.log (1 / h))) h
        (pairedEtaCriticalCubicPhase (kappa j - kappa i) (alpha j - alpha i) h (Real.log (1 / h))) /
          (h * Real.log (1 / h))) := by
    funext h
    simp only [Matrix.smul_apply, smul_eq_mul, pairedEtaSupportGapCubicPhaseGram, pairedEtaSupportGapPhaseGram]
    have hphase : (fun t : ℝ ↦ pairedEtaCriticalCubicPhase (kappa j) (alpha j) h (Real.log (1 / h)) t -
        pairedEtaCriticalCubicPhase (kappa i) (alpha i) h (Real.log (1 / h)) t) =
        pairedEtaCriticalCubicPhase (kappa j - kappa i) (alpha j - alpha i) h (Real.log (1 / h)) := by
      funext t
      unfold pairedEtaCriticalCubicPhase
      ring
    rw [hphase]
    ring
  rw [hfun]
  exact pairedEtaSupportGapGaussianLeakage_cubic_movingTilt_tendsto lambda (kappa j - kappa i) (alpha j - alpha i)

end

end RiemannGaussian
