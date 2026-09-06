import RiemannGaussian.EtaCurrentKernelMass

/-!
# Simultaneous heat and tilt for the actual completed current

The tilt `(N+1)⁻²` and heat width `(N+1)⁴` are independent of the zero.
Their reconstruction error has an explicit logarithmic-over-cubic bound;
the odd arithmetic weight leaves a logarithmic-over-square majorant. The
source is the original completed current and its exact signed gap-return
error, retained in the imported reconstruction theorems.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The simultaneous reconstruction tilt at arithmetic cutoff `N`. -/
def pairedEtaCurrentReconstructionTilt (N : ℕ) : ℝ := 1 / (N + 1 : ℝ) ^ 2

/-- The simultaneous broad heat width at arithmetic cutoff `N`. -/
def pairedEtaCurrentReconstructionWidth (N : ℕ) : ℝ := (N + 1 : ℝ) ^ 4

/-- The actual normalized gap return with the simultaneous parameters. -/
def pairedEtaLeadingCurrentScheduledGapReturn (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  pairedEtaLeadingCurrentNormalizedGapReturn rho N
    (pairedEtaCurrentReconstructionTilt N) (pairedEtaCurrentReconstructionWidth N)

/-- Every scheduled tilt is positive and at most one, and every width is positive. -/
theorem pairedEtaCurrentReconstructionSchedule_bounds (N : ℕ) :
    0 < pairedEtaCurrentReconstructionTilt N ∧
    pairedEtaCurrentReconstructionTilt N ≤ 1 ∧
    0 < pairedEtaCurrentReconstructionWidth N := by
  have hx : (1 : ℝ) ≤ N + 1 := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  dsimp [pairedEtaCurrentReconstructionTilt, pairedEtaCurrentReconstructionWidth]
  refine ⟨by positivity, ?_, by positivity⟩
  simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) (one_le_pow₀ (n := 2) hx)

/-- The explicit completion-dependent coefficient of the scheduled error. -/
def pairedEtaCurrentReconstructionErrorConstant (rho : NontrivialZetaZero) : ℝ :=
  pairedEtaLeadingCurrentMassConstant rho * (3 + 2 / pairedEtaGapLaplaceMass 1)

/-- The scheduled error coefficient is nonnegative. -/
theorem pairedEtaCurrentReconstructionErrorConstant_nonneg (rho : NontrivialZetaZero) :
    0 ≤ pairedEtaCurrentReconstructionErrorConstant rho := by
  have hC := pairedEtaLeadingCurrentMassConstant_nonneg rho
  have hM := (pairedEtaGapLaplaceMass_pos (by norm_num : (0 : ℝ) < 1)).le
  dsimp [pairedEtaCurrentReconstructionErrorConstant]
  positivity

/-- Both scale errors in the actual reconstruction are bounded simultaneously. -/
theorem current_reconstruction_scale_error_le {x L M : ℝ}
    (hx : 1 ≤ x) (hL : 0 ≤ L) (hM : 0 < M) :
    (1 / x ^ 2) * L + (2 / (M * (1 / x ^ 2) ^ 3) + 2 * L ^ 2) / (x ^ 4) ^ 2 ≤
      (3 + 2 / M) * (1 + L) ^ 2 / x ^ 2 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hxp : x ^ 2 ≤ x ^ 8 := pow_le_pow_right₀ hx (by norm_num)
  have hquot : 2 * L ^ 2 / x ^ 8 ≤ 2 * L ^ 2 / x ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hxp
  have hpoly : L + 2 / M + 2 * L ^ 2 ≤ (3 + 2 / M) * (1 + L) ^ 2 := by
    have hc : 0 ≤ 2 / M := by positivity
    have hp : 0 ≤ (2 / M) * (L ^ 2 + 2 * L) := mul_nonneg hc (by positivity)
    nlinarith [sq_nonneg L]
  calc
    _ = L / x ^ 2 + 2 / M / x ^ 2 + 2 * L ^ 2 / x ^ 8 := by
      field_simp
      ring
    _ ≤ L / x ^ 2 + 2 / M / x ^ 2 + 2 * L ^ 2 / x ^ 2 := add_le_add le_rfl hquot
    _ = (L + 2 / M + 2 * L ^ 2) / x ^ 2 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hpoly (by positivity)

/-- The actual simultaneous return differs from the unchanged current by
an explicit logarithmic-over-cubic quantity at every arithmetic cutoff. -/
theorem pairedEtaLeadingCurrentScheduledGapReturn_error_le
    (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaLeadingCurrentScheduledGapReturn rho N -
      (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ)‖ ≤
      pairedEtaCurrentReconstructionErrorConstant rho *
        (1 + pairedEtaLogTailCutoff (N + 2)) ^ (2 * analyticZetaZeroMultiplicity rho + 2) /
          (N + 1 : ℝ) ^ 3 := by
  obtain ⟨ha, ha1, hh⟩ := pairedEtaCurrentReconstructionSchedule_bounds N
  have hC := pairedEtaLeadingCurrentMassConstant_nonneg rho
  have hL := pairedEtaLogTailCutoff_nonneg (N + 2)
  have hM := pairedEtaGapLaplaceMass_pos (by norm_num : (0 : ℝ) < 1)
  have hx : (1 : ℝ) ≤ N + 1 := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  apply (pairedEtaLeadingCurrentNormalizedGapReturn_error_le_arithmetic rho N ha ha1 hh).trans
  calc
    _ ≤ (pairedEtaLeadingCurrentMassConstant rho *
        (1 + pairedEtaLogTailCutoff (N + 2)) ^ (2 * analyticZetaZeroMultiplicity rho) / (N + 1 : ℝ)) *
        ((3 + 2 / pairedEtaGapLaplaceMass 1) * (1 + pairedEtaLogTailCutoff (N + 2)) ^ 2 /
          (N + 1 : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (current_reconstruction_scale_error_le hx hL hM) (by positivity)
    _ = _ := by
      unfold pairedEtaCurrentReconstructionErrorConstant
      rw [pow_add]
      field_simp

/-- The required odd cutoff weight leaves a logarithmic-over-square
majorant for the actual reconstruction error. -/
theorem pairedEtaLeadingCurrentScheduledGapReturn_weighted_error_le
    (rho : NontrivialZetaZero) (N : ℕ) :
    (2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentScheduledGapReturn rho N -
      (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ)‖ ≤
      2 * pairedEtaCurrentReconstructionErrorConstant rho *
        (1 + pairedEtaLogTailCutoff (N + 2)) ^ (2 * analyticZetaZeroMultiplicity rho + 2) /
          (N + 1 : ℝ) ^ 2 := by
  have hD := pairedEtaCurrentReconstructionErrorConstant_nonneg rho
  have hL := pairedEtaLogTailCutoff_nonneg (N + 2)
  calc
    _ ≤ (2 * N + 1 : ℝ) * (pairedEtaCurrentReconstructionErrorConstant rho *
        (1 + pairedEtaLogTailCutoff (N + 2)) ^ (2 * analyticZetaZeroMultiplicity rho + 2) /
          (N + 1 : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_left (pairedEtaLeadingCurrentScheduledGapReturn_error_le rho N) (by positivity)
    _ ≤ (2 * (N + 1) : ℝ) * (pairedEtaCurrentReconstructionErrorConstant rho *
        (1 + pairedEtaLogTailCutoff (N + 2)) ^ (2 * analyticZetaZeroMultiplicity rho + 2) /
          (N + 1 : ℝ) ^ 3) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by field_simp

end

end RiemannGaussian
