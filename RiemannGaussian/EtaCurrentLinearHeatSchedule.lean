import RiemannGaussian.EtaCurrentEndpointSeries

/-!
# Linear heat width for the original completed current

The actual arithmetic midpoint gain makes the first heat correction
summable with width `2(N+1)`. The signed midpoint term remains explicit,
and the checked inverse-square-width defect controls the remaining error
on the entire original gap. Neither current nor return is replaced.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- A linear heat width, independent of the zero and its multiplicity. -/
def pairedEtaCurrentLinearHeatWidth (N : ℕ) : ℝ := 2 * (N + 1 : ℝ)

/-- The existing zero-tilt full gap return evaluated at linear width. -/
def pairedEtaLeadingCurrentLinearHeatReturn (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  pairedEtaLeadingCurrentZeroTiltGapReturn rho N (pairedEtaCurrentLinearHeatWidth N)

/-- The actual signed midpoint term in the linear-width return. -/
def pairedEtaLeadingCurrentLinearMidpointTerm (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  ((pairedEtaLeadingCurrentMidpointMoment rho N /
    (Real.sqrt Real.pi * pairedEtaCurrentLinearHeatWidth N) : ℝ) : ℂ)

/-- Every linear width lies in the range of the proved full-gap normalization. -/
theorem pairedEtaCurrentLinearHeatWidth_ge_two (N : ℕ) :
    2 ≤ pairedEtaCurrentLinearHeatWidth N := by
  unfold pairedEtaCurrentLinearHeatWidth
  have := Nat.cast_nonneg (α := ℝ) N
  linarith

/-- The odd-weighted midpoint correction has an explicit summable
arithmetic majorant at the linear heat width. -/
theorem pairedEtaLeadingCurrentLinearMidpointTerm_weighted_le (rho : NontrivialZetaZero) (N : ℕ) :
    (2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearMidpointTerm rho N‖ ≤
      (2 * (analyticZetaZeroMultiplicity rho : ℝ) / Real.sqrt Real.pi) *
        ((1 + pairedEtaLogTailCutoff (N + 2)) * pairedEtaCurrentMidpointEnvelope rho N / (N + 1 : ℝ)) := by
  have hh : 0 < pairedEtaCurrentLinearHeatWidth N := lt_of_lt_of_le (by norm_num) (pairedEtaCurrentLinearHeatWidth_ge_two N)
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hw : (2 * N + 1 : ℝ) ≤ pairedEtaCurrentLinearHeatWidth N := by
    unfold pairedEtaCurrentLinearHeatWidth
    linarith
  rw [pairedEtaLeadingCurrentLinearMidpointTerm, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_pos (mul_pos hs hh)]
  calc
    _ ≤ pairedEtaCurrentLinearHeatWidth N *
        (|pairedEtaLeadingCurrentMidpointMoment rho N| / (Real.sqrt Real.pi * pairedEtaCurrentLinearHeatWidth N)) :=
      mul_le_mul_of_nonneg_right hw (by positivity)
    _ = |pairedEtaLeadingCurrentMidpointMoment rho N| / Real.sqrt Real.pi := by field_simp
    _ ≤ (2 * (analyticZetaZeroMultiplicity rho : ℝ) * (1 + pairedEtaLogTailCutoff (N + 2)) /
        (N + 1 : ℝ) * pairedEtaCurrentMidpointEnvelope rho N) / Real.sqrt Real.pi :=
      div_le_div_of_nonneg_right (abs_pairedEtaLeadingCurrentMidpointMoment_le_arithmetic rho N) hs.le
    _ = _ := by ring

/-- The original signed return minus the original current and midpoint
term has an explicit cubic-cutoff error at linear heat width. -/
theorem pairedEtaLeadingCurrentLinearHeatReturn_after_midpoint_error_le (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaLeadingCurrentLinearHeatReturn rho N -
      (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ) - pairedEtaLeadingCurrentLinearMidpointTerm rho N‖ ≤
      (19 / 4) * pairedEtaLeadingCurrentMassConstant rho *
        (1 + pairedEtaLogTailCutoff (N + 2)) ^ (2 * analyticZetaZeroMultiplicity rho + 3) / (N + 1 : ℝ) ^ 3 := by
  apply (pairedEtaLeadingCurrentZeroTiltGapReturn_midpoint_error_le_arithmetic rho N
    (pairedEtaCurrentLinearHeatWidth_ge_two N)).trans_eq
  unfold pairedEtaCurrentLinearHeatWidth
  field_simp
  ring

/-- After the actual midpoint term, the odd arithmetic weight leaves an
explicit logarithmic-power-over-square reconstruction remainder. -/
theorem pairedEtaLeadingCurrentLinearHeatReturn_after_midpoint_weighted_error_le
    (rho : NontrivialZetaZero) (N : ℕ) :
    (2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho N -
      (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ) - pairedEtaLeadingCurrentLinearMidpointTerm rho N‖ ≤
      (19 / 2) * pairedEtaLeadingCurrentMassConstant rho *
        (1 + pairedEtaLogTailCutoff (N + 2)) ^ (2 * analyticZetaZeroMultiplicity rho + 3) / (N + 1 : ℝ) ^ 2 := by
  have hC := pairedEtaLeadingCurrentMassConstant_nonneg rho
  have hL := pairedEtaLogTailCutoff_nonneg (N + 2)
  calc
    _ ≤ (2 * N + 1 : ℝ) * ((19 / 4) * pairedEtaLeadingCurrentMassConstant rho *
        (1 + pairedEtaLogTailCutoff (N + 2)) ^ (2 * analyticZetaZeroMultiplicity rho + 3) / (N + 1 : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_left (pairedEtaLeadingCurrentLinearHeatReturn_after_midpoint_error_le rho N) (by positivity)
    _ ≤ (2 * (N + 1) : ℝ) * ((19 / 4) * pairedEtaLeadingCurrentMassConstant rho *
        (1 + pairedEtaLogTailCutoff (N + 2)) ^ (2 * analyticZetaZeroMultiplicity rho + 3) / (N + 1 : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by field_simp; ring

/-- The explicit two-part majorant for the full weighted linear-width
reconstruction error, including the actual midpoint term. -/
def pairedEtaCurrentLinearHeatErrorMajorant (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  (19 / 2) * pairedEtaLeadingCurrentMassConstant rho *
      ((1 + pairedEtaLogTailCutoff (N + 2)) ^ (2 * analyticZetaZeroMultiplicity rho + 3) / (N + 1 : ℝ) ^ 2) +
    (2 * (analyticZetaZeroMultiplicity rho : ℝ) / Real.sqrt Real.pi) *
      ((1 + pairedEtaLogTailCutoff (N + 2)) * pairedEtaCurrentMidpointEnvelope rho N / (N + 1 : ℝ))

/-- Every term of the explicit weighted error majorant is nonnegative. -/
theorem pairedEtaCurrentLinearHeatErrorMajorant_nonneg (rho : NontrivialZetaZero) (N : ℕ) :
    0 ≤ pairedEtaCurrentLinearHeatErrorMajorant rho N := by
  have hC := pairedEtaLeadingCurrentMassConstant_nonneg rho
  have hL := pairedEtaLogTailCutoff_nonneg (N + 2)
  have hE := pairedEtaCurrentMidpointEnvelope_nonneg rho N
  unfold pairedEtaCurrentLinearHeatErrorMajorant
  positivity

/-- The unchanged original current is reconstructed at linear heat width
with its full weighted error bounded by an explicit arithmetic majorant. -/
theorem pairedEtaLeadingCurrentLinearHeatReturn_weighted_error_le (rho : NontrivialZetaZero) (N : ℕ) :
    (2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho N -
      (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ)‖ ≤
      pairedEtaCurrentLinearHeatErrorMajorant rho N := by
  have ht : ‖pairedEtaLeadingCurrentLinearHeatReturn rho N - (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ)‖ ≤
      ‖pairedEtaLeadingCurrentLinearHeatReturn rho N - (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ) -
        pairedEtaLeadingCurrentLinearMidpointTerm rho N‖ + ‖pairedEtaLeadingCurrentLinearMidpointTerm rho N‖ := by
    calc
      _ = ‖(pairedEtaLeadingCurrentLinearHeatReturn rho N - (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ) -
        pairedEtaLeadingCurrentLinearMidpointTerm rho N) + pairedEtaLeadingCurrentLinearMidpointTerm rho N‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  calc
    _ ≤ (2 * N + 1 : ℝ) * (‖pairedEtaLeadingCurrentLinearHeatReturn rho N -
        (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ) - pairedEtaLeadingCurrentLinearMidpointTerm rho N‖ +
          ‖pairedEtaLeadingCurrentLinearMidpointTerm rho N‖) := mul_le_mul_of_nonneg_left ht (by positivity)
    _ = (2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho N -
        (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ) - pairedEtaLeadingCurrentLinearMidpointTerm rho N‖ +
          (2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearMidpointTerm rho N‖ := by ring
    _ ≤ (19 / 2) * pairedEtaLeadingCurrentMassConstant rho *
        (1 + pairedEtaLogTailCutoff (N + 2)) ^ (2 * analyticZetaZeroMultiplicity rho + 3) / (N + 1 : ℝ) ^ 2 +
      (2 * (analyticZetaZeroMultiplicity rho : ℝ) / Real.sqrt Real.pi) *
        ((1 + pairedEtaLogTailCutoff (N + 2)) * pairedEtaCurrentMidpointEnvelope rho N / (N + 1 : ℝ)) :=
      add_le_add (pairedEtaLeadingCurrentLinearHeatReturn_after_midpoint_weighted_error_le rho N)
        (pairedEtaLeadingCurrentLinearMidpointTerm_weighted_le rho N)
    _ = _ := by unfold pairedEtaCurrentLinearHeatErrorMajorant; ring

end

end RiemannGaussian
