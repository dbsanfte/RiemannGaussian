import RiemannGaussian.EtaCurrentReconstructionSchedule
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Summable weighted reconstruction of the completed eta current

The explicit simultaneous return approximates the unchanged completed
current with a summable first absolute-moment error. Its accumulated error
has a proved finite bound independent of the terminal arithmetic cutoff.
The weighted complex error series retains its sign and phase, and finite
absolute moments of the return and current differ by at most that bound.
No bound for either full absolute moment is assumed or proved here.
-/

open Complex Filter MeasureTheory Set Topology Asymptotics
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Every fixed logarithmic power in the reconstruction majorant is
summable after division by the square arithmetic cutoff. -/
theorem summable_pairedEtaCurrent_logPower_div_sq (k : ℕ) :
    Summable (fun N : ℕ ↦ (1 + pairedEtaLogTailCutoff (N + 2)) ^ k / (N + 1 : ℝ) ^ 2) := by
  let z : ℕ → ℝ := fun N ↦ Real.exp 1 * (2 * N + 5)
  have hz : Tendsto z atTop atTop :=
    (tendsto_atTop_add_const_right atTop 5
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2))).const_mul_atTop
        (Real.exp_pos 1)
  have hl := ((isLittleO_log_rpow_rpow_atTop (k : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto hz).bound (by norm_num : (0 : ℝ) < 1)
  have hs := ((Real.summable_one_div_nat_add_rpow 1 (3 / 2)).2 (by norm_num)).mul_left
    ((5 * Real.exp 1) ^ (1 / 2 : ℝ))
  refine hs.of_norm_bounded_eventually_nat ?_
  filter_upwards [hl] with N hN
  have hL := pairedEtaLogTailCutoff_nonneg (N + 2)
  have hx : 0 < (N + 1 : ℝ) := by positivity
  have hzpos : 0 < z N := by dsimp [z]; positivity
  have hlog : Real.log (z N) = 1 + pairedEtaLogTailCutoff (N + 2) := by
    dsimp [z, pairedEtaLogTailCutoff]
    rw [Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp]
    push_cast
    congr 2
    ring
  have hpow : (1 + pairedEtaLogTailCutoff (N + 2)) ^ k ≤ (z N) ^ (1 / 2 : ℝ) := by
    simpa only [Function.comp_apply, Real.rpow_natCast, hlog,
      Real.norm_of_nonneg (by positivity : 0 ≤ (1 + pairedEtaLogTailCutoff (N + 2)) ^ k),
      Real.norm_of_nonneg (Real.rpow_nonneg hzpos.le _), one_mul] using hN
  have hzle : z N ≤ (5 * Real.exp 1) * (N + 1 : ℝ) := by
    dsimp [z]
    have he := Real.exp_pos 1
    have hn := Nat.cast_nonneg (α := ℝ) N
    nlinarith
  have hrpow := Real.rpow_le_rpow hzpos.le hzle (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [Real.mul_rpow (by positivity) hx.le] at hrpow
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ ((5 * Real.exp 1) ^ (1 / 2 : ℝ) * (N + 1 : ℝ) ^ (1 / 2 : ℝ)) / (N + 1 : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (hpow.trans hrpow) (by positivity)
    _ = (5 * Real.exp 1) ^ (1 / 2 : ℝ) * (1 / (N + 1 : ℝ) ^ (3 / 2 : ℝ)) := by
      rw [mul_div_assoc, ← Real.rpow_natCast, ← Real.rpow_sub hx]
      rw [show (1 / 2 : ℝ) - (2 : ℕ) = -(3 / 2 : ℝ) by norm_num,
        Real.rpow_neg hx.le]
      simp only [one_div]
    _ = _ := by rw [abs_of_pos hx]

/-- The exact finite error budget supplied by the proved logarithmic series.
Its dependence on the zero is only through the explicit completion
constant and analytic multiplicity. -/
def pairedEtaCurrentWeightedReconstructionErrorBound (rho : NontrivialZetaZero) : ℝ :=
  2 * pairedEtaCurrentReconstructionErrorConstant rho *
    ∑' N : ℕ, (1 + pairedEtaLogTailCutoff (N + 2)) ^
      (2 * analyticZetaZeroMultiplicity rho + 2) / (N + 1 : ℝ) ^ 2

/-- The full weighted reconstruction error budget is nonnegative. -/
theorem pairedEtaCurrentWeightedReconstructionErrorBound_nonneg (rho : NontrivialZetaZero) :
    0 ≤ pairedEtaCurrentWeightedReconstructionErrorBound rho := by
  unfold pairedEtaCurrentWeightedReconstructionErrorBound
  apply mul_nonneg (mul_nonneg (by norm_num) (pairedEtaCurrentReconstructionErrorConstant_nonneg rho))
  exact tsum_nonneg fun N ↦ by
    have hL := pairedEtaLogTailCutoff_nonneg (N + 2)
    positivity

/-- The actual simultaneous return has a summable odd-weighted norm error
relative to the original leading current, for every actual nontrivial zero. -/
theorem summable_oddEndpoint_mul_norm_pairedEtaLeadingCurrentScheduledGapReturn_error
    (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦ (2 * N + 1 : ℝ) *
      ‖pairedEtaLeadingCurrentScheduledGapReturn rho N -
        (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ)‖) := by
  have hs := (summable_pairedEtaCurrent_logPower_div_sq
    (2 * analyticZetaZeroMultiplicity rho + 2)).mul_left
      (2 * pairedEtaCurrentReconstructionErrorConstant rho)
  apply hs.of_nonneg_of_le (fun N ↦ by positivity)
  intro N
  simpa only [mul_div_assoc] using pairedEtaLeadingCurrentScheduledGapReturn_weighted_error_le rho N

/-- The odd-weighted complex reconstruction error itself is summable;
the signed difference remains available upstream of the absolute bound. -/
theorem summable_oddEndpoint_smul_pairedEtaLeadingCurrentScheduledGapReturn_error
    (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦ (2 * N + 1 : ℝ) •
      (pairedEtaLeadingCurrentScheduledGapReturn rho N -
        (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ))) := by
  apply (summable_oddEndpoint_mul_norm_pairedEtaLeadingCurrentScheduledGapReturn_error rho).of_norm_bounded
  intro N
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * N + 1), le_refl]

/-- Accumulating the actual weighted reconstruction norm error over any
finite prefix stays below the same proved finite error budget. -/
theorem pairedEtaLeadingCurrentScheduledGapReturn_weighted_error_sum_le
    (rho : NontrivialZetaZero) (K : ℕ) :
    (∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) *
      ‖pairedEtaLeadingCurrentScheduledGapReturn rho N -
        (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ)‖) ≤
      pairedEtaCurrentWeightedReconstructionErrorBound rho := by
  have hD := pairedEtaCurrentReconstructionErrorConstant_nonneg rho
  have hs := (summable_pairedEtaCurrent_logPower_div_sq
    (2 * analyticZetaZeroMultiplicity rho + 2)).mul_left
      (2 * pairedEtaCurrentReconstructionErrorConstant rho)
  calc
    _ ≤ ∑ N ∈ Finset.range K, 2 * pairedEtaCurrentReconstructionErrorConstant rho *
        ((1 + pairedEtaLogTailCutoff (N + 2)) ^
          (2 * analyticZetaZeroMultiplicity rho + 2) / (N + 1 : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro N _
      simpa only [mul_div_assoc] using pairedEtaLeadingCurrentScheduledGapReturn_weighted_error_le rho N
    _ ≤ ∑' N : ℕ, 2 * pairedEtaCurrentReconstructionErrorConstant rho *
        ((1 + pairedEtaLogTailCutoff (N + 2)) ^
          (2 * analyticZetaZeroMultiplicity rho + 2) / (N + 1 : ℝ) ^ 2) := by
      apply hs.sum_le_tsum
      intro N _
      have hL := pairedEtaLogTailCutoff_nonneg (N + 2)
      positivity
    _ = _ := by rw [tsum_mul_left]; rfl

/-- Finite first absolute moments of the actual scheduled return and the
unchanged current differ by at most the same cutoff-independent error
budget. This is stability of reconstruction, not a bound for either moment. -/
theorem pairedEtaLeadingCurrentScheduledGapReturn_firstMoment_stability
    (rho : NontrivialZetaZero) (K : ℕ) :
    |(∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentScheduledGapReturn rho N‖) -
      (∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N|)| ≤
      pairedEtaCurrentWeightedReconstructionErrorBound rho := by
  calc
    _ = |∑ N ∈ Finset.range K, ((2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentScheduledGapReturn rho N‖ -
        (2 * N + 1 : ℝ) * |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N|)| := by
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ N ∈ Finset.range K, |(2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentScheduledGapReturn rho N‖ -
        (2 * N + 1 : ℝ) * (|pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N|)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) *
        ‖pairedEtaLeadingCurrentScheduledGapReturn rho N -
          (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ)‖ := by
      apply Finset.sum_le_sum
      intro N _
      have hw : (0 : ℝ) ≤ 2 * N + 1 := by positivity
      rw [← mul_sub, abs_mul, abs_of_nonneg hw]
      apply mul_le_mul_of_nonneg_left _ hw
      simpa only [Complex.norm_real, Real.norm_eq_abs] using
        abs_norm_sub_norm_le (pairedEtaLeadingCurrentScheduledGapReturn rho N)
          (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ)
    _ ≤ _ := pairedEtaLeadingCurrentScheduledGapReturn_weighted_error_sum_le rho K

end

end RiemannGaussian
