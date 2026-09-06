import RiemannGaussian.EtaCurrentPowerSum

/-!
# Unconditional growth bound for the actual weighted return moment

The original completed current and its actual linear-width return have
explicit finite first-moment bounds with exponent `|2 Re rho - 1| < 1`.
Both multiplicity branches are included. At the critical line the exact
signed cancellation is used separately. Consequently the return moment
divided by its cutoff tends to zero. A bound independent of cutoff, the
active RH-strength goal, is not proved by this sublinear estimate.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The explicit completion- and multiplicity-dependent amplitude in the
weighted current's horizontal power bound. -/
def pairedEtaCurrentGrowthAmplitude (rho : NontrivialZetaZero) : ℝ :=
  4 * (analyticZetaZeroMultiplicity rho : ℝ) *
    (pairedEtaCurrentMomentConstant (NontrivialZetaZero.conjugatePartner rho) ^ 2 + pairedEtaCurrentMomentConstant rho ^ 2)

/-- The current growth amplitude is nonnegative. -/
theorem pairedEtaCurrentGrowthAmplitude_nonneg (rho : NontrivialZetaZero) :
    0 ≤ pairedEtaCurrentGrowthAmplitude rho := by unfold pairedEtaCurrentGrowthAmplitude; positivity

/-- The unchanged current's weighted term has the explicit horizontal
displacement power at every arithmetic cutoff. -/
theorem pairedEtaLeadingCurrent_weighted_le_displacement_rpow (rho : NontrivialZetaZero) (N : ℕ) :
    (2 * N + 1 : ℝ) * |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N| ≤
      pairedEtaCurrentGrowthAmplitude rho * (N + 1 : ℝ) ^ (pairedEtaCurrentHorizontalDisplacement rho - 1) := by
  exact (pairedEtaLeadingCurrent_weighted_le_doubleDecay rho N).trans
    ((mul_le_mul_of_nonneg_left (pairedEtaCurrentDoubleDecayEnvelope_le_displacement_rpow rho N)
      (by positivity : 0 ≤ 4 * (analyticZetaZeroMultiplicity rho : ℝ))).trans_eq
        (by unfold pairedEtaCurrentGrowthAmplitude; ring))

/-- Off the critical line, every finite first absolute moment of the
original current has an explicit displacement-power upper bound. -/
theorem pairedEtaLeadingCurrent_firstMoment_growth_le_of_re_ne_half (rho : NontrivialZetaZero)
    (hrho : rho.1.re ≠ 1 / 2) (K : ℕ) :
    (∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N|) ≤
      (pairedEtaCurrentGrowthAmplitude rho / pairedEtaCurrentHorizontalDisplacement rho) *
        (K + 1 : ℝ) ^ pairedEtaCurrentHorizontalDisplacement rho := by
  have he := pairedEtaCurrentHorizontalDisplacement_pos rho hrho
  have he1 := (pairedEtaCurrentHorizontalDisplacement_bounds rho).2
  have hs := sum_range_nat_add_one_rpow_le
    (by linarith : -1 < pairedEtaCurrentHorizontalDisplacement rho - 1) (by linarith) K
  rw [sub_add_cancel] at hs
  calc
    _ ≤ ∑ N ∈ Finset.range K, pairedEtaCurrentGrowthAmplitude rho *
        (N + 1 : ℝ) ^ (pairedEtaCurrentHorizontalDisplacement rho - 1) :=
      Finset.sum_le_sum (fun N _ ↦ pairedEtaLeadingCurrent_weighted_le_displacement_rpow rho N)
    _ = pairedEtaCurrentGrowthAmplitude rho *
        ∑ N ∈ Finset.range K, (N + 1 : ℝ) ^ (pairedEtaCurrentHorizontalDisplacement rho - 1) := by rw [Finset.mul_sum]
    _ ≤ pairedEtaCurrentGrowthAmplitude rho *
        ((K + 1 : ℝ) ^ pairedEtaCurrentHorizontalDisplacement rho / pairedEtaCurrentHorizontalDisplacement rho) :=
      mul_le_mul_of_nonneg_left hs (pairedEtaCurrentGrowthAmplitude_nonneg rho)
    _ = _ := by ring

/-- On the critical line, the exact original-current cancellation leaves
only the already proved finite heat reconstruction budget for the return. -/
theorem pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_le_of_re_eq_half (rho : NontrivialZetaZero)
    (hrho : rho.1.re = 1 / 2) (K : ℕ) :
    (∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho N‖) ≤
      pairedEtaCurrentLinearHeatWeightedErrorBound rho := by
  have h := pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_stability rho K
  simp only [pairedEtaLeadingCurrent_eq_zero_of_re_eq_half rho hrho, abs_zero, mul_zero,
    Finset.sum_const_zero, sub_zero] at h
  exact (le_abs_self _).trans h

/-- Away from the critical line the actual return's weighted first moment
has the original current's explicit power bound plus one finite heat budget. -/
theorem pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_growth_le_of_re_ne_half (rho : NontrivialZetaZero)
    (hrho : rho.1.re ≠ 1 / 2) (K : ℕ) :
    (∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho N‖) ≤
      pairedEtaCurrentLinearHeatWeightedErrorBound rho +
        (pairedEtaCurrentGrowthAmplitude rho / pairedEtaCurrentHorizontalDisplacement rho) *
          (K + 1 : ℝ) ^ pairedEtaCurrentHorizontalDisplacement rho := by
  have h := (le_abs_self _).trans (pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_stability rho K)
  have hg := pairedEtaLeadingCurrent_firstMoment_growth_le_of_re_ne_half rho hrho K
  linarith

/-- An explicit finite growth constant for the original return. The
critical-line branch avoids division by zero and uses exact cancellation. -/
def pairedEtaCurrentReturnGrowthConstant (rho : NontrivialZetaZero) : ℝ :=
  pairedEtaCurrentLinearHeatWeightedErrorBound rho +
    if rho.1.re = 1 / 2 then 0 else pairedEtaCurrentGrowthAmplitude rho / pairedEtaCurrentHorizontalDisplacement rho

/-- The actual return's growth constant is nonnegative in both branches. -/
theorem pairedEtaCurrentReturnGrowthConstant_nonneg (rho : NontrivialZetaZero) :
    0 ≤ pairedEtaCurrentReturnGrowthConstant rho := by
  have hE := pairedEtaCurrentLinearHeatWeightedErrorBound_nonneg rho
  have hA := pairedEtaCurrentGrowthAmplitude_nonneg rho
  have he := (pairedEtaCurrentHorizontalDisplacement_bounds rho).1
  unfold pairedEtaCurrentReturnGrowthConstant
  split <;> positivity

/-- Every actual nontrivial zero has the same explicit all-cutoff power
law for its original weighted return moment; the exponent is its actual
horizontal displacement and is strictly less than one. -/
theorem pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_growth_le (rho : NontrivialZetaZero) (K : ℕ) :
    (∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho N‖) ≤
      pairedEtaCurrentReturnGrowthConstant rho * (K + 1 : ℝ) ^ pairedEtaCurrentHorizontalDisplacement rho := by
  by_cases hrho : rho.1.re = 1 / 2
  · simpa only [pairedEtaCurrentReturnGrowthConstant, if_pos hrho, add_zero, pairedEtaCurrentHorizontalDisplacement,
      hrho, if_true, show (2 : ℝ) * (1 / 2) - 1 = 0 by norm_num, abs_zero, Real.rpow_zero, mul_one] using
        pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_le_of_re_eq_half rho hrho K
  · have hE := pairedEtaCurrentLinearHeatWeightedErrorBound_nonneg rho
    have hp : 1 ≤ (K + 1 : ℝ) ^ pairedEtaCurrentHorizontalDisplacement rho :=
      Real.one_le_rpow (by have := Nat.cast_nonneg (α := ℝ) K; linarith)
        (pairedEtaCurrentHorizontalDisplacement_bounds rho).1
    apply (pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_growth_le_of_re_ne_half rho hrho K).trans
    unfold pairedEtaCurrentReturnGrowthConstant
    rw [if_neg hrho, add_mul]
    exact add_le_add (le_mul_of_one_le_right hE hp) le_rfl

/-- Unconditionally for every actual zero, the first absolute moment of
the unchanged return grows sublinearly in the arithmetic cutoff. This
normalization is explicit; it does not assert an unnormalized uniform bound. -/
theorem pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_div_cutoff_tendsto_zero (rho : NontrivialZetaZero) :
    Tendsto (fun K : ℕ ↦
      (∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho N‖) / (K + 1 : ℝ))
        atTop (𝓝 0) := by
  have hx : Tendsto (fun K : ℕ ↦ (K + 1 : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have he := (pairedEtaCurrentHorizontalDisplacement_bounds rho).2
  have hpow := (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - pairedEtaCurrentHorizontalDisplacement rho)).comp hx
  have hlim := hpow.const_mul (pairedEtaCurrentReturnGrowthConstant rho)
  simp only [mul_zero, neg_sub] at hlim
  apply squeeze_zero (fun K ↦ by positivity) _ hlim
  intro K
  have hK : 0 < (K + 1 : ℝ) := by positivity
  calc
    _ ≤ (pairedEtaCurrentReturnGrowthConstant rho * (K + 1 : ℝ) ^ pairedEtaCurrentHorizontalDisplacement rho) / (K + 1 : ℝ) :=
      div_le_div_of_nonneg_right (pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_growth_le rho K) hK.le
    _ = _ := by
      simp only [Function.comp_apply]
      rw [mul_div_assoc, Real.rpow_sub hK, Real.rpow_one]

end

end RiemannGaussian
