import RiemannGaussian.EtaCurrentReturnSharpGrowth

/-!
# Signed weighted partial sums of the actual eta leading current

The principal endpoint has a fixed eventual sign at an off-critical zero.
Its positive displacement-power lower bound survives in the signed partial
sums of the unchanged current, with a finite initial-segment allowance and
the already proved summable arithmetic error. The cancellation deficit of
the actual current is itself summable: signs cannot erase that power by
cancellation across cutoffs. No independent upper bound is proved here.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The side of the critical line supplying the slower principal channel. -/
def pairedEtaLeadingFluxSide (rho : NontrivialZetaZero) : ℝ :=
  if rho.1.re ≤ 1 / 2 then -1 else 1

/-- The retained side has unit absolute value. -/
theorem abs_pairedEtaLeadingFluxSide (rho : NontrivialZetaZero) :
    |pairedEtaLeadingFluxSide rho| = 1 := by
  unfold pairedEtaLeadingFluxSide
  split <;> norm_num

/-- The actual signed current, with its literal odd endpoint weight. -/
def pairedEtaLeadingFluxSignedPartialSum (rho : NontrivialZetaZero) (K : ℕ) : ℝ :=
  ∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N

/-- The signed principal partial sum keeps the same endpoints and weights. -/
def pairedEtaLeadingFluxPrincipalPartialSum (rho : NontrivialZetaZero) (K : ℕ) : ℝ :=
  ∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * pairedEtaCurrentPrincipalEndpoint rho N

/-- The total arithmetic comparison error, finite by upstream summability. -/
def pairedEtaLeadingFluxPrincipalErrorBudget (rho : NontrivialZetaZero) : ℝ :=
  ∑' N : ℕ, (2 * N + 1 : ℝ) *
    |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N - pairedEtaCurrentPrincipalEndpoint rho N|

/-- The original and principal signed sums differ by a fixed finite budget. -/
theorem pairedEtaLeadingFluxSignedPartialSum_principal_error_le (rho : NontrivialZetaZero) (K : ℕ) :
    |pairedEtaLeadingFluxSignedPartialSum rho K - pairedEtaLeadingFluxPrincipalPartialSum rho K| ≤
      pairedEtaLeadingFluxPrincipalErrorBudget rho := by
  unfold pairedEtaLeadingFluxSignedPartialSum pairedEtaLeadingFluxPrincipalPartialSum
    pairedEtaLeadingFluxPrincipalErrorBudget
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ N ∈ Finset.range K, |(2 * N + 1 : ℝ) * pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N -
        (2 * N + 1 : ℝ) * pairedEtaCurrentPrincipalEndpoint rho N| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) *
        |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N - pairedEtaCurrentPrincipalEndpoint rho N| := by
      apply Finset.sum_congr rfl
      intro N _
      rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * N + 1)]
    _ ≤ _ := (summable_oddEndpoint_mul_abs_pairedEtaLeadingCurrent_principal_error rho).sum_le_tsum _
      (fun N _ ↦ by positivity)

/-- Off the critical line the positive dominant bracket fixes the actual
principal sign eventually, before any cutoff sums are taken. -/
theorem pairedEtaCurrentPrincipalEndpoint_side_eq_abs_eventually (rho : NontrivialZetaZero)
    (hrho : rho.1.re ≠ 1 / 2) : ∀ᶠ N : ℕ in atTop,
      pairedEtaLeadingFluxSide rho * pairedEtaCurrentPrincipalEndpoint rho N =
        |pairedEtaCurrentPrincipalEndpoint rho N| := by
  have hsmall := (tendsto_pairedEtaCurrent_relative_recessive_zero rho hrho).eventually_lt_const
    (pairedEtaCurrentDominantCoefficient_pos rho)
  filter_upwards [hsmall] with N hN
  have hpos : 0 ≤ pairedEtaLogTailShiftIncrement (N + 1) *
      Real.exp ((pairedEtaCurrentHorizontalDisplacement rho - 1) * pairedEtaLogTailCutoff (N + 2)) *
        (pairedEtaCurrentDominantCoefficient rho - pairedEtaCurrentRecessiveCoefficient rho *
          Real.exp (-2 * pairedEtaCurrentHorizontalDisplacement rho * pairedEtaLogTailCutoff (N + 2))) :=
    mul_nonneg (mul_nonneg (pairedEtaLogTailShiftIncrement_pos _).le (Real.exp_pos _).le)
      (sub_nonneg.mpr hN.le)
  rw [pairedEtaCurrentPrincipalEndpoint_eq_dominant_factor]
  unfold pairedEtaLeadingFluxSide
  split <;> simp only [neg_one_mul, neg_neg, one_mul, abs_neg, abs_of_nonneg hpos]

/-- The principal cancellation deficit vanishes beyond a finite cutoff.
The earlier cutoffs are retained rather than assumed to have the final sign. -/
theorem summable_pairedEtaLeadingFlux_principal_cancellationDeficit (rho : NontrivialZetaZero)
    (hrho : rho.1.re ≠ 1 / 2) : Summable (fun N : ℕ ↦ (2 * N + 1 : ℝ) *
      (|pairedEtaCurrentPrincipalEndpoint rho N| -
        pairedEtaLeadingFluxSide rho * pairedEtaCurrentPrincipalEndpoint rho N)) := by
  apply (summable_congr_atTop (show (fun N : ℕ ↦ (2 * N + 1 : ℝ) *
      (|pairedEtaCurrentPrincipalEndpoint rho N| - pairedEtaLeadingFluxSide rho *
        pairedEtaCurrentPrincipalEndpoint rho N)) =ᶠ[atTop] (fun _ ↦ 0) from ?_)).2 summable_zero
  filter_upwards [pairedEtaCurrentPrincipalEndpoint_side_eq_abs_eventually rho hrho] with N hN
  rw [hN, sub_self, mul_zero]

/-- The total amount lost by replacing the oriented actual current by its
absolute value. Each summand is nonnegative, but its total will be finite. -/
def pairedEtaLeadingFluxCancellationDeficit (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  (2 * N + 1 : ℝ) * (|pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N| -
    pairedEtaLeadingFluxSide rho * pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N)

/-- An oriented real value never exceeds its absolute value. -/
theorem pairedEtaLeadingFluxSide_mul_le_abs (rho : NontrivialZetaZero) (x : ℝ) :
    pairedEtaLeadingFluxSide rho * x ≤ |x| := by
  calc
    _ ≤ |pairedEtaLeadingFluxSide rho * x| := le_abs_self _
    _ = |x| := by rw [abs_mul, abs_pairedEtaLeadingFluxSide, one_mul]

/-- The cancellation deficit is nonnegative at each actual cutoff. -/
theorem pairedEtaLeadingFluxCancellationDeficit_nonneg (rho : NontrivialZetaZero) (N : ℕ) :
    0 ≤ pairedEtaLeadingFluxCancellationDeficit rho N :=
  mul_nonneg (by positivity) (sub_nonneg.mpr (pairedEtaLeadingFluxSide_mul_le_abs rho _))

/-- The actual negative mass in the eventual orientation has a finite
first moment. Thus cancellation across cutoffs cannot absorb the off-line
displacement power; only a finite total cancellation allowance remains. -/
theorem summable_pairedEtaLeadingFluxCancellationDeficit (rho : NontrivialZetaZero)
    (hrho : rho.1.re ≠ 1 / 2) : Summable (pairedEtaLeadingFluxCancellationDeficit rho) := by
  have hmajor := ((summable_oddEndpoint_mul_abs_pairedEtaLeadingCurrent_principal_error rho).mul_left 2).add
    (summable_pairedEtaLeadingFlux_principal_cancellationDeficit rho hrho)
  apply hmajor.of_nonneg_of_le (pairedEtaLeadingFluxCancellationDeficit_nonneg rho)
  intro N
  have hnorm := abs_sub_abs_le_abs_sub (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N)
    (pairedEtaCurrentPrincipalEndpoint rho N)
  have hside := pairedEtaLeadingFluxSide_mul_le_abs rho
    (pairedEtaCurrentPrincipalEndpoint rho N - pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N)
  rw [abs_sub_comm] at hside
  have hterm : |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N| -
      pairedEtaLeadingFluxSide rho * pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N ≤
    2 * |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N - pairedEtaCurrentPrincipalEndpoint rho N| +
      (|pairedEtaCurrentPrincipalEndpoint rho N| -
        pairedEtaLeadingFluxSide rho * pairedEtaCurrentPrincipalEndpoint rho N) := by nlinarith
  have h := mul_le_mul_of_nonneg_left hterm (by positivity : (0 : ℝ) ≤ 2 * N + 1)
  dsimp only [pairedEtaLeadingFluxCancellationDeficit]
  nlinarith [h]

/-- Signed and absolute current partial sums differ by a convergent finite
cancellation allowance, not by another growing cutoff power. -/
theorem pairedEtaLeadingFluxSignedPartialSum_cancellationDeficit_tendsto (rho : NontrivialZetaZero)
    (hrho : rho.1.re ≠ 1 / 2) : Tendsto (fun K : ℕ ↦
      (∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N|) -
        pairedEtaLeadingFluxSide rho * pairedEtaLeadingFluxSignedPartialSum rho K)
      atTop (𝓝 (∑' N : ℕ, pairedEtaLeadingFluxCancellationDeficit rho N)) := by
  convert (summable_pairedEtaLeadingFluxCancellationDeficit rho hrho).hasSum.tendsto_sum_nat using 1
  ext K
  simp only [pairedEtaLeadingFluxSignedPartialSum, pairedEtaLeadingFluxCancellationDeficit,
    Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro N _
  ring

/-- The finite allowance for signed growth includes the true principal
error, the complete pre-sign cancellation deficit, and the initial power sum. -/
def pairedEtaLeadingFluxSignedGrowthOffset (rho : NontrivialZetaZero) (N₀ : ℕ) : ℝ :=
  pairedEtaLeadingFluxPrincipalErrorBudget rho +
    (∑' N : ℕ, (2 * N + 1 : ℝ) * (|pairedEtaCurrentPrincipalEndpoint rho N| -
      pairedEtaLeadingFluxSide rho * pairedEtaCurrentPrincipalEndpoint rho N)) +
    pairedEtaCurrentReturnGrowthLowerCoefficient rho +
    ∑ N ∈ Finset.range N₀, pairedEtaCurrentPrincipalGrowthFloor rho *
      (N + 1 : ℝ) ^ (pairedEtaCurrentHorizontalDisplacement rho - 1)

/-- Every hypothetical off-critical zero forces signed power growth of
the actual current, with all early cutoffs and arithmetic errors paid. -/
theorem pairedEtaLeadingFluxSignedPartialSum_lower_with_offset (rho : NontrivialZetaZero)
    (hrho : rho.1.re ≠ 1 / 2) : ∃ N₀ : ℕ, ∀ K : ℕ,
      pairedEtaCurrentReturnGrowthLowerCoefficient rho * (K + 1 : ℝ) ^ pairedEtaCurrentHorizontalDisplacement rho -
        pairedEtaLeadingFluxSignedGrowthOffset rho N₀ ≤
          pairedEtaLeadingFluxSide rho * pairedEtaLeadingFluxSignedPartialSum rho K := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (pairedEtaCurrentPrincipalEndpoint_weighted_lower_eventually rho hrho)
  refine ⟨N₀, fun K ↦ ?_⟩
  have he := pairedEtaCurrentHorizontalDisplacement_pos rho hrho
  have he1 := (pairedEtaCurrentHorizontalDisplacement_bounds rho).2
  have hc := (pairedEtaCurrentPrincipalGrowthFloor_pos rho).le
  have hsum := sum_range_le_sum_add_initial_of_eventual_bound
    (fun N ↦ mul_nonneg hc (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ N + 1) _))
    (fun N ↦ by positivity : ∀ N : ℕ, 0 ≤ (2 * N + 1 : ℝ) * |pairedEtaCurrentPrincipalEndpoint rho N|) N₀ hN₀ K
  have hpow := mul_le_mul_of_nonneg_left
    (sub_one_div_le_sum_range_nat_add_one_rpow (by linarith : -1 < pairedEtaCurrentHorizontalDisplacement rho - 1)
      (by linarith) K) hc
  rw [sub_add_cancel, Finset.mul_sum] at hpow
  have hcancel := (summable_pairedEtaLeadingFlux_principal_cancellationDeficit rho hrho).sum_le_tsum
    (Finset.range K) (fun N _ ↦ mul_nonneg (by positivity)
      (sub_nonneg.mpr (pairedEtaLeadingFluxSide_mul_le_abs rho _)))
  have hid : (∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) *
      (|pairedEtaCurrentPrincipalEndpoint rho N| -
        pairedEtaLeadingFluxSide rho * pairedEtaCurrentPrincipalEndpoint rho N)) =
      (∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * |pairedEtaCurrentPrincipalEndpoint rho N|) -
        pairedEtaLeadingFluxSide rho * pairedEtaLeadingFluxPrincipalPartialSum rho K := by
    simp only [pairedEtaLeadingFluxPrincipalPartialSum, Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro N _
    ring
  rw [hid] at hcancel
  have herr := (pairedEtaLeadingFluxSide_mul_le_abs rho
    (pairedEtaLeadingFluxPrincipalPartialSum rho K - pairedEtaLeadingFluxSignedPartialSum rho K)).trans
      (by simpa only [abs_sub_comm] using pairedEtaLeadingFluxSignedPartialSum_principal_error_le rho K)
  unfold pairedEtaLeadingFluxSignedGrowthOffset pairedEtaCurrentReturnGrowthLowerCoefficient
  have halg : pairedEtaCurrentPrincipalGrowthFloor rho / pairedEtaCurrentHorizontalDisplacement rho *
      (K + 1 : ℝ) ^ pairedEtaCurrentHorizontalDisplacement rho =
    pairedEtaCurrentPrincipalGrowthFloor rho *
      (((K + 1 : ℝ) ^ pairedEtaCurrentHorizontalDisplacement rho - 1) / pairedEtaCurrentHorizontalDisplacement rho) +
      pairedEtaCurrentPrincipalGrowthFloor rho / pairedEtaCurrentHorizontalDisplacement rho := by ring
  rw [halg]
  nlinarith [hsum, hpow, hcancel, herr]

/-- The oriented signed current tends to positive infinity off the
critical line. This proves the divergence side of the proposed contradiction. -/
theorem pairedEtaLeadingFluxSignedPartialSum_tendsto_side_infinity_of_re_ne_half
    (rho : NontrivialZetaZero) (hrho : rho.1.re ≠ 1 / 2) : Tendsto
      (fun K : ℕ ↦ pairedEtaLeadingFluxSide rho * pairedEtaLeadingFluxSignedPartialSum rho K) atTop atTop := by
  obtain ⟨N₀, hN₀⟩ := pairedEtaLeadingFluxSignedPartialSum_lower_with_offset rho hrho
  have hx : Tendsto (fun K : ℕ ↦ (K + 1 : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have ht := ((tendsto_rpow_atTop (pairedEtaCurrentHorizontalDisplacement_pos rho hrho)).comp hx).const_mul_atTop
    (pairedEtaCurrentReturnGrowthLowerCoefficient_pos rho hrho)
  exact tendsto_atTop_mono' atTop (Eventually.of_forall hN₀)
    (tendsto_atTop_add_const_right atTop (-pairedEtaLeadingFluxSignedGrowthOffset rho N₀) ht)

/-- Right of the critical line, the original signed partial sum tends
to positive infinity without an absolute value around its summands. -/
theorem pairedEtaLeadingFluxSignedPartialSum_tendsto_atTop_of_half_lt_re
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (pairedEtaLeadingFluxSignedPartialSum rho) atTop atTop := by
  simpa only [pairedEtaLeadingFluxSide, if_neg (not_le.mpr hrho), one_mul] using
    pairedEtaLeadingFluxSignedPartialSum_tendsto_side_infinity_of_re_ne_half rho (ne_of_gt hrho)

/-- The finite offset is eventually absorbed by half the proved power
coefficient. Any independent upper estimate smaller than this rate would
already contradict an off-critical zero; boundedness is not required. -/
theorem pairedEtaLeadingFluxSignedPartialSum_power_lower_eventually (rho : NontrivialZetaZero)
    (hrho : rho.1.re ≠ 1 / 2) : ∀ᶠ K : ℕ in atTop,
      (pairedEtaCurrentReturnGrowthLowerCoefficient rho / 2) *
        (K + 1 : ℝ) ^ pairedEtaCurrentHorizontalDisplacement rho ≤
          pairedEtaLeadingFluxSide rho * pairedEtaLeadingFluxSignedPartialSum rho K := by
  obtain ⟨N₀, hN₀⟩ := pairedEtaLeadingFluxSignedPartialSum_lower_with_offset rho hrho
  have hc := pairedEtaCurrentReturnGrowthLowerCoefficient_pos rho hrho
  have hx : Tendsto (fun K : ℕ ↦ (K + 1 : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have ht := ((tendsto_rpow_atTop (pairedEtaCurrentHorizontalDisplacement_pos rho hrho)).comp hx).const_mul_atTop
    (by positivity : 0 < pairedEtaCurrentReturnGrowthLowerCoefficient rho / 2)
  filter_upwards [ht.eventually_ge_atTop (pairedEtaLeadingFluxSignedGrowthOffset rho N₀)] with K hK
  dsimp only [Function.comp_apply] at hK
  nlinarith [hN₀ K]

/-- Left of the critical line, the original signed partial sum tends
to negative infinity. Reflection is retained in the direction of divergence. -/
theorem pairedEtaLeadingFluxSignedPartialSum_tendsto_atBot_of_re_lt_half
    (rho : NontrivialZetaZero) (hrho : rho.1.re < 1 / 2) :
    Tendsto (pairedEtaLeadingFluxSignedPartialSum rho) atTop atBot := by
  have h := pairedEtaLeadingFluxSignedPartialSum_tendsto_side_infinity_of_re_ne_half rho (ne_of_lt hrho)
  simpa only [pairedEtaLeadingFluxSide, if_pos hrho.le, neg_one_mul, Function.comp_def, neg_neg] using
    tendsto_neg_atTop_atBot.comp h

/-- Bounded signed partial sums characterize the critical line for this
actual current. This is a conditional criterion; it does not establish the
independent bound required for a zero whose real part is unknown. -/
theorem pairedEtaLeadingFluxSignedPartialSum_bounded_iff_re_eq_half (rho : NontrivialZetaZero) :
    (∃ C : ℝ, ∀ K : ℕ, |pairedEtaLeadingFluxSignedPartialSum rho K| ≤ C) ↔ rho.1.re = 1 / 2 := by
  constructor
  · rintro ⟨C, hC⟩
    by_contra hrho
    have ht := pairedEtaLeadingFluxSignedPartialSum_tendsto_side_infinity_of_re_ne_half rho hrho
    obtain ⟨K, hK⟩ := (ht.eventually_ge_atTop (C + 1)).exists
    have hle := (pairedEtaLeadingFluxSide_mul_le_abs rho (pairedEtaLeadingFluxSignedPartialSum rho K)).trans (hC K)
    linarith
  · intro hrho
    have hs := (summable_oddEndpoint_mul_abs_topPrefixFiniteEnergyLeadingFlux_iff_re_eq_half rho).2 hrho
    push_cast at hs
    refine ⟨∑' N : ℕ, (2 * N + 1 : ℝ) * |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N|, fun K ↦ ?_⟩
    calc
      _ ≤ ∑ N ∈ Finset.range K, |(2 * N + 1 : ℝ) * pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N| := by
        apply Finset.sum_congr rfl
        intro N _
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * N + 1)]
      _ ≤ _ := hs.sum_le_tsum _ (fun N _ ↦ by positivity)

end

end RiemannGaussian
