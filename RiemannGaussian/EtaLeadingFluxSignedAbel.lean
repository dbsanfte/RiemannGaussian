import RiemannGaussian.EtaLeadingFluxSignedPartialSum

/-!
# Exact signed summation by parts for the actual eta current

The weighted leading current equals the full signed energy Abel expression
minus two proved summable corrections: increment energy and remainder flux.
The terminal weighted energy is retained explicitly. Consequently this Abel
expression inherits the off-critical signed power lower bound. Telescoping
the unweighted energy, which tends to zero, supplies no bound on this
weighted expression.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

private theorem odd_weight_sum_difference (f : ℕ → ℝ) (K : ℕ) :
    (∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * (f N - f (N + 1))) =
      f 0 + 2 * (∑ N ∈ Finset.range K, f (N + 1)) - (2 * K + 1 : ℝ) * f K := by
  induction K with
  | zero => simp
  | succ K ih =>
    simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    rw [ih]
    ring

/-- The signed energy expression after exact summation by parts. Its
terminal energy carries the original growing odd endpoint weight. -/
def pairedEtaLeadingFluxEnergyAbelSum (rho : NontrivialZetaZero) (K : ℕ) : ℝ :=
  pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference rho 0 +
    2 * (∑ N ∈ Finset.range K,
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference rho (N + 1)) -
    (2 * K + 1 : ℝ) *
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference rho K

/-- The actual signed corrections omitted from the leading flux:
the increment energy and the arithmetic remainder flux. -/
def pairedEtaLeadingFluxAbelCorrection (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteIncrementEnergyDifference rho N +
    pairedEtaTopPrefixFiniteEnergyRemainderFlux rho N

/-- The entire correction has a finite weighted absolute total at
every actual zero, with no independent-current bound assumed. -/
theorem summable_oddEndpoint_mul_abs_pairedEtaLeadingFluxAbelCorrection (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦ (2 * N + 1 : ℝ) * |pairedEtaLeadingFluxAbelCorrection rho N|) := by
  have hI := summable_oddEndpoint_mul_abs_topPrefixFiniteIncrementEnergyDifference rho
  have hR := summable_oddEndpoint_mul_abs_topPrefixFiniteEnergyRemainderFlux rho
  push_cast at hI hR
  apply (hI.add hR).of_nonneg_of_le (fun N ↦ by positivity)
  intro N
  simpa only [pairedEtaLeadingFluxAbelCorrection, mul_add] using
    mul_le_mul_of_nonneg_left
      (abs_add_le
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteIncrementEnergyDifference rho N)
        (pairedEtaTopPrefixFiniteEnergyRemainderFlux rho N))
      (by positivity : (0 : ℝ) ≤ 2 * N + 1)

/-- Exact signed conservation at every finite cutoff, retaining the
terminal boundary and both corrections before taking a norm or limit. -/
theorem pairedEtaLeadingFluxSignedPartialSum_add_correction_eq_abel
    (rho : NontrivialZetaZero) (K : ℕ) :
    pairedEtaLeadingFluxSignedPartialSum rho K +
      (∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * pairedEtaLeadingFluxAbelCorrection rho N) =
        pairedEtaLeadingFluxEnergyAbelSum rho K := by
  have hstep (N : ℕ) : pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N +
      pairedEtaLeadingFluxAbelCorrection rho N =
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference rho N -
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference rho (N + 1) := by
    have h := topPrefixFiniteEnergyWork_eq_incrementEnergyDifference_add_flux rho N
    rw [topPrefixFiniteEnergyFlux_eq_leading_add_remainder] at h
    dsimp only [pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork] at h
    dsimp only [pairedEtaLeadingFluxAbelCorrection]
    linarith
  calc
    _ = ∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) *
        (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N + pairedEtaLeadingFluxAbelCorrection rho N) := by
      simp only [pairedEtaLeadingFluxSignedPartialSum, mul_add, Finset.sum_add_distrib]
    _ = ∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) *
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference rho N -
          pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference rho (N + 1)) := by
      apply Finset.sum_congr rfl
      intro N _
      rw [hstep]
    _ = _ := odd_weight_sum_difference _ K

/-- The finite total correction used in the signed energy comparison. -/
def pairedEtaLeadingFluxAbelErrorBudget (rho : NontrivialZetaZero) : ℝ :=
  ∑' N : ℕ, (2 * N + 1 : ℝ) * |pairedEtaLeadingFluxAbelCorrection rho N|

/-- Every finite signed current is within one fixed finite budget of
the full energy Abel expression, including its terminal weighted energy. -/
theorem pairedEtaLeadingFluxSignedPartialSum_abel_error_le (rho : NontrivialZetaZero) (K : ℕ) :
    |pairedEtaLeadingFluxSignedPartialSum rho K - pairedEtaLeadingFluxEnergyAbelSum rho K| ≤
      pairedEtaLeadingFluxAbelErrorBudget rho := by
  rw [← pairedEtaLeadingFluxSignedPartialSum_add_correction_eq_abel, sub_add_cancel_left, abs_neg]
  calc
    _ ≤ ∑ N ∈ Finset.range K, |(2 * N + 1 : ℝ) * pairedEtaLeadingFluxAbelCorrection rho N| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * |pairedEtaLeadingFluxAbelCorrection rho N| := by
      apply Finset.sum_congr rfl
      intro N _
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * N + 1)]
    _ ≤ _ := (summable_oddEndpoint_mul_abs_pairedEtaLeadingFluxAbelCorrection rho).sum_le_tsum _
      (fun N _ ↦ by positivity)

/-- The difference between the two signed representations converges
to the actual signed total correction; the phase-bearing energy identity
has therefore not been replaced merely by a triangle estimate. -/
theorem pairedEtaLeadingFluxEnergyAbelSum_sub_current_tendsto (rho : NontrivialZetaZero) :
    Tendsto (fun K : ℕ ↦ pairedEtaLeadingFluxEnergyAbelSum rho K - pairedEtaLeadingFluxSignedPartialSum rho K)
      atTop (𝓝 (∑' N : ℕ, (2 * N + 1 : ℝ) * pairedEtaLeadingFluxAbelCorrection rho N)) := by
  have hs : Summable (fun N : ℕ ↦ (2 * N + 1 : ℝ) * pairedEtaLeadingFluxAbelCorrection rho N) := by
    apply Summable.of_norm
    apply (summable_oddEndpoint_mul_abs_pairedEtaLeadingFluxAbelCorrection rho).congr
    intro N
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * N + 1)]
  convert hs.hasSum.tendsto_sum_nat using 1
  ext K
  rw [← pairedEtaLeadingFluxSignedPartialSum_add_correction_eq_abel]
  ring

/-- Exact summation by parts preserves the same unavoidable signed
displacement power, with only the proved finite correction budget added. -/
theorem pairedEtaLeadingFluxEnergyAbelSum_lower_with_offset (rho : NontrivialZetaZero)
    (hrho : rho.1.re ≠ 1 / 2) : ∃ N₀ : ℕ, ∀ K : ℕ,
      pairedEtaCurrentReturnGrowthLowerCoefficient rho * (K + 1 : ℝ) ^ pairedEtaCurrentHorizontalDisplacement rho -
        (pairedEtaLeadingFluxSignedGrowthOffset rho N₀ + pairedEtaLeadingFluxAbelErrorBudget rho) ≤
          pairedEtaLeadingFluxSide rho * pairedEtaLeadingFluxEnergyAbelSum rho K := by
  obtain ⟨N₀, hN₀⟩ := pairedEtaLeadingFluxSignedPartialSum_lower_with_offset rho hrho
  refine ⟨N₀, fun K ↦ ?_⟩
  have h := (pairedEtaLeadingFluxSide_mul_le_abs rho
    (pairedEtaLeadingFluxSignedPartialSum rho K - pairedEtaLeadingFluxEnergyAbelSum rho K)).trans
      (pairedEtaLeadingFluxSignedPartialSum_abel_error_le rho K)
  nlinarith [hN₀ K, h]

/-- The complete energy Abel expression also diverges in the correct
side direction. The unweighted decay of the energy cannot justify dropping
the terminal weighted boundary or claiming this expression is bounded. -/
theorem pairedEtaLeadingFluxEnergyAbelSum_tendsto_side_infinity_of_re_ne_half
    (rho : NontrivialZetaZero) (hrho : rho.1.re ≠ 1 / 2) : Tendsto
      (fun K : ℕ ↦ pairedEtaLeadingFluxSide rho * pairedEtaLeadingFluxEnergyAbelSum rho K) atTop atTop := by
  have ht := tendsto_atTop_add_const_right atTop (-pairedEtaLeadingFluxAbelErrorBudget rho)
    (pairedEtaLeadingFluxSignedPartialSum_tendsto_side_infinity_of_re_ne_half rho hrho)
  apply tendsto_atTop_mono' atTop _ ht
  filter_upwards [] with K
  have h := (pairedEtaLeadingFluxSide_mul_le_abs rho
    (pairedEtaLeadingFluxSignedPartialSum rho K - pairedEtaLeadingFluxEnergyAbelSum rho K)).trans
      (pairedEtaLeadingFluxSignedPartialSum_abel_error_le rho K)
  nlinarith

end

end RiemannGaussian
