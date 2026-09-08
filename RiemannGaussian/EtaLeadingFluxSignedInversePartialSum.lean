import RiemannGaussian.EtaLeadingFluxSignedPartialSum
import RiemannGaussian.EtaCurrentFullInverseEnergy

/-!
# Signed partial sums of the complete reflected inverse energy

The unchanged weighted current and the complete moving inverse-energy sum
have a convergent signed difference and a fixed, proved error budget.
Consequently the off-critical lower power survives in the full inverse
representation. Every physical cutoff, completion coefficient, and reflected
channel is retained. An independent relative upper saving is still required.
-/

open Complex Filter Topology
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- The complete reflected inverse energy with the original odd weights. -/
def pairedEtaFullInverseEnergySignedPartialSum (rho : NontrivialZetaZero) (K : ℕ) : ℝ :=
  ∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * pairedEtaCurrentFullInverseEnergy rho N

/-- The signed transport error retains every actual current discrepancy. -/
theorem pairedEtaLeadingFluxSignedPartialSum_sub_fullInverse_eq_sum
    (rho : NontrivialZetaZero) (K : ℕ) :
    pairedEtaLeadingFluxSignedPartialSum rho K - pairedEtaFullInverseEnergySignedPartialSum rho K =
      ∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) *
        (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N - pairedEtaCurrentFullInverseEnergy rho N) := by
  simp only [pairedEtaLeadingFluxSignedPartialSum, pairedEtaFullInverseEnergySignedPartialSum,
    mul_sub, Finset.sum_sub_distrib]

/-- A uniform finite budget transports the signed sum without taking
absolute values of either current or inverse-energy summands separately. -/
theorem pairedEtaLeadingFluxSignedPartialSum_fullInverse_error_le
    (rho : NontrivialZetaZero) (K : ℕ) :
    |pairedEtaLeadingFluxSignedPartialSum rho K - pairedEtaFullInverseEnergySignedPartialSum rho K| ≤
      ∑' N : ℕ, pairedEtaCurrentZeroEnergyErrorEnvelope rho N := by
  rw [pairedEtaLeadingFluxSignedPartialSum_sub_fullInverse_eq_sum]
  calc
    _ ≤ ∑ N ∈ Finset.range K, |(2 * N + 1 : ℝ) *
        (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N - pairedEtaCurrentFullInverseEnergy rho N)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) *
        |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N - pairedEtaCurrentFullInverseEnergy rho N| := by
      apply Finset.sum_congr rfl
      intro N _
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * N + 1)]
    _ ≤ ∑ N ∈ Finset.range K, pairedEtaCurrentZeroEnergyErrorEnvelope rho N :=
      Finset.sum_le_sum (fun N _ ↦ pairedEtaLeadingCurrent_weighted_fullInverseEnergy_error_le rho N)
    _ ≤ _ := (summable_pairedEtaCurrentZeroEnergyErrorEnvelope rho).sum_le_tsum _
      (fun N _ ↦ pairedEtaCurrentZeroEnergyErrorEnvelope_nonneg rho N)

/-- The signed transport difference converges to its actual absolutely
summable error series; the finite budget does not discard this identity. -/
theorem pairedEtaLeadingFluxSignedPartialSum_sub_fullInverse_tendsto
    (rho : NontrivialZetaZero) :
    Tendsto (fun K : ℕ ↦ pairedEtaLeadingFluxSignedPartialSum rho K -
      pairedEtaFullInverseEnergySignedPartialSum rho K) atTop
        (𝓝 (∑' N : ℕ, (2 * N + 1 : ℝ) *
          (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N - pairedEtaCurrentFullInverseEnergy rho N))) := by
  have hs : Summable (fun N : ℕ ↦ (2 * N + 1 : ℝ) *
      (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N - pairedEtaCurrentFullInverseEnergy rho N)) := by
    apply Summable.of_norm
    apply (summable_oddEndpoint_mul_abs_pairedEtaLeadingCurrent_fullInverseEnergy_error rho).congr
    intro N
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * N + 1)]
  simpa only [pairedEtaLeadingFluxSignedPartialSum_sub_fullInverse_eq_sum] using hs.hasSum.tendsto_sum_nat

/-- The full inverse sum inherits the original signed lower power, with
the whole transport budget added to the finite initial allowance. -/
theorem pairedEtaFullInverseEnergySignedPartialSum_lower_with_offset
    (rho : NontrivialZetaZero) (hrho : rho.1.re ≠ 1 / 2) : ∃ N₀ : ℕ, ∀ K : ℕ,
      pairedEtaCurrentReturnGrowthLowerCoefficient rho * (K + 1 : ℝ) ^ pairedEtaCurrentHorizontalDisplacement rho -
        (pairedEtaLeadingFluxSignedGrowthOffset rho N₀ + ∑' N : ℕ, pairedEtaCurrentZeroEnergyErrorEnvelope rho N) ≤
          pairedEtaLeadingFluxSide rho * pairedEtaFullInverseEnergySignedPartialSum rho K := by
  obtain ⟨N₀, hN₀⟩ := pairedEtaLeadingFluxSignedPartialSum_lower_with_offset rho hrho
  refine ⟨N₀, fun K ↦ ?_⟩
  have h := (pairedEtaLeadingFluxSide_mul_le_abs rho
    (pairedEtaLeadingFluxSignedPartialSum rho K - pairedEtaFullInverseEnergySignedPartialSum rho K)).trans
      (pairedEtaLeadingFluxSignedPartialSum_fullInverse_error_le rho K)
  nlinarith [hN₀ K, h]

/-- The finite transport allowance is eventually absorbed by half the
positive lower coefficient. Any independent relative vanishing upper
factor for this complete inverse sum would contradict an off-critical zero. -/
theorem pairedEtaFullInverseEnergySignedPartialSum_power_lower_eventually
    (rho : NontrivialZetaZero) (hrho : rho.1.re ≠ 1 / 2) : ∀ᶠ K : ℕ in atTop,
      (pairedEtaCurrentReturnGrowthLowerCoefficient rho / 2) *
        (K + 1 : ℝ) ^ pairedEtaCurrentHorizontalDisplacement rho ≤
          pairedEtaLeadingFluxSide rho * pairedEtaFullInverseEnergySignedPartialSum rho K := by
  obtain ⟨N₀, hN₀⟩ := pairedEtaFullInverseEnergySignedPartialSum_lower_with_offset rho hrho
  have hc := pairedEtaCurrentReturnGrowthLowerCoefficient_pos rho hrho
  have hx : Tendsto (fun K : ℕ ↦ (K + 1 : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have ht := ((tendsto_rpow_atTop (pairedEtaCurrentHorizontalDisplacement_pos rho hrho)).comp hx).const_mul_atTop
    (by positivity : 0 < pairedEtaCurrentReturnGrowthLowerCoefficient rho / 2)
  filter_upwards [ht.eventually_ge_atTop
    (pairedEtaLeadingFluxSignedGrowthOffset rho N₀ + ∑' N : ℕ, pairedEtaCurrentZeroEnergyErrorEnvelope rho N)] with K hK
  dsimp only [Function.comp_apply] at hK
  nlinarith [hN₀ K]

end

end RiemannGaussian
