import RiemannGaussian.EtaMoebiusParityCovariance
import RiemannGaussian.EtaMoebiusRefinedHeadDecay

/-!
# The unchanged zero bound in the signed near-parity coordinates

The simplest original dyadic grid already suffices for the exact parity
rewrite. Its full far-period contribution tends to zero. The canonical
deficit and every actual zero displacement are bounded by the signed
near-parity energy plus a proved vanishing allowance. The near-parity
energy's decay is the remaining theorem, not a premise inserted here.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The original logarithmic Möbius family's unchanged signed near-parity energy on the unrefined dyadic grid. -/
def pairedEtaDyadicMoebiusNearParityEnergy (k : ℕ) : ℝ :=
  pairedEtaMoebiusNearParityEnergy (pairedEtaDyadicTranslateDimension k) (k + 1)
    (pairedEtaMoebiusTrialLogWeight (k + 1))

/-- All head, grid, ridge, and genuine far-parity costs accompanying the original near-parity integral. -/
def pairedEtaDyadicMoebiusParityAllowance (k : ℕ) : ℝ :=
  pairedEtaDyadicMoebiusExteriorAllowance k + pairedEtaDyadicMoebiusTrialAllowance k / 2

/-- The entire original exterior is bounded by its near-parity integral and half of the existing vanishing arithmetic allowance. -/
theorem pairedEtaDyadicMoebiusRefinedExteriorEnergy_zero_le_near (k : ℕ) :
    pairedEtaDyadicMoebiusRefinedExteriorEnergy k 0 ≤
      pairedEtaDyadicMoebiusNearParityEnergy k + pairedEtaDyadicMoebiusTrialAllowance k / 2 := by
  have h := integral_pairedEtaMoebiusGrid_exterior_le_near_add_allowance
    (pairedEtaDyadicTranslateDimension_pos k) (pairedEtaDyadicMoebiusTrial_cutoff_le_dimension k)
    (fun _ hn ↦ abs_pairedEtaMoebiusTrialLogWeight_le hn)
  simpa only [pairedEtaDyadicMoebiusRefinedExteriorEnergy, zero_add, mul_one,
    pairedEtaDyadicMoebiusNearParityEnergy, pairedEtaDyadicMoebiusTrialAllowance,
    pairedEtaDyadicTranslateDimension, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one,
    div_mul_eq_div_div_swap] using h

/-- Every cost outside the signed near-parity energy tends to zero on the original stages, with no refinement schedule to choose. -/
theorem pairedEtaDyadicMoebiusParityAllowance_tendsto_zero :
    Tendsto pairedEtaDyadicMoebiusParityAllowance atTop (𝓝 0) := by
  change Tendsto (fun k : ℕ ↦ pairedEtaDyadicMoebiusExteriorAllowance k +
    pairedEtaDyadicMoebiusTrialAllowance k / 2) atTop (𝓝 0)
  simpa only [zero_div, add_zero] using
    pairedEtaDyadicMoebiusExteriorAllowance_tendsto_zero.add
      (pairedEtaDyadicMoebiusTrialAllowance_tendsto_zero.div_const 2)

/-- The original canonical deficit is bounded by the complete signed near-parity integral with all remaining costs proved vanishing. -/
theorem pairedEtaDyadicTranslateDeficit_le_moebius_nearParity {k : ℕ} (hk : 7 ≤ k) :
    pairedEtaDyadicTranslateDeficit k ≤ pairedEtaDyadicMoebiusNearParityEnergy k +
      pairedEtaDyadicMoebiusParityAllowance k := by
  have h := pairedEtaDyadicTranslateDeficit_le_moebius_exterior hk 0
  have hp := pairedEtaDyadicMoebiusRefinedExteriorEnergy_zero_le_near k
  unfold pairedEtaDyadicMoebiusParityAllowance
  linarith

/-- Every original actual zero satisfies the same signed near-parity bound; the still-open near-energy decay has not been assumed. -/
theorem pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_moebius_nearParity
    (rho : NontrivialZetaZero) {k : ℕ} (hk : 7 ≤ k) :
    pairedEtaCurrentHorizontalDisplacement rho * pairedEtaProjectionHeadZeroWeight rho ≤
      pairedEtaDyadicMoebiusNearParityEnergy k + pairedEtaDyadicMoebiusParityAllowance k :=
  (pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_dyadicDeficit rho k).trans
    (pairedEtaDyadicTranslateDeficit_le_moebius_nearParity hk)

end

end RiemannGaussian
