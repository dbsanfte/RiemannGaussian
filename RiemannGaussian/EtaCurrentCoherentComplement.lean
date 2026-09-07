import RiemannGaussian.EtaCurrentFullInverseEnergy

/-!
# Coherent inverse bands at the original current's physical cutoff

Each reflected channel chooses its actual coherent band by integer
division of the current's cutoff. The full moving complement restores
the complete energy, including its negative mixed interaction. The
original current differs from this full signed split expression by a
proved summable weighted error for every cutoff and multiplicity.
-/

open Complex
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- The coherent band inside the literal even cutoff of the original current. -/
def pairedEtaCurrentCoherentBand (rho : NontrivialZetaZero) (N : ℕ) : Finset (ℕ × ℕ) :=
  pairedEtaInverseCoherentBand (pairedEtaInverseCoherenceScale rho)
    (2 * (N + 2) / (pairedEtaInverseCoherenceScale rho + 2))

/-- Integer division places the chosen band inside the actual full inverse region at every cutoff. -/
theorem pairedEtaCurrentCoherentBand_subset (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCurrentCoherentBand rho N ⊆ pairedEtaInverseHyperbolicRegion (2 * (N + 2)) :=
  (pairedEtaInverseCoherentBand_subset _ _).trans
    (pairedEtaInverseHyperbolicRegion_mono (Nat.mul_div_le _ _))

/-- At the original physical cutoff, each sufficiently large coherent band has the proved negative mixed interaction
with its complete moving complement. The displayed size conditions are explicit cutoff thresholds. -/
theorem pairedEtaCurrentCoherentComplement_cross_re_le (rho : NontrivialZetaZero) (N : ℕ)
    (hsize : pairedEtaInverseCoherenceScale rho + 2 ≤
      2 * (N + 2) / (pairedEtaInverseCoherenceScale rho + 2))
    (hlarge : 4 * (‖rho.1‖ / rho.1.re + 1) ≤
      ((2 * (N + 2) / (pairedEtaInverseCoherenceScale rho + 2) : ℕ) : ℝ)) :
    let M := 2 * (N + 2)
    let P := (M : ℂ) ^ rho.1 * pairedEtaCompletedMomentInverseRegion rho 0 (pairedEtaLogTailCutoff (N + 2)) M
      (pairedEtaCurrentCoherentBand rho N)
    let Q := (M : ℂ) ^ rho.1 * pairedEtaCompletedMomentInverseRegion rho 0 (pairedEtaLogTailCutoff (N + 2)) M
      (pairedEtaInverseHyperbolicRegion M \ pairedEtaCurrentCoherentBand rho N)
    (Q * starRingEnd ℂ P).re ≤ -(‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 8) *
      ((M / (pairedEtaInverseCoherenceScale rho + 2) : ℕ) : ℝ) ^ 2 := by
  let B := pairedEtaInverseCoherenceScale rho
  let M := 2 * (N + 2)
  let K := M / (B + 2)
  have hK : 1 ≤ K := by change B + 2 ≤ K at hsize; omega
  have hr : M % (B + 2) < K := (Nat.mod_lt M (by omega : 0 < B + 2)).trans_le hsize
  have h := pairedEtaCompletedMomentInverseCoherentComplement_cross_re_le rho
    (pairedEtaLogTailCutoff (N + 2)) hK hr hlarge
  dsimp only [B, M, K] at h
  simpa only [Nat.div_add_mod, pairedEtaInverseCoherentComplement, pairedEtaCurrentCoherentBand] using h

/-- The unchanged current is controlled by the full coherent/complement energies with all mixed terms and both
reflected channels retained. Its explicit error envelope is summable independently of terminal cutoff. -/
theorem pairedEtaLeadingCurrent_weighted_coherentComplement_error_le (rho : NontrivialZetaZero) (N : ℕ) :
    let V := fun z R ↦ pairedEtaCompletedMomentInverseRegion z 0 (pairedEtaLogTailCutoff (N + 2)) (2 * (N + 2)) R
    let P := fun z ↦ V z (pairedEtaCurrentCoherentBand z N)
    let Q := fun z ↦ V z (pairedEtaInverseHyperbolicRegion (2 * (N + 2)) \ pairedEtaCurrentCoherentBand z N)
    let rp := NontrivialZetaZero.conjugatePartner rho
    (2 * N + 1 : ℝ) * |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N -
      2 * pairedEtaLogTailShiftIncrement (N + 1) *
        ((pairedEtaCurrentZeroEnergyCoefficient rp).re *
            (‖Q rp‖ ^ 2 + ‖P rp‖ ^ 2 + 2 * (Q rp * starRingEnd ℂ (P rp)).re) -
          (pairedEtaCurrentZeroEnergyCoefficient rho).re *
            (‖Q rho‖ ^ 2 + ‖P rho‖ ^ 2 + 2 * (Q rho * starRingEnd ℂ (P rho)).re))| ≤
      pairedEtaCurrentZeroEnergyErrorEnvelope rho N := by
  have h := pairedEtaLeadingCurrent_weighted_fullInverseEnergy_error_le rho N
  rw [pairedEtaCurrentFullInverseEnergy_eq_split rho N
    (pairedEtaCurrentCoherentBand_subset (NontrivialZetaZero.conjugatePartner rho) N)
    (pairedEtaCurrentCoherentBand_subset rho N)] at h
  exact h

end

end RiemannGaussian
