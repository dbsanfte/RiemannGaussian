import RiemannGaussian.EtaCurrentZeroEnergyTransport
import RiemannGaussian.EtaCoherentBandComplement

/-!
# The full moving inverse energy in the original weighted current

Both original current branches have summable weighted error from one
signed expression in the complete zeroth-order inverse regions. Every
region may be split into an arbitrary band and its full moving complement,
with all ordered complex cross terms retained. The error budget also
applies to the actual linear-width Gaussian return. No bound for the
signed inverse energy itself is proved here.
-/

open Complex
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- The whole original inverse region equals the actual finite moment at its physical cutoff and center. -/
theorem pairedEtaFiniteCompletedMoment_eq_fullInverseRegion
    (rho : NontrivialZetaZero) (N k : ℕ) :
    pairedEtaFiniteCompletedMoment rho N k =
      pairedEtaCompletedMomentInverseRegion rho k (pairedEtaLogTailCutoff N) (2 * N)
        (pairedEtaInverseHyperbolicRegion (2 * N)) := by
  rw [pairedEtaCompletedMomentInverseRegion_full, pairedEtaFiniteCompletedMoment_eq_momentInverse,
    sum_pairedEtaCompletedMomentInverseTerm]

/-- Any part of the original inverse region and its full moving complement sum to the complete carrier. -/
theorem pairedEtaCompletedMomentInverseRegion_complement_add
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) (M : ℕ) {S : Finset (ℕ × ℕ)}
    (hS : S ⊆ pairedEtaInverseHyperbolicRegion M) :
    pairedEtaCompletedMomentInverseRegion rho k a M (pairedEtaInverseHyperbolicRegion M \ S) +
      pairedEtaCompletedMomentInverseRegion rho k a M S =
        pairedEtaCompletedMomentInverseRegion rho k a M (pairedEtaInverseHyperbolicRegion M) := by
  unfold pairedEtaCompletedMomentInverseRegion
  exact Finset.sum_sdiff hS

/-- Independent splits of the two actual inverse factors retain all four ordered complex products. -/
theorem pairedEtaCompletedMomentInverseRegion_full_product_eq_split
    (rho : NontrivialZetaZero) (k l : ℕ) (a : ℝ) (M : ℕ) {S T : Finset (ℕ × ℕ)}
    (hS : S ⊆ pairedEtaInverseHyperbolicRegion M) (hT : T ⊆ pairedEtaInverseHyperbolicRegion M) :
    let V := fun j R ↦ pairedEtaCompletedMomentInverseRegion rho j a M R
    let H := pairedEtaInverseHyperbolicRegion M
    V k H * starRingEnd ℂ (V l H) =
      V k (H \ S) * starRingEnd ℂ (V l (H \ T)) +
        V k (H \ S) * starRingEnd ℂ (V l T) +
        V k S * starRingEnd ℂ (V l (H \ T)) + V k S * starRingEnd ℂ (V l T) := by
  dsimp only
  conv_lhs =>
    rw [← pairedEtaCompletedMomentInverseRegion_complement_add rho k a M hS,
      ← pairedEtaCompletedMomentInverseRegion_complement_add rho l a M hT]
  rw [map_add]
  ring

/-- The complete inverse energy keeps the real mixed interaction with its complement. -/
theorem pairedEtaCompletedMomentInverseRegion_full_norm_sq_eq_split
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) (M : ℕ) {S : Finset (ℕ × ℕ)}
    (hS : S ⊆ pairedEtaInverseHyperbolicRegion M) :
    let P := pairedEtaCompletedMomentInverseRegion rho k a M S
    let Q := pairedEtaCompletedMomentInverseRegion rho k a M (pairedEtaInverseHyperbolicRegion M \ S)
    ‖pairedEtaCompletedMomentInverseRegion rho k a M (pairedEtaInverseHyperbolicRegion M)‖ ^ 2 =
      ‖Q‖ ^ 2 + ‖P‖ ^ 2 + 2 * (Q * starRingEnd ℂ P).re := by
  dsimp only
  rw [← pairedEtaCompletedMomentInverseRegion_complement_add rho k a M hS]
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_add]

/-- The signed complete inverse energies, with the original physical cutoffs and actual multiplicity coefficients. -/
def pairedEtaCurrentFullInverseEnergy (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  2 * pairedEtaLogTailShiftIncrement (N + 1) *
    ((pairedEtaCurrentZeroEnergyCoefficient (NontrivialZetaZero.conjugatePartner rho)).re *
        ‖pairedEtaCompletedMomentInverseRegion (NontrivialZetaZero.conjugatePartner rho) 0
          (pairedEtaLogTailCutoff (N + 2)) (2 * (N + 2))
          (pairedEtaInverseHyperbolicRegion (2 * (N + 2)))‖ ^ 2 -
      (pairedEtaCurrentZeroEnergyCoefficient rho).re *
        ‖pairedEtaCompletedMomentInverseRegion rho 0 (pairedEtaLogTailCutoff (N + 2)) (2 * (N + 2))
          (pairedEtaInverseHyperbolicRegion (2 * (N + 2)))‖ ^ 2)

/-- Exact full inversion identifies the signed carrier used by the proved current transport. -/
theorem pairedEtaCurrentFullInverseEnergy_eq_zeroEnergy (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCurrentFullInverseEnergy rho N = pairedEtaCurrentZeroEnergy rho N := by
  rw [pairedEtaCurrentZeroEnergy_eq_signed_norms]
  simp only [pairedEtaCurrentFullInverseEnergy, pairedEtaFiniteCompletedMoment_eq_fullInverseRegion]

/-- Both reflected regions can be split independently while retaining each full mixed term in the signed current carrier. -/
theorem pairedEtaCurrentFullInverseEnergy_eq_split (rho : NontrivialZetaZero) (N : ℕ)
    {S T : Finset (ℕ × ℕ)} (hS : S ⊆ pairedEtaInverseHyperbolicRegion (2 * (N + 2)))
    (hT : T ⊆ pairedEtaInverseHyperbolicRegion (2 * (N + 2))) :
    let V := fun z R ↦ pairedEtaCompletedMomentInverseRegion z 0 (pairedEtaLogTailCutoff (N + 2)) (2 * (N + 2)) R
    let H := pairedEtaInverseHyperbolicRegion (2 * (N + 2))
    let rp := NontrivialZetaZero.conjugatePartner rho
    pairedEtaCurrentFullInverseEnergy rho N = 2 * pairedEtaLogTailShiftIncrement (N + 1) *
      ((pairedEtaCurrentZeroEnergyCoefficient rp).re *
          (‖V rp (H \ S)‖ ^ 2 + ‖V rp S‖ ^ 2 + 2 * (V rp (H \ S) * starRingEnd ℂ (V rp S)).re) -
        (pairedEtaCurrentZeroEnergyCoefficient rho).re *
          (‖V rho (H \ T)‖ ^ 2 + ‖V rho T‖ ^ 2 + 2 * (V rho (H \ T) * starRingEnd ℂ (V rho T)).re)) := by
  dsimp only
  unfold pairedEtaCurrentFullInverseEnergy
  rw [pairedEtaCompletedMomentInverseRegion_full_norm_sq_eq_split _ _ _ _ hS,
    pairedEtaCompletedMomentInverseRegion_full_norm_sq_eq_split _ _ _ _ hT]

/-- The original current has a proved summable weighted error from the complete inverse energies in both branches. -/
theorem pairedEtaLeadingCurrent_weighted_fullInverseEnergy_error_le (rho : NontrivialZetaZero) (N : ℕ) :
    (2 * N + 1 : ℝ) * |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N - pairedEtaCurrentFullInverseEnergy rho N| ≤
      pairedEtaCurrentZeroEnergyErrorEnvelope rho N := by
  rw [pairedEtaCurrentFullInverseEnergy_eq_zeroEnergy]
  exact pairedEtaLeadingCurrent_weighted_zeroEnergy_error_le rho N

/-- Summability of the complete current transport error is unconditional for every actual zero and multiplicity. -/
theorem summable_oddEndpoint_mul_abs_pairedEtaLeadingCurrent_fullInverseEnergy_error (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦ (2 * N + 1 : ℝ) *
      |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N - pairedEtaCurrentFullInverseEnergy rho N|) :=
  (summable_pairedEtaCurrentZeroEnergyErrorEnvelope rho).of_nonneg_of_le
    (fun N ↦ by positivity) (pairedEtaLeadingCurrent_weighted_fullInverseEnergy_error_le rho)

/-- The original current's first absolute moment differs from the complete signed inverse energy by a uniform finite budget. -/
theorem pairedEtaLeadingCurrent_fullInverseEnergy_firstMoment_stability
    (rho : NontrivialZetaZero) (K : ℕ) :
    |(∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N|) -
      (∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * |pairedEtaCurrentFullInverseEnergy rho N|)| ≤
        ∑' N : ℕ, pairedEtaCurrentZeroEnergyErrorEnvelope rho N := by
  calc
    _ = |∑ N ∈ Finset.range K, ((2 * N + 1 : ℝ) * |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N| -
        (2 * N + 1 : ℝ) * |pairedEtaCurrentFullInverseEnergy rho N|)| := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ N ∈ Finset.range K, |(2 * N + 1 : ℝ) * |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N| -
        (2 * N + 1 : ℝ) * (|pairedEtaCurrentFullInverseEnergy rho N|)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) *
        |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N - pairedEtaCurrentFullInverseEnergy rho N| := by
      apply Finset.sum_le_sum
      intro N _
      have hw : (0 : ℝ) ≤ 2 * N + 1 := by positivity
      rw [← mul_sub, abs_mul, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub _ _) hw
    _ ≤ ∑ N ∈ Finset.range K, pairedEtaCurrentZeroEnergyErrorEnvelope rho N :=
      Finset.sum_le_sum (fun N _ ↦ pairedEtaLeadingCurrent_weighted_fullInverseEnergy_error_le rho N)
    _ ≤ _ := (summable_pairedEtaCurrentZeroEnergyErrorEnvelope rho).sum_le_tsum _
      (fun N _ ↦ pairedEtaCurrentZeroEnergyErrorEnvelope_nonneg rho N)

/-- The original linear-width heat return retains both the Gaussian and complete inverse transport errors. -/
theorem pairedEtaLeadingCurrentLinearHeatReturn_weighted_fullInverseEnergy_error_le
    (rho : NontrivialZetaZero) (N : ℕ) :
    (2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho N - (pairedEtaCurrentFullInverseEnergy rho N : ℂ)‖ ≤
      pairedEtaCurrentLinearHeatErrorMajorant rho N + pairedEtaCurrentZeroEnergyErrorEnvelope rho N := by
  have ht := norm_sub_le_norm_sub_add_norm_sub (pairedEtaLeadingCurrentLinearHeatReturn rho N)
    (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ) (pairedEtaCurrentFullInverseEnergy rho N : ℂ)
  have h := mul_le_mul_of_nonneg_left ht (by positivity : (0 : ℝ) ≤ 2 * N + 1)
  rw [mul_add] at h
  simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  exact h.trans (add_le_add (pairedEtaLeadingCurrentLinearHeatReturn_weighted_error_le rho N)
    (pairedEtaLeadingCurrent_weighted_fullInverseEnergy_error_le rho N))

/-- The return's full weighted norm error is bounded by a genuinely summable explicit envelope. -/
theorem summable_oddEndpoint_mul_norm_pairedEtaLeadingCurrentLinearHeatReturn_fullInverseEnergy_error
    (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦ (2 * N + 1 : ℝ) *
      ‖pairedEtaLeadingCurrentLinearHeatReturn rho N - (pairedEtaCurrentFullInverseEnergy rho N : ℂ)‖) :=
  ((summable_pairedEtaCurrentLinearHeatErrorMajorant rho).add
    (summable_pairedEtaCurrentZeroEnergyErrorEnvelope rho)).of_nonneg_of_le
      (fun N ↦ by positivity) (pairedEtaLeadingCurrentLinearHeatReturn_weighted_fullInverseEnergy_error_le rho)

/-- The signed complex weighted error series is retained along with its absolute summability. -/
theorem summable_oddEndpoint_smul_pairedEtaLeadingCurrentLinearHeatReturn_fullInverseEnergy_error
    (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦ (2 * N + 1 : ℝ) •
      (pairedEtaLeadingCurrentLinearHeatReturn rho N - (pairedEtaCurrentFullInverseEnergy rho N : ℂ))) := by
  apply (summable_oddEndpoint_mul_norm_pairedEtaLeadingCurrentLinearHeatReturn_fullInverseEnergy_error rho).of_norm_bounded
  intro N
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * N + 1), le_refl]

/-- A single finite explicit budget controls the full transport at all terminal cutoffs. -/
theorem pairedEtaLeadingCurrentLinearHeatReturn_fullInverseEnergy_error_sum_le
    (rho : NontrivialZetaZero) (K : ℕ) :
    (∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) *
      ‖pairedEtaLeadingCurrentLinearHeatReturn rho N - (pairedEtaCurrentFullInverseEnergy rho N : ℂ)‖) ≤
        ∑' N : ℕ, (pairedEtaCurrentLinearHeatErrorMajorant rho N + pairedEtaCurrentZeroEnergyErrorEnvelope rho N) := by
  calc
    _ ≤ ∑ N ∈ Finset.range K,
        (pairedEtaCurrentLinearHeatErrorMajorant rho N + pairedEtaCurrentZeroEnergyErrorEnvelope rho N) :=
      Finset.sum_le_sum (fun N _ ↦ pairedEtaLeadingCurrentLinearHeatReturn_weighted_fullInverseEnergy_error_le rho N)
    _ ≤ _ := ((summable_pairedEtaCurrentLinearHeatErrorMajorant rho).add
      (summable_pairedEtaCurrentZeroEnergyErrorEnvelope rho)).sum_le_tsum _
        (fun N _ ↦ add_nonneg (pairedEtaCurrentLinearHeatErrorMajorant_nonneg rho N)
          (pairedEtaCurrentZeroEnergyErrorEnvelope_nonneg rho N))

/-- The first absolute moments of the actual return and signed full inverse energies differ by a finite uniform budget.
This proves stability of the target and does not bound either moment itself. -/
theorem pairedEtaLeadingCurrentLinearHeatReturn_fullInverseEnergy_firstMoment_stability
    (rho : NontrivialZetaZero) (K : ℕ) :
    |(∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho N‖) -
      (∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * |pairedEtaCurrentFullInverseEnergy rho N|)| ≤
        ∑' N : ℕ, (pairedEtaCurrentLinearHeatErrorMajorant rho N + pairedEtaCurrentZeroEnergyErrorEnvelope rho N) := by
  calc
    _ = |∑ N ∈ Finset.range K, ((2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho N‖ -
        (2 * N + 1 : ℝ) * |pairedEtaCurrentFullInverseEnergy rho N|)| := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ N ∈ Finset.range K, |(2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho N‖ -
        (2 * N + 1 : ℝ) * (|pairedEtaCurrentFullInverseEnergy rho N|)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) *
        ‖pairedEtaLeadingCurrentLinearHeatReturn rho N - (pairedEtaCurrentFullInverseEnergy rho N : ℂ)‖ := by
      apply Finset.sum_le_sum
      intro N _
      have hw : (0 : ℝ) ≤ 2 * N + 1 := by positivity
      rw [← mul_sub, abs_mul, abs_of_nonneg hw]
      apply mul_le_mul_of_nonneg_left _ hw
      simpa only [Complex.norm_real, Real.norm_eq_abs] using
        abs_norm_sub_norm_le (pairedEtaLeadingCurrentLinearHeatReturn rho N) (pairedEtaCurrentFullInverseEnergy rho N : ℂ)
    _ ≤ _ := pairedEtaLeadingCurrentLinearHeatReturn_fullInverseEnergy_error_sum_le rho K

end

end RiemannGaussian
