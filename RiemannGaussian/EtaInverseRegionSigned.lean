import RiemannGaussian.EtaMomentInverseRegion

/-!
# Signed mixed bounds between independently selected inverse regions

The two actual curved divisor regions may overlap or differ. Their
complete complex cross kernel precedes the first absolute average.
Both reflected channels and the actual adjacent multiplicity orders
remain present in the resulting physical estimate.
-/

open Complex
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- The signed completed mixed pair on two independently selected original inverse regions. -/
def pairedEtaSignedCompletedMomentInverseRegionPair
    (rho : NontrivialZetaZero) (k l M : ℕ) (S R : Finset (ℕ × ℕ)) : ℂ :=
  etaSignedCompletedPair
    (pairedEtaCompletedMomentInverseRegion (NontrivialZetaZero.conjugatePartner rho) k
      (Real.log (M + 1 : ℝ)) M S)
    (pairedEtaCompletedMomentInverseRegion (NontrivialZetaZero.conjugatePartner rho) l
      (Real.log (M + 1 : ℝ)) M R)
    (pairedEtaCompletedMomentInverseRegion rho k (Real.log (M + 1 : ℝ)) M S)
    (pairedEtaCompletedMomentInverseRegion rho l (Real.log (M + 1 : ℝ)) M R)

/-- The signed mixed kernel retains every original ordered cell pair across both regions. -/
theorem pairedEtaSignedCompletedMomentInverseRegionPair_eq_double_sum
    (rho : NontrivialZetaZero) (k l M : ℕ) (S R : Finset (ℕ × ℕ)) :
    pairedEtaSignedCompletedMomentInverseRegionPair rho k l M S R =
      ∑ p ∈ S, ∑ q ∈ R, etaSignedCompletedPair
        ((p.1 : ℂ) ^ (-(NontrivialZetaZero.conjugatePartner rho).1) *
          pairedEtaCompletedMomentMoebiusTerm (NontrivialZetaZero.conjugatePartner rho) k
            (Real.log (M + 1 : ℝ) - Real.log p.1) (M / p.1) p.2)
        ((q.1 : ℂ) ^ (-(NontrivialZetaZero.conjugatePartner rho).1) *
          pairedEtaCompletedMomentMoebiusTerm (NontrivialZetaZero.conjugatePartner rho) l
            (Real.log (M + 1 : ℝ) - Real.log q.1) (M / q.1) q.2)
        ((p.1 : ℂ) ^ (-rho.1) * pairedEtaCompletedMomentMoebiusTerm rho k
          (Real.log (M + 1 : ℝ) - Real.log p.1) (M / p.1) p.2)
        ((q.1 : ℂ) ^ (-rho.1) * pairedEtaCompletedMomentMoebiusTerm rho l
          (Real.log (M + 1 : ℝ) - Real.log q.1) (M / q.1) q.2) := by
  simp only [pairedEtaSignedCompletedMomentInverseRegionPair, pairedEtaCompletedMomentInverseRegion,
    etaSignedCompletedPair, map_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
  congr 1 <;> rw [Finset.sum_comm]

/-- The first absolute average of the original signed pair of inverse regions. -/
def pairedEtaSignedCompletedMomentInverseRegionMeanAbsolute
    (rho : NontrivialZetaZero) (k l A L : ℕ) (S R : Finset (ℕ × ℕ)) : ℝ :=
  (∑ n ∈ Finset.range L, ‖pairedEtaSignedCompletedMomentInverseRegionPair rho k l (A + n) S R‖) / L

/-- The full mixed absolute average is bounded through its four original completed channels. -/
theorem pairedEtaSignedCompletedMomentInverseRegionMeanAbsolute_le_channels
    (rho : NontrivialZetaZero) (k l A L : ℕ) (S R : Finset (ℕ × ℕ)) :
    pairedEtaSignedCompletedMomentInverseRegionMeanAbsolute rho k l A L S R ≤
      (pairedEtaCompletedMomentInverseRegionMeanSquare (NontrivialZetaZero.conjugatePartner rho) k A L S +
       pairedEtaCompletedMomentInverseRegionMeanSquare (NontrivialZetaZero.conjugatePartner rho) l A L R +
       pairedEtaCompletedMomentInverseRegionMeanSquare rho k A L S +
       pairedEtaCompletedMomentInverseRegionMeanSquare rho l A L R) / 2 := by
  unfold pairedEtaSignedCompletedMomentInverseRegionMeanAbsolute pairedEtaCompletedMomentInverseRegionMeanSquare
  rw [← add_div, ← add_div, ← add_div, div_right_comm]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg L)
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_le_sum
  intro n hn
  unfold pairedEtaSignedCompletedMomentInverseRegionPair
  apply (norm_etaSignedCompletedPair_le _ _ _ _).trans
  nlinarith [sq_nonneg
    (‖pairedEtaCompletedMomentInverseRegion (NontrivialZetaZero.conjugatePartner rho) k
      (Real.log ((A + n : ℕ) + 1 : ℝ)) (A + n) S‖ -
     ‖pairedEtaCompletedMomentInverseRegion (NontrivialZetaZero.conjugatePartner rho) l
      (Real.log ((A + n : ℕ) + 1 : ℝ)) (A + n) R‖),
    sq_nonneg
    (‖pairedEtaCompletedMomentInverseRegion rho k (Real.log ((A + n : ℕ) + 1 : ℝ)) (A + n) S‖ -
     ‖pairedEtaCompletedMomentInverseRegion rho l (Real.log ((A + n : ℕ) + 1 : ℝ)) (A + n) R‖)]

/-- The mixed operator constant keeps both moment orders of the original inverse. -/
def pairedEtaCompletedMixedMomentInverseRegionConstant (rho : NontrivialZetaZero) (k l : ℕ) : ℝ :=
  (pairedEtaWeightedMomentDivisorConstant rho k + pairedEtaWeightedMomentDivisorConstant rho l) / 2

/-- Two arbitrary actual inverse subregions have joint signed first absolute control,
including their full mixed pairs and both complementary physical decay rates. -/
theorem pairedEtaSignedCompletedMomentInverseRegionMeanAbsolute_le
    (rho : NontrivialZetaZero) {k l A L T : ℕ}
    (hk : k < analyticZetaZeroMultiplicity rho) (hl : l < analyticZetaZeroMultiplicity rho)
    {S R : Finset (ℕ × ℕ)} (hS : S ⊆ pairedEtaInverseHyperbolicRegion T)
    (hR : R ⊆ pairedEtaInverseHyperbolicRegion T)
    (hT : 1 ≤ T) (hTA : T ≤ A) (hTL : T ^ 2 ≤ L) :
    pairedEtaSignedCompletedMomentInverseRegionMeanAbsolute rho k l A L S R ≤
      pairedEtaInverseRegionBudget T *
        (pairedEtaCompletedMixedMomentInverseRegionConstant (NontrivialZetaZero.conjugatePartner rho) k l *
            (A : ℝ) ^ (-2 * (1 - rho.1.re)) +
          pairedEtaCompletedMixedMomentInverseRegionConstant rho k l * (A : ℝ) ^ (-2 * rho.1.re)) := by
  have hkp : k < analyticZetaZeroMultiplicity (NontrivialZetaZero.conjugatePartner rho) := by
    simpa only [analyticZetaZeroMultiplicity_conjugatePartner] using hk
  have hlp : l < analyticZetaZeroMultiplicity (NontrivialZetaZero.conjugatePartner rho) := by
    simpa only [analyticZetaZeroMultiplicity_conjugatePartner] using hl
  have h := div_le_div_of_nonneg_right (add_le_add (add_le_add (add_le_add
    (pairedEtaCompletedMomentInverseRegionMeanSquare_le
      (NontrivialZetaZero.conjugatePartner rho) hkp hS hT hTA hTL)
    (pairedEtaCompletedMomentInverseRegionMeanSquare_le
      (NontrivialZetaZero.conjugatePartner rho) hlp hR hT hTA hTL))
    (pairedEtaCompletedMomentInverseRegionMeanSquare_le rho hk hS hT hTA hTL))
    (pairedEtaCompletedMomentInverseRegionMeanSquare_le rho hl hR hT hTA hTL))
    (by norm_num : (0 : ℝ) ≤ 2)
  apply (pairedEtaSignedCompletedMomentInverseRegionMeanAbsolute_le_channels rho k l A L S R).trans
  simp only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_re, Complex.one_re, Complex.conj_re] at h
  convert h using 1
  unfold pairedEtaCompletedMixedMomentInverseRegionConstant
  ring

/-- The adjacent orders of the actual repeated-zero current have mixed
control across any two outer bands with their complete curved inner ranges. -/
theorem pairedEtaSignedCompletedMomentInverseHyperbolicBands_adjacent_le
    (rho : NontrivialZetaZero) (hm : 2 ≤ analyticZetaZeroMultiplicity rho)
    {A L T : ℕ} (E F G H : ℕ) (hT : 1 ≤ T) (hTA : T ≤ A) (hTL : T ^ 2 ≤ L) :
    pairedEtaSignedCompletedMomentInverseRegionMeanAbsolute rho
      (analyticZetaZeroMultiplicity rho - 2) (analyticZetaZeroMultiplicity rho - 1) A L
      (pairedEtaInverseHyperbolicBand T E F) (pairedEtaInverseHyperbolicBand T G H) ≤
      pairedEtaInverseRegionBudget T *
        (pairedEtaCompletedMixedMomentInverseRegionConstant (NontrivialZetaZero.conjugatePartner rho)
            (analyticZetaZeroMultiplicity rho - 2) (analyticZetaZeroMultiplicity rho - 1) *
              (A : ℝ) ^ (-2 * (1 - rho.1.re)) +
          pairedEtaCompletedMixedMomentInverseRegionConstant rho
            (analyticZetaZeroMultiplicity rho - 2) (analyticZetaZeroMultiplicity rho - 1) *
              (A : ℝ) ^ (-2 * rho.1.re)) :=
  pairedEtaSignedCompletedMomentInverseRegionMeanAbsolute_le rho (by omega) (by omega)
    (pairedEtaInverseHyperbolicBand_subset T E F) (pairedEtaInverseHyperbolicBand_subset T G H)
    hT hTA hTL

end

end RiemannGaussian
