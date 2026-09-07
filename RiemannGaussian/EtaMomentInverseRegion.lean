import RiemannGaussian.EtaInverseHyperbolicCoefficients
import RiemannGaussian.EtaWeightedAtomMeanSquare

/-!
# Mean-square control of the original inverse on curved divisor regions

The carrier consists of the original outer inverse and inner Möbius
terms with their exact divided cutoff and translated center. Product
grouping and a complete collision bound apply to arbitrary portions of
the actual hyperbola, before the original horizontal decay is restored.
-/

open Complex
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- The unmodified completed inverse on a selected finite set of divisor pairs. -/
def pairedEtaCompletedMomentInverseRegion (rho : NontrivialZetaZero) (k : ℕ)
    (a : ℝ) (M : ℕ) (S : Finset (ℕ × ℕ)) : ℂ :=
  ∑ p ∈ S, (p.1 : ℂ) ^ (-rho.1) *
    pairedEtaCompletedMomentMoebiusTerm rho k (a - Real.log p.1) (M / p.1) p.2

/-- Exact product grouping preserves the complete original inverse on every physical subregion. -/
theorem pairedEtaCompletedMomentInverseRegion_eq_atoms
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) (M : ℕ)
    {S : Finset (ℕ × ℕ)} {T : ℕ} (hS : S ⊆ pairedEtaInverseHyperbolicRegion T) :
    pairedEtaCompletedMomentInverseRegion rho k a M S =
      pairedEtaWeightedMomentDivisorFamily rho k (fun n ↦ pairedEtaInverseRegionCoefficient S n) a M T := by
  unfold pairedEtaWeightedMomentDivisorFamily
  simp only [Complex.ofReal_intCast]
  rw [sum_pairedEtaInverseRegionCoefficient_mul hS]
  unfold pairedEtaCompletedMomentInverseRegion
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hd, he, _⟩ := mem_pairedEtaInverseHyperbolicRegion.mp (hS hp)
  exact pairedEtaMomentInverseCell_eq_atom rho k a M hd he

/-- An actual hyperbolic outer band is exactly the original inverse
sum with its curved inner cutoff, including every translated center. -/
theorem pairedEtaCompletedMomentInverseHyperbolicBand_eq_sum
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) (M T E F : ℕ) :
    pairedEtaCompletedMomentInverseRegion rho k a M (pairedEtaInverseHyperbolicBand T E F) =
      ∑ d ∈ Finset.Ioc E F, pairedEtaCompletedMomentInversePartialTerm rho k a M d (T / d) := by
  let f : ℕ × ℕ → ℂ := fun p ↦ (p.1 : ℂ) ^ (-rho.1) *
    pairedEtaCompletedMomentMoebiusTerm rho k (a - Real.log p.1) (M / p.1) p.2
  have h := Finset.sum_fiberwise_of_maps_to (s := pairedEtaInverseHyperbolicBand T E F)
    (t := Finset.Ioc E F) (g := fun p : ℕ × ℕ ↦ p.1)
    (fun p hp ↦ Finset.mem_Ioc.mpr (Finset.mem_filter.mp hp).2) f
  change (∑ p ∈ pairedEtaInverseHyperbolicBand T E F, f p) = _
  rw [← h]
  apply Finset.sum_congr rfl
  intro d hd
  have hdp : 1 ≤ d := by have hEd := (Finset.mem_Ioc.mp hd).1; omega
  unfold pairedEtaCompletedMomentInversePartialTerm pairedEtaCompletedMomentOriginalFamily
  rw [Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun e _ ↦ (d, e))
  · intro e he
    obtain ⟨he1, heT⟩ := Finset.mem_Icc.mp he
    apply Finset.mem_filter.mpr
    refine ⟨?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨mem_pairedEtaInverseHyperbolicRegion.mpr ⟨hdp, he1, ?_⟩, Finset.mem_Ioc.mp hd⟩
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hdp).mp heT
  · intro e he e' he' heq
    exact congrArg Prod.snd heq
  · intro p hp
    obtain ⟨hpS, hpd⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpos, he, hprod⟩ := mem_pairedEtaInverseHyperbolicRegion.mp (Finset.mem_filter.mp hpS).1
    refine ⟨p.2, Finset.mem_Icc.mpr ⟨he, ?_⟩, ?_⟩
    · apply (Nat.le_div_iff_mul_le hdp).mpr
      simpa only [hpd, Nat.mul_comm] using hprod
    · exact Prod.ext hpd.symm rfl
  · intro e he
    rfl

/-- The full mixed complex kernel retains all pairs from two independently selected regions. -/
theorem pairedEtaCompletedMomentInverseRegion_mul_conj_eq_pairs
    (rho : NontrivialZetaZero) (k l : ℕ) (a : ℝ) (M : ℕ) (S R : Finset (ℕ × ℕ)) :
    pairedEtaCompletedMomentInverseRegion rho k a M S *
        starRingEnd ℂ (pairedEtaCompletedMomentInverseRegion rho l a M R) =
      ∑ p ∈ S, ∑ q ∈ R,
        ((p.1 : ℂ) ^ (-rho.1) *
          pairedEtaCompletedMomentMoebiusTerm rho k (a - Real.log p.1) (M / p.1) p.2) *
        starRingEnd ℂ ((q.1 : ℂ) ^ (-rho.1) *
          pairedEtaCompletedMomentMoebiusTerm rho l (a - Real.log q.1) (M / q.1) q.2) := by
  simp only [pairedEtaCompletedMomentInverseRegion, map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The literal inverse mean square on a fixed curved region at the moving physical endpoint. -/
def pairedEtaCompletedMomentInverseRegionMeanSquare
    (rho : NontrivialZetaZero) (k A L : ℕ) (S : Finset (ℕ × ℕ)) : ℝ :=
  (∑ n ∈ Finset.range L, ‖pairedEtaCompletedMomentInverseRegion rho k
    (Real.log ((A + n : ℕ) + 1 : ℝ)) (A + n) S‖ ^ 2) / L

/-- Exact grouping transfers the original region average to the complete signed product coefficients. -/
theorem pairedEtaCompletedMomentInverseRegionMeanSquare_eq_weighted
    (rho : NontrivialZetaZero) (k A L : ℕ) {S : Finset (ℕ × ℕ)} {T : ℕ}
    (hS : S ⊆ pairedEtaInverseHyperbolicRegion T) :
    pairedEtaCompletedMomentInverseRegionMeanSquare rho k A L S =
      pairedEtaWeightedMomentDivisorMeanSquare rho k (fun n ↦ pairedEtaInverseRegionCoefficient S n) A L T := by
  unfold pairedEtaCompletedMomentInverseRegionMeanSquare pairedEtaWeightedMomentDivisorMeanSquare
  simp_rw [pairedEtaCompletedMomentInverseRegion_eq_atoms rho k _ _ hS]

/-- The complete hyperbolic region has product times fifth-logarithmic mean-square cost. -/
def pairedEtaInverseRegionBudget (T : ℕ) : ℝ := (T : ℝ) * (1 + Real.log T) ^ 5

/-- Every actual selected inverse region is jointly bounded through its
complete signed factorization energy, with no rectangular decomposition. -/
theorem pairedEtaCompletedMomentInverseRegionMeanSquare_le
    (rho : NontrivialZetaZero) {k A L T : ℕ} (hk : k < analyticZetaZeroMultiplicity rho)
    {S : Finset (ℕ × ℕ)} (hS : S ⊆ pairedEtaInverseHyperbolicRegion T)
    (hT : 1 ≤ T) (hTA : T ≤ A) (hTL : T ^ 2 ≤ L) :
    pairedEtaCompletedMomentInverseRegionMeanSquare rho k A L S ≤
      pairedEtaWeightedMomentDivisorConstant rho k * pairedEtaInverseRegionBudget T *
        (A : ℝ) ^ (-2 * rho.1.re) := by
  rw [pairedEtaCompletedMomentInverseRegionMeanSquare_eq_weighted rho k A L hS]
  apply (pairedEtaWeightedMomentDivisorMeanSquare_le rho hk
    (fun n ↦ pairedEtaInverseRegionCoefficient S n) hT hTA hTL).trans
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (sum_sq_pairedEtaInverseRegionCoefficient_le_log_cube S T)
    (mul_nonneg (pairedEtaWeightedMomentDivisorConstant_nonneg rho k) (sq_nonneg (1 + Real.log T))))
    (Real.rpow_nonneg (Nat.cast_nonneg A) (-2 * rho.1.re))
  convert h using 1
  unfold pairedEtaInverseRegionBudget
  ring

/-- The original inverse on any outer band keeps its entire curved inner range,
with all geometric conditions discharged at the full physical starting cutoff. -/
theorem pairedEtaCompletedMomentInverseHyperbolicBandMeanSquare_le
    (rho : NontrivialZetaZero) {k A L T : ℕ} (hk : k < analyticZetaZeroMultiplicity rho)
    (E F : ℕ) (hT : 1 ≤ T) (hTA : T ≤ A) (hTL : T ^ 2 ≤ L) :
    pairedEtaCompletedMomentInverseRegionMeanSquare rho k A L (pairedEtaInverseHyperbolicBand T E F) ≤
      pairedEtaWeightedMomentDivisorConstant rho k * pairedEtaInverseRegionBudget T *
        (A : ℝ) ^ (-2 * rho.1.re) :=
  pairedEtaCompletedMomentInverseRegionMeanSquare_le rho hk
    (pairedEtaInverseHyperbolicBand_subset T E F) hT hTA hTL

end

end RiemannGaussian
