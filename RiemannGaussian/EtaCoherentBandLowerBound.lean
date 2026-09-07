import RiemannGaussian.EtaCoherentBandPhase
import RiemannGaussian.EtaCoherentBandCoefficients

/-!
# A physical lower bound on a complete original inverse band

The actual completion and complex inverse powers remain coherent on a
window proportional to the physical starting index. The coefficient
energy is linear in the number of terms, while the physical mean square
has a quadratic lower bound. Thus the cost of keeping a separate band
cannot be removed merely by sharpening an arbitrary-coefficient norm
estimate; its interaction with the complementary inverse is essential.
-/

open Complex
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The original region mean square with its actual common physical power retained. -/
def pairedEtaCompletedMomentInverseRegionPhysicalMeanSquare
    (rho : NontrivialZetaZero) (k A L : ℕ) (S : Finset (ℕ × ℕ)) : ℝ :=
  (∑ r ∈ Finset.range L, ‖((A + r : ℕ) : ℂ) ^ rho.1 *
    pairedEtaCompletedMomentInverseRegion rho k (Real.log ((A + r : ℕ) + 1 : ℝ)) (A + r) S‖ ^ 2) / L

/-- Exact grouping retains the physical average of the original region before applying any operator estimate. -/
theorem pairedEtaCompletedMomentInverseRegionPhysicalMeanSquare_eq_weighted
    (rho : NontrivialZetaZero) (k A L : ℕ) {S : Finset (ℕ × ℕ)} {T : ℕ}
    (hS : S ⊆ pairedEtaInverseHyperbolicRegion T) :
    pairedEtaCompletedMomentInverseRegionPhysicalMeanSquare rho k A L S =
      pairedEtaWeightedMomentDivisorPhysicalMeanSquare rho k
        (fun n ↦ pairedEtaInverseRegionCoefficient S n) A L T := by
  unfold pairedEtaCompletedMomentInverseRegionPhysicalMeanSquare pairedEtaWeightedMomentDivisorPhysicalMeanSquare
  simp_rw [pairedEtaCompletedMomentInverseRegion_eq_atoms rho k _ _ hS]

/-- Every original completed band value retains a linear physical norm on the whole proportional window. -/
theorem pairedEtaCompletedMomentInverseCoherentBand_physical_norm_lower
    (rho : NontrivialZetaZero) (a : ℝ) {B K r : ℕ} (hB : 4 ≤ B)
    (hK : 1 ≤ K) (hr : r < K) (hphase : 4 * ‖rho.1‖ ≤ (B : ℝ)) :
    (‖pairedEtaXiCompletionFactor rho.1‖ / 2) * K ≤
      ‖(((B + 2) * K + r : ℕ) : ℂ) ^ rho.1 *
        pairedEtaCompletedMomentInverseRegion rho 0 a ((B + 2) * K + r)
          (pairedEtaInverseCoherentBand B K)‖ := by
  have hBp : 1 ≤ B := by omega
  have hbase : (0 : ℝ) < (B * K : ℕ) := by exact_mod_cast Nat.mul_pos hBp hK
  have hBM : B * K ≤ (B + 2) * K + r := by simp only [Nat.add_mul]; omega
  have hM : (0 : ℝ) < ((B + 2) * K + r : ℕ) :=
    hbase.trans_le (by exact_mod_cast hBM)
  have hpow : (B * K : ℕ) ^ rho.1.re ≤ (((B + 2) * K + r : ℕ) : ℝ) ^ rho.1.re :=
    Real.rpow_le_rpow hbase.le (by exact_mod_cast hBM) (NontrivialZetaZero.zero_lt_re rho).le
  have hlower := pairedEtaCoherentBandPowerSum_norm_lower rho hBp hK hphase
  rw [pairedEtaCompletedMomentInverseCoherentBand_eq_powerSum rho a hB hr,
    norm_mul, norm_mul]
  have hnorm : ‖(((B + 2) * K + r : ℕ) : ℂ) ^ rho.1‖ =
      (((B + 2) * K + r : ℕ) : ℝ) ^ rho.1.re := by
    simpa only [Complex.ofReal_natCast] using Complex.norm_cpow_eq_rpow_re_of_pos hM rho.1
  rw [hnorm, ← mul_assoc]
  calc
    _ = ((B * K : ℕ) ^ rho.1.re * ‖pairedEtaXiCompletionFactor rho.1‖) *
        (((K : ℝ) / 2) * (B * K : ℕ) ^ (-rho.1.re)) := by
      rw [show ((B * K : ℕ) ^ rho.1.re * ‖pairedEtaXiCompletionFactor rho.1‖) *
          (((K : ℝ) / 2) * (B * K : ℕ) ^ (-rho.1.re)) =
          (‖pairedEtaXiCompletionFactor rho.1‖ / 2 * K) *
            ((B * K : ℕ) ^ rho.1.re * (B * K : ℕ) ^ (-rho.1.re)) by ring,
        ← Real.rpow_add hbase, add_neg_cancel, Real.rpow_zero, mul_one]
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)) hlower
      (by positivity) (by positivity)

/-- The original inverse band's physical mean square has a quadratic lower
bound, with the actual zero's phase scale and every window condition discharged. -/
theorem pairedEtaCompletedMomentInverseCoherentBandPhysicalMeanSquare_lower
    (rho : NontrivialZetaZero) {K : ℕ} (hK : 1 ≤ K) :
    (‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 4) * (K : ℝ) ^ 2 ≤
      pairedEtaCompletedMomentInverseRegionPhysicalMeanSquare rho 0
        ((pairedEtaInverseCoherenceScale rho + 2) * K) K
        (pairedEtaInverseCoherentBand (pairedEtaInverseCoherenceScale rho) K) := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  unfold pairedEtaCompletedMomentInverseRegionPhysicalMeanSquare
  calc
    _ = (∑ _r ∈ Finset.range K, (‖pairedEtaXiCompletionFactor rho.1‖ / 2 * K) ^ 2) / (K : ℝ) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
      ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hKR.le
      apply Finset.sum_le_sum
      intro r hr
      exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr
        (pairedEtaCompletedMomentInverseCoherentBand_physical_norm_lower rho _
          (four_le_pairedEtaInverseCoherenceScale rho) hK (Finset.mem_range.mp hr)
          (four_norm_le_pairedEtaInverseCoherenceScale rho))

/-- Even over the complete doubling window, the original physical inverse band
has a quadratic lower bound from its coherent initial subwindow. -/
theorem pairedEtaCompletedMomentInverseCoherentBandPhysicalMeanSquare_dyadic_lower
    (rho : NontrivialZetaZero) {K : ℕ} (hK : 1 ≤ K) :
    (‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 /
      (4 * ((pairedEtaInverseCoherenceScale rho + 2 : ℕ) : ℝ))) * (K : ℝ) ^ 2 ≤
      pairedEtaCompletedMomentInverseRegionPhysicalMeanSquare rho 0
        ((pairedEtaInverseCoherenceScale rho + 2) * K)
        ((pairedEtaInverseCoherenceScale rho + 2) * K)
        (pairedEtaInverseCoherentBand (pairedEtaInverseCoherenceScale rho) K) := by
  let c := pairedEtaInverseCoherenceScale rho + 2
  let A := c * K
  let S := pairedEtaInverseCoherentBand (pairedEtaInverseCoherenceScale rho) K
  have hc : 1 ≤ c := by dsimp [c]; omega
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hKA : K ≤ A := Nat.le_mul_of_pos_left K hc
  have hAR : (0 : ℝ) < A := by exact_mod_cast hK.trans hKA
  have hmono : pairedEtaCompletedMomentInverseRegionPhysicalMeanSquare rho 0 A K S * K ≤
      pairedEtaCompletedMomentInverseRegionPhysicalMeanSquare rho 0 A A S * A := by
    unfold pairedEtaCompletedMomentInverseRegionPhysicalMeanSquare
    rw [div_mul_cancel₀ _ hKR.ne', div_mul_cancel₀ _ hAR.ne']
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hKA) (fun r _ _ ↦ sq_nonneg _)
  have hlower := mul_le_mul_of_nonneg_right
    (pairedEtaCompletedMomentInverseCoherentBandPhysicalMeanSquare_lower rho hK) hKR.le
  calc
    _ = ((‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 4 * (K : ℝ) ^ 2) * K) / (A : ℝ) := by
      change (‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / (4 * (c : ℝ))) * (K : ℝ) ^ 2 = _
      dsimp [A]
      push_cast
      field_simp
    _ ≤ _ := (div_le_iff₀ hAR).mpr (hlower.trans hmono)

/-- The literal product coefficient energy is only linear on the same original inverse band. -/
theorem pairedEtaCompletedMomentInverseCoherentBand_coefficient_energy
    (rho : NontrivialZetaZero) (K : ℕ) :
    (∑ n ∈ Finset.Icc 1 ((pairedEtaInverseCoherenceScale rho + 2) * K),
      (pairedEtaInverseRegionCoefficient (pairedEtaInverseCoherentBand (pairedEtaInverseCoherenceScale rho) K) n : ℝ) ^ 2) = K :=
  sum_sq_pairedEtaInverseRegionCoefficient_coherentBand _ _

/-- The physical energy per unit of actual signed coefficient energy
has a linear lower bound on proportional windows at every actual zero. -/
theorem pairedEtaCompletedMomentInverseCoherentBand_energy_ratio_lower
    (rho : NontrivialZetaZero) {K : ℕ} (hK : 1 ≤ K) :
    (‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 4) * K ≤
      pairedEtaCompletedMomentInverseRegionPhysicalMeanSquare rho 0
        ((pairedEtaInverseCoherenceScale rho + 2) * K) K
        (pairedEtaInverseCoherentBand (pairedEtaInverseCoherenceScale rho) K) /
      (∑ n ∈ Finset.Icc 1 ((pairedEtaInverseCoherenceScale rho + 2) * K),
        (pairedEtaInverseRegionCoefficient (pairedEtaInverseCoherentBand (pairedEtaInverseCoherenceScale rho) K) n : ℝ) ^ 2) := by
  rw [pairedEtaCompletedMomentInverseCoherentBand_coefficient_energy]
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  apply (le_div_iff₀ hKR).mpr
  simpa only [pow_two, mul_assoc] using
    pairedEtaCompletedMomentInverseCoherentBandPhysicalMeanSquare_lower rho hK

end

end RiemannGaussian
