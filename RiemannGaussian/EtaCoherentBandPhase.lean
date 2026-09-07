import RiemannGaussian.EtaInverseCoherentBand
import RiemannGaussian.EtaOddPowerQuadrature

/-!
# Quantitative complex phase coherence in the actual inverse band

The original power sum is compared with its full complex anchor, before
taking a norm. A scale chosen from the actual zero makes the complete
phase error at most half the anchored main term, uniformly in the size
of the physical window.
-/

open Complex
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- Every original inverse power stays within a quantitative complex neighborhood of the common anchor. -/
theorem norm_coherentBand_cpow_sub_anchor_le (rho : NontrivialZetaZero)
    {B K j : ℕ} (hB : 1 ≤ B) (hK : 1 ≤ K) (hj : j < K)
    (hphase : 4 * ‖rho.1‖ ≤ (B : ℝ)) :
    ‖((B * K + 2 * j + 1 : ℕ) : ℂ) ^ (-rho.1) - ((B * K : ℕ) : ℂ) ^ (-rho.1)‖ ≤
      (1 / 2 : ℝ) * (B * K : ℕ) ^ (-rho.1.re) := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hbase : (0 : ℝ) < (B * K : ℕ) := by exact_mod_cast Nat.mul_pos hB hK
  have h := norm_cpow_sub_cpow_le_above (-rho.1) hbase
    (by simp only [Complex.neg_re]; linarith [NontrivialZetaZero.zero_lt_re rho]) le_rfl
    (show ((B * K : ℕ) : ℝ) ≤ (B * K + 2 * j + 1 : ℕ) by exact_mod_cast (by omega : B * K ≤ B * K + 2 * j + 1))
  have hd : |((B * K + 2 * j + 1 : ℕ) : ℝ) - (B * K : ℕ)| ≤ 2 * (K : ℝ) := by
    have hjR : (j : ℝ) + 1 ≤ K := by exact_mod_cast hj
    push_cast
    rw [show (B : ℝ) * K + 2 * j + 1 - B * K = 2 * j + 1 by ring,
      abs_of_nonneg (by positivity)]
    linarith
  calc
    _ ≤ ‖rho.1‖ * (B * K : ℕ) ^ (-rho.1.re - 1) *
        |((B * K + 2 * j + 1 : ℕ) : ℝ) - (B * K : ℕ)| := by
      simpa only [Complex.ofReal_natCast, norm_neg, Complex.neg_re] using h
    _ ≤ ‖rho.1‖ * (B * K : ℕ) ^ (-rho.1.re - 1) * (2 * K) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = (2 * ‖rho.1‖ / B) * (B * K : ℕ) ^ (-rho.1.re) := by
      rw [Real.rpow_sub hbase, Real.rpow_one]
      push_cast
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      ((div_le_iff₀ hBR).mpr (by linarith)) (Real.rpow_nonneg hbase.le _)

/-- The complete signed complex power sum retains its common anchor with at most half its magnitude in error. -/
theorem norm_pairedEtaCoherentBandPowerSum_sub_anchor_le (rho : NontrivialZetaZero)
    {B K : ℕ} (hB : 1 ≤ B) (hK : 1 ≤ K) (hphase : 4 * ‖rho.1‖ ≤ (B : ℝ)) :
    ‖pairedEtaCoherentBandPowerSum rho B K - (K : ℂ) * ((B * K : ℕ) : ℂ) ^ (-rho.1)‖ ≤
      ((K : ℝ) / 2) * (B * K : ℕ) ^ (-rho.1.re) := by
  have he : pairedEtaCoherentBandPowerSum rho B K - (K : ℂ) * ((B * K : ℕ) : ℂ) ^ (-rho.1) =
      ∑ j ∈ Finset.range K,
        (((B * K + 2 * j + 1 : ℕ) : ℂ) ^ (-rho.1) - ((B * K : ℕ) : ℂ) ^ (-rho.1)) := by
    simp only [pairedEtaCoherentBandPowerSum, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
  rw [he]
  calc
    _ ≤ ∑ j ∈ Finset.range K,
        ‖((B * K + 2 * j + 1 : ℕ) : ℂ) ^ (-rho.1) - ((B * K : ℕ) : ℂ) ^ (-rho.1)‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range K, (1 / 2 : ℝ) * (B * K : ℕ) ^ (-rho.1.re) :=
      Finset.sum_le_sum (fun j hj ↦ norm_coherentBand_cpow_sub_anchor_le rho hB hK (Finset.mem_range.mp hj) hphase)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- The whole original inverse band retains a positive coherent magnitude after every phase is summed. -/
theorem pairedEtaCoherentBandPowerSum_norm_lower (rho : NontrivialZetaZero)
    {B K : ℕ} (hB : 1 ≤ B) (hK : 1 ≤ K) (hphase : 4 * ‖rho.1‖ ≤ (B : ℝ)) :
    ((K : ℝ) / 2) * (B * K : ℕ) ^ (-rho.1.re) ≤ ‖pairedEtaCoherentBandPowerSum rho B K‖ := by
  have hbase : (0 : ℝ) < (B * K : ℕ) := by exact_mod_cast Nat.mul_pos hB hK
  have hn : ‖(K : ℂ) * ((B * K : ℕ) : ℂ) ^ (-rho.1)‖ =
      (K : ℝ) * (B * K : ℕ) ^ (-rho.1.re) := by
    rw [norm_mul, Complex.norm_natCast]
    congr 1
    simpa only [Complex.ofReal_natCast, Complex.neg_re] using
      Complex.norm_cpow_eq_rpow_re_of_pos hbase (-rho.1)
  have ht := norm_le_insert' ((K : ℂ) * ((B * K : ℕ) : ℂ) ^ (-rho.1))
    (pairedEtaCoherentBandPowerSum rho B K)
  rw [hn, norm_sub_rev] at ht
  linarith [norm_pairedEtaCoherentBandPowerSum_sub_anchor_le rho hB hK hphase]

end

end RiemannGaussian
