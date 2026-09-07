import RiemannGaussian.EtaCoherentBandLowerBound

/-!
# The necessary mixed cancellation with the full moving inverse complement

The coherent band is kept together with every remaining original inverse
cell at the actual physical index. Their exact complex sum is the complete
eta prefix. This gives a quantitative negative mixed term, showing where
the growing separate-band energy is cancelled on proportional windows.
-/

open Complex
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- The actual hyperbolic divisor regions increase with their physical cutoff. -/
theorem pairedEtaInverseHyperbolicRegion_mono {T M : ℕ} (hTM : T ≤ M) :
    pairedEtaInverseHyperbolicRegion T ⊆ pairedEtaInverseHyperbolicRegion M := by
  intro p hp
  obtain ⟨hd, he, hprod⟩ := mem_pairedEtaInverseHyperbolicRegion.mp hp
  exact mem_pairedEtaInverseHyperbolicRegion.mpr ⟨hd, he, hprod.trans hTM⟩

/-- The full actual hyperbola reconstructs the original completed centered prefix. -/
theorem pairedEtaCompletedMomentInverseRegion_full (rho : NontrivialZetaZero)
    (k : ℕ) (a : ℝ) (M : ℕ) :
    pairedEtaCompletedMomentInverseRegion rho k a M (pairedEtaInverseHyperbolicRegion M) =
      (pairedEtaXiCompletionFactor rho.1 * rho.1) * pairedEtaUnpairedCenteredMomentPrefix k rho.1 a M := by
  have hband : pairedEtaInverseHyperbolicBand M 0 M = pairedEtaInverseHyperbolicRegion M := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    obtain ⟨hd, he, hprod⟩ := mem_pairedEtaInverseHyperbolicRegion.mp hp
    exact ⟨hd, (Nat.le_mul_of_pos_right p.1 he).trans hprod⟩
  rw [← hband, pairedEtaCompletedMomentInverseHyperbolicBand_eq_sum]
  have hI : Finset.Ioc 0 M = Finset.Icc 1 M := by ext d; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  simp_rw [hI, pairedEtaCompletedMomentInversePartialTerm_full]
  exact sum_pairedEtaCompletedMomentInverseTerm rho k a M

/-- At order zero the whole inverse is exactly the original completed Dirichlet prefix. -/
theorem pairedEtaCompletedMomentInverseRegion_full_zero (rho : NontrivialZetaZero)
    (a : ℝ) (M : ℕ) :
    pairedEtaCompletedMomentInverseRegion rho 0 a M (pairedEtaInverseHyperbolicRegion M) =
      pairedEtaXiCompletionFactor rho.1 * pairedEtaUnpairedDirichletPrefix M rho.1 := by
  rw [pairedEtaCompletedMomentInverseRegion_full, pairedEtaUnpairedCenteredMomentPrefix_zero]
  field_simp [NontrivialZetaZero.coe_ne_zero rho]

/-- The full original inverse has a uniform physical norm after its exact cancellation. -/
theorem norm_pairedEtaCompletedMomentInverseRegion_full_physical_le
    (rho : NontrivialZetaZero) (a : ℝ) {M : ℕ} (hM : 1 ≤ M) :
    ‖(M : ℂ) ^ rho.1 * pairedEtaCompletedMomentInverseRegion rho 0 a M
      (pairedEtaInverseHyperbolicRegion M)‖ ≤
      ‖pairedEtaXiCompletionFactor rho.1‖ * (‖rho.1‖ / rho.1.re + 1) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hnorm : ‖(M : ℂ) ^ rho.1‖ = (M : ℝ) ^ rho.1.re := by
    simpa only [Complex.ofReal_natCast] using Complex.norm_cpow_eq_rpow_re_of_pos hMR rho.1
  rw [pairedEtaCompletedMomentInverseRegion_full_zero, norm_mul, norm_mul, hnorm]
  calc
    _ ≤ (M : ℝ) ^ rho.1.re * (‖pairedEtaXiCompletionFactor rho.1‖ *
        ((‖rho.1‖ / rho.1.re + 1) * (M : ℝ) ^ (-rho.1.re))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (norm_pairedEtaUnpairedDirichletPrefix_le rho hM) (norm_nonneg _)) (by positivity)
    _ = _ := by
      rw [show (M : ℝ) ^ rho.1.re * (‖pairedEtaXiCompletionFactor rho.1‖ *
          ((‖rho.1‖ / rho.1.re + 1) * (M : ℝ) ^ (-rho.1.re))) =
          (‖pairedEtaXiCompletionFactor rho.1‖ * (‖rho.1‖ / rho.1.re + 1)) *
            ((M : ℝ) ^ rho.1.re * (M : ℝ) ^ (-rho.1.re)) by ring,
        ← Real.rpow_add hMR, add_neg_cancel, Real.rpow_zero, mul_one]

/-- Every remaining original inverse cell at the actual moving physical index. -/
def pairedEtaInverseCoherentComplement (B K M : ℕ) : Finset (ℕ × ℕ) :=
  pairedEtaInverseHyperbolicRegion M \ pairedEtaInverseCoherentBand B K

/-- The coherent band and its complete moving complement reconstruct the full original inverse. -/
theorem pairedEtaCompletedMomentInverseCoherentComplement_add_band
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) (B K r : ℕ) :
    pairedEtaCompletedMomentInverseRegion rho k a ((B + 2) * K + r)
        (pairedEtaInverseCoherentComplement B K ((B + 2) * K + r)) +
      pairedEtaCompletedMomentInverseRegion rho k a ((B + 2) * K + r)
        (pairedEtaInverseCoherentBand B K) =
      pairedEtaCompletedMomentInverseRegion rho k a ((B + 2) * K + r)
        (pairedEtaInverseHyperbolicRegion ((B + 2) * K + r)) := by
  unfold pairedEtaCompletedMomentInverseRegion pairedEtaInverseCoherentComplement
  exact Finset.sum_sdiff ((pairedEtaInverseCoherentBand_subset B K).trans
    (pairedEtaInverseHyperbolicRegion_mono (Nat.le_add_right _ _)))

/-- The complete complex cross term cancels the coherent diagonal,
leaving its exact product with the full completed eta prefix. -/
theorem pairedEtaCompletedMomentInverseCoherentComplement_cross_eq
    (rho : NontrivialZetaZero) (a : ℝ) (B K r : ℕ) :
    let M := (B + 2) * K + r
    let P := (M : ℂ) ^ rho.1 * pairedEtaCompletedMomentInverseRegion rho 0 a M (pairedEtaInverseCoherentBand B K)
    let Q := (M : ℂ) ^ rho.1 * pairedEtaCompletedMomentInverseRegion rho 0 a M (pairedEtaInverseCoherentComplement B K M)
    Q * starRingEnd ℂ P + (‖P‖ : ℂ) ^ 2 =
      ((M : ℂ) ^ rho.1 * pairedEtaXiCompletionFactor rho.1 * pairedEtaUnpairedDirichletPrefix M rho.1) *
        starRingEnd ℂ P := by
  dsimp only
  rw [← Complex.mul_conj', ← add_mul, ← mul_add,
    pairedEtaCompletedMomentInverseCoherentComplement_add_band,
    pairedEtaCompletedMomentInverseRegion_full_zero]
  ring

/-- The physical mixed correction is at most the full prefix bound times the coherent band norm. -/
theorem norm_pairedEtaCompletedMomentInverseCoherentComplement_cross_correction_le
    (rho : NontrivialZetaZero) (a : ℝ) {B K r : ℕ} (hK : 1 ≤ K) :
    let M := (B + 2) * K + r
    let P := (M : ℂ) ^ rho.1 * pairedEtaCompletedMomentInverseRegion rho 0 a M (pairedEtaInverseCoherentBand B K)
    let Q := (M : ℂ) ^ rho.1 * pairedEtaCompletedMomentInverseRegion rho 0 a M (pairedEtaInverseCoherentComplement B K M)
    ‖Q * starRingEnd ℂ P + (‖P‖ : ℂ) ^ 2‖ ≤
      (‖pairedEtaXiCompletionFactor rho.1‖ * (‖rho.1‖ / rho.1.re + 1)) * ‖P‖ := by
  dsimp only
  rw [pairedEtaCompletedMomentInverseCoherentComplement_cross_eq]
  have hM : 1 ≤ (B + 2) * K + r := by nlinarith
  have h := norm_pairedEtaCompletedMomentInverseRegion_full_physical_le rho a hM
  rw [pairedEtaCompletedMomentInverseRegion_full_zero, ← mul_assoc] at h
  rw [norm_mul, norm_conj]
  exact mul_le_mul_of_nonneg_right h (norm_nonneg _)

/-- The full moving complement has a quantitatively negative mixed
interaction with the actual coherent band on every sufficiently large proportional window. -/
theorem pairedEtaCompletedMomentInverseCoherentComplement_cross_re_le
    (rho : NontrivialZetaZero) (a : ℝ) {K r : ℕ} (hK : 1 ≤ K) (hr : r < K)
    (hlarge : 4 * (‖rho.1‖ / rho.1.re + 1) ≤ (K : ℝ)) :
    let B := pairedEtaInverseCoherenceScale rho
    let M := (B + 2) * K + r
    let P := (M : ℂ) ^ rho.1 * pairedEtaCompletedMomentInverseRegion rho 0 a M (pairedEtaInverseCoherentBand B K)
    let Q := (M : ℂ) ^ rho.1 * pairedEtaCompletedMomentInverseRegion rho 0 a M (pairedEtaInverseCoherentComplement B K M)
    (Q * starRingEnd ℂ P).re ≤ -(‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 8) * (K : ℝ) ^ 2 := by
  dsimp only
  let B := pairedEtaInverseCoherenceScale rho
  let M := (B + 2) * K + r
  let P := (M : ℂ) ^ rho.1 * pairedEtaCompletedMomentInverseRegion rho 0 a M (pairedEtaInverseCoherentBand B K)
  let Q := (M : ℂ) ^ rho.1 * pairedEtaCompletedMomentInverseRegion rho 0 a M (pairedEtaInverseCoherentComplement B K M)
  change (Q * starRingEnd ℂ P).re ≤ _
  have hlower : (‖pairedEtaXiCompletionFactor rho.1‖ / 2) * K ≤ ‖P‖ :=
    pairedEtaCompletedMomentInverseCoherentBand_physical_norm_lower rho a
      (four_le_pairedEtaInverseCoherenceScale rho) hK hr (four_norm_le_pairedEtaInverseCoherenceScale rho)
  have he : ‖Q * starRingEnd ℂ P + (‖P‖ : ℂ) ^ 2‖ ≤
      (‖pairedEtaXiCompletionFactor rho.1‖ * (‖rho.1‖ / rho.1.re + 1)) * ‖P‖ :=
    norm_pairedEtaCompletedMomentInverseCoherentComplement_cross_correction_le rho a hK
  have hre := (Complex.re_le_norm (Q * starRingEnd ℂ P + (‖P‖ : ℂ) ^ 2)).trans he
  simp only [Complex.add_re, ← Complex.ofReal_pow, Complex.ofReal_re] at hre
  have hscaled := mul_le_mul_of_nonneg_left hlarge (norm_nonneg (pairedEtaXiCompletionFactor rho.1))
  have hhalf : ‖pairedEtaXiCompletionFactor rho.1‖ * (‖rho.1‖ / rho.1.re + 1) ≤ ‖P‖ / 2 := by
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hhalf (norm_nonneg P)
  have hs := (sq_le_sq₀ (by positivity) (norm_nonneg P)).mpr hlower
  nlinarith

end

end RiemannGaussian
