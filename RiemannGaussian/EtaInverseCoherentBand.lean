import RiemannGaussian.EtaMomentInverseRegion

/-!
# An actual divisor band coherent on a proportional physical window

The original inner Möbius factor is one on this band. All divided
cutoffs remain one while the physical index varies through a window
whose length is a fixed positive fraction of its starting cutoff.
The exact original complex inverse therefore remains constant.
-/

open Complex
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- A zero-dependent integer scale retaining the complete ordinate in the phase comparison. -/
def pairedEtaInverseCoherenceScale (rho : NontrivialZetaZero) : ℕ :=
  4 * (1 + ⌈‖rho.1‖⌉₊)

/-- The coherence scale is at least four. -/
theorem four_le_pairedEtaInverseCoherenceScale (rho : NontrivialZetaZero) :
    4 ≤ pairedEtaInverseCoherenceScale rho := by
  unfold pairedEtaInverseCoherenceScale
  omega

/-- The actual zero's complete complex frequency is controlled by the chosen integer scale. -/
theorem four_norm_le_pairedEtaInverseCoherenceScale (rho : NontrivialZetaZero) :
    4 * ‖rho.1‖ ≤ (pairedEtaInverseCoherenceScale rho : ℝ) := by
  have h := Nat.le_ceil ‖rho.1‖
  unfold pairedEtaInverseCoherenceScale
  push_cast
  linarith

/-- The selected original inverse pairs have inner divisor one and midpoints spaced by two. -/
def pairedEtaInverseCoherentBand (B K : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range K).image (fun j ↦ (B * K + 2 * j + 1, 1))

/-- The entire selected band lies in its actual physical product region. -/
theorem pairedEtaInverseCoherentBand_subset (B K : ℕ) :
    pairedEtaInverseCoherentBand B K ⊆ pairedEtaInverseHyperbolicRegion ((B + 2) * K) := by
  intro p hp
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
  have hjK := Finset.mem_range.mp hj
  apply mem_pairedEtaInverseHyperbolicRegion.mpr
  refine ⟨by omega, by omega, ?_⟩
  simp only [mul_one, Nat.add_mul]
  omega

/-- Every selected pair keeps divided cutoff one throughout the entire physical window. -/
theorem div_eq_one_on_pairedEtaInverseCoherentBand {B K r j : ℕ}
    (hB : 4 ≤ B) (hr : r < K) (hj : j < K) :
    ((B + 2) * K + r) / (B * K + 2 * j + 1) = 1 := by
  have hd : 0 < B * K + 2 * j + 1 := by omega
  have hBK : 4 * K ≤ B * K := Nat.mul_le_mul_right K hB
  have hlo : 1 ≤ ((B + 2) * K + r) / (B * K + 2 * j + 1) := by
    apply (Nat.le_div_iff_mul_le hd).mpr
    simp only [Nat.add_mul, one_mul]
    omega
  have hhi : ((B + 2) * K + r) / (B * K + 2 * j + 1) < 2 := by
    apply (Nat.div_lt_iff_lt_mul hd).mpr
    simp only [Nat.add_mul]
    omega
  omega

/-- The full complex power sum of the selected original outer inverse weights. -/
def pairedEtaCoherentBandPowerSum (rho : NontrivialZetaZero) (B K : ℕ) : ℂ :=
  ∑ j ∈ Finset.range K, ((B * K + 2 * j + 1 : ℕ) : ℂ) ^ (-rho.1)

/-- At order zero and divided cutoff one, the original completed cell keeps its exact inverse power. -/
theorem pairedEtaCompletedMomentMoebiusTerm_zero_one (rho : NontrivialZetaZero) (a : ℝ) :
    pairedEtaCompletedMomentMoebiusTerm rho 0 a 1 1 = pairedEtaXiCompletionFactor rho.1 := by
  rw [pairedEtaCompletedMomentMoebiusTerm, pairedEtaUnpairedCenteredMomentPrefix_zero]
  norm_num [pairedEtaUnpairedDirichletPrefix, pairedEtaDirichletSign]
  field_simp [NontrivialZetaZero.coe_ne_zero rho]

/-- The entire original completed inverse band is constant on its physical window,
with the complete complex phase and completion factor retained. -/
theorem pairedEtaCompletedMomentInverseCoherentBand_eq_powerSum
    (rho : NontrivialZetaZero) (a : ℝ) {B K r : ℕ} (hB : 4 ≤ B) (hr : r < K) :
    pairedEtaCompletedMomentInverseRegion rho 0 a ((B + 2) * K + r)
      (pairedEtaInverseCoherentBand B K) =
        pairedEtaXiCompletionFactor rho.1 * pairedEtaCoherentBandPowerSum rho B K := by
  unfold pairedEtaCompletedMomentInverseRegion pairedEtaInverseCoherentBand pairedEtaCoherentBandPowerSum
  rw [Finset.sum_image]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [div_eq_one_on_pairedEtaInverseCoherentBand hB hr (Finset.mem_range.mp hj),
      pairedEtaCompletedMomentMoebiusTerm_zero_one]
    ring
  · intro i hi j hj hij
    have h := congrArg Prod.fst hij
    change B * K + 2 * i + 1 = B * K + 2 * j + 1 at h
    omega

/-- Averaging the literal band on its proportional window preserves its exact complex square. -/
theorem pairedEtaCompletedMomentInverseCoherentBandMeanSquare_eq
    (rho : NontrivialZetaZero) {B K : ℕ} (hB : 4 ≤ B) (hK : 1 ≤ K) :
    pairedEtaCompletedMomentInverseRegionMeanSquare rho 0 ((B + 2) * K) K
      (pairedEtaInverseCoherentBand B K) =
        ‖pairedEtaXiCompletionFactor rho.1 * pairedEtaCoherentBandPowerSum rho B K‖ ^ 2 := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  unfold pairedEtaCompletedMomentInverseRegionMeanSquare
  have hsum : (∑ r ∈ Finset.range K,
      ‖pairedEtaCompletedMomentInverseRegion rho 0
        (Real.log (((B + 2) * K + r : ℕ) + 1 : ℝ)) ((B + 2) * K + r)
          (pairedEtaInverseCoherentBand B K)‖ ^ 2) =
      (K : ℝ) * ‖pairedEtaXiCompletionFactor rho.1 * pairedEtaCoherentBandPowerSum rho B K‖ ^ 2 := by
    calc
      _ = ∑ _r ∈ Finset.range K,
          ‖pairedEtaXiCompletionFactor rho.1 * pairedEtaCoherentBandPowerSum rho B K‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [pairedEtaCompletedMomentInverseCoherentBand_eq_powerSum rho _ hB (Finset.mem_range.mp hr)]
      _ = _ := by simp
  rw [hsum]
  field_simp

end

end RiemannGaussian
