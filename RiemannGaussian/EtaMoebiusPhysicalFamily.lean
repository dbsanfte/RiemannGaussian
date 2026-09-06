import RiemannGaussian.EtaMoebiusPhysicalNormalization

/-!
# The original divisor family at a common physical cutoff

This family contains the original completed Möbius terms without individual
endpoint multipliers. Its exact complex Gram is the original pair kernel.
The difference from the established endpoint family is retained as a complex
sum and bounded at the common physical scale over every physical divisor.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The first `D` original completed Möbius terms at physical cutoff `M`,
with their original complex divisor weights and genuine tails. -/
def pairedEtaCompletedMoebiusPartialAggregate (rho : NontrivialZetaZero) (M D : ℕ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 D, pairedEtaCompletedMoebiusTerm rho M d

/-- At the full physical range this is exactly the existing completed
tail aggregate, with no change to the original arithmetic carrier. -/
theorem pairedEtaCompletedMoebiusPartialAggregate_full (rho : NontrivialZetaZero) (M : ℕ) :
    pairedEtaCompletedMoebiusPartialAggregate rho M M = pairedEtaCompletedMoebiusTailAggregate rho M :=
  sum_pairedEtaCompletedMoebiusTerm rho M

/-- The original family's complex Gram retains every unmodified pair
kernel and both Möbius coefficients, including all off-diagonal terms. -/
theorem pairedEtaCompletedMoebiusPartialAggregate_norm_sq_eq_kernel
    (rho : NontrivialZetaZero) (M D : ℕ) :
    (‖pairedEtaCompletedMoebiusPartialAggregate rho M D‖ : ℂ) ^ 2 =
      ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
        pairedEtaCompletedMoebiusPairKernel rho M d e := by
  rw [← Complex.mul_conj']
  simp only [pairedEtaCompletedMoebiusPartialAggregate, map_sum, Finset.sum_mul,
    Finset.mul_sum, pairedEtaCompletedMoebiusPairKernel]
  rw [Finset.sum_comm]

/-- The common physical normalization has an exact complex error sum;
every individual endpoint multiplier remains available in that error. -/
theorem pairedEtaCompletedMoebiusPartialAggregate_physical_sub_endpoint
    (rho : NontrivialZetaZero) (M D : ℕ) :
    (M : ℂ) ^ rho.1 * pairedEtaCompletedMoebiusPartialAggregate rho M D -
      pairedEtaCompletedMoebiusEndpointFamily rho M D =
      ∑ d ∈ Finset.Icc 1 D, ((M : ℂ) ^ rho.1 -
        ((d * pairedEtaUnpairedOddEndpoint (M / d) : ℕ) : ℂ) ^ rho.1) *
          pairedEtaCompletedMoebiusTerm rho M d := by
  unfold pairedEtaCompletedMoebiusPartialAggregate pairedEtaCompletedMoebiusEndpointFamily
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp_rw [pairedEtaCompletedMoebiusTerm_physical_sub_endpoint]

/-- Replacing all endpoint powers by the common physical power costs
at most the explicit `D²/M` error over the entire physical divisor range. -/
theorem norm_pairedEtaCompletedMoebiusPartialAggregate_physical_sub_endpoint_le
    (rho : NontrivialZetaZero) {M D : ℕ} (hDM : D ≤ M) :
    ‖(M : ℂ) ^ rho.1 * pairedEtaCompletedMoebiusPartialAggregate rho M D -
      pairedEtaCompletedMoebiusEndpointFamily rho M D‖ ≤
      pairedEtaCompletedMoebiusPhysicalErrorConstant rho * (D : ℝ) ^ 2 / M := by
  have hB := pairedEtaCompletedMoebiusPhysicalErrorConstant_nonneg rho
  unfold pairedEtaCompletedMoebiusPartialAggregate pairedEtaCompletedMoebiusEndpointFamily
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _d ∈ Finset.Icc 1 D, pairedEtaCompletedMoebiusPhysicalErrorConstant rho * D / M := by
      apply Finset.sum_le_sum
      intro d hd
      have hdm : d ∈ Finset.Icc 1 M := Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hd).1, (Finset.mem_Icc.mp hd).2.trans hDM⟩
      apply (norm_pairedEtaCompletedMoebiusTerm_physical_sub_endpoint_le rho hdm).trans
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg M)
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast (Finset.mem_Icc.mp hd).2) hB
    _ = _ := by
      simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      ring

/-- The common physical power cancels from the original family square
with its exact real decay. This uses the actual zero's full complex power. -/
theorem pairedEtaCompletedMoebiusPartialAggregate_norm_sq_eq_physical
    (rho : NontrivialZetaZero) {M : ℕ} (hM : 1 ≤ M) (D : ℕ) :
    ‖pairedEtaCompletedMoebiusPartialAggregate rho M D‖ ^ 2 =
      (M : ℝ) ^ (-2 * rho.1.re) *
        ‖(M : ℂ) ^ rho.1 * pairedEtaCompletedMoebiusPartialAggregate rho M D‖ ^ 2 := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hp : ‖(M : ℂ) ^ rho.1‖ = (M : ℝ) ^ rho.1.re := by
    simpa only [Complex.ofReal_natCast] using Complex.norm_cpow_eq_rpow_re_of_pos hMR rho.1
  have hs : ((M : ℝ) ^ rho.1.re) ^ 2 = (M : ℝ) ^ (rho.1.re * 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hMR.le]
    norm_num
  rw [norm_mul, hp, mul_pow, hs]
  rw [← mul_assoc, ← Real.rpow_add hMR,
    show -2 * rho.1.re + rho.1.re * 2 = 0 by ring, Real.rpow_zero, one_mul]

end

end RiemannGaussian
