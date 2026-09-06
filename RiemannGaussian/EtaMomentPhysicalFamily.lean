import RiemannGaussian.EtaMomentPhysicalReduction

/-!
# The original moment family and its physical reduction

The moment family sums the unmodified completed divisor terms at one
explicit center. Its full complex pair kernel and exact reduction to the
zeroth-order family precede the norm estimate. Summation retains the
quadratic divisor cost and the original physical cutoff.
-/

open Complex
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- The original completed moment terms in the first `D` physical divisor columns. -/
def pairedEtaCompletedMomentOriginalFamily (rho : NontrivialZetaZero) (k : ℕ)
    (a : ℝ) (M D : ℕ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 D, pairedEtaCompletedMomentMoebiusTerm rho k a M d

/-- The full family is exactly the existing completed moment aggregate. -/
theorem pairedEtaCompletedMomentOriginalFamily_full (rho : NontrivialZetaZero)
    (k : ℕ) (a : ℝ) (M : ℕ) :
    pairedEtaCompletedMomentOriginalFamily rho k a M M =
      pairedEtaCompletedMomentMoebiusAggregate rho k a M := rfl

/-- At order zero the original family agrees with the previously bounded carrier. -/
theorem pairedEtaCompletedMomentOriginalFamily_zero (rho : NontrivialZetaZero)
    (a : ℝ) (M D : ℕ) :
    pairedEtaCompletedMomentOriginalFamily rho 0 a M D =
      pairedEtaCompletedMoebiusPartialAggregate rho M D := by
  simp only [pairedEtaCompletedMomentOriginalFamily, pairedEtaCompletedMomentMoebiusTerm_zero,
    pairedEtaCompletedMoebiusPartialAggregate]

/-- The full complex family square retains all original moment divisor pairs. -/
theorem pairedEtaCompletedMomentOriginalFamily_norm_sq_eq_pairs
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) (M D : ℕ) :
    (‖pairedEtaCompletedMomentOriginalFamily rho k a M D‖ : ℂ) ^ 2 =
      ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
        pairedEtaCompletedMomentMoebiusTerm rho k a M d *
          starRingEnd ℂ (pairedEtaCompletedMomentMoebiusTerm rho k a M e) := by
  rw [← Complex.mul_conj']
  simp only [pairedEtaCompletedMomentOriginalFamily, map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The exact family reduction retains the full complex coefficient
and every physical moment-to-zeroth-order term difference. -/
theorem pairedEtaCompletedMomentOriginalFamily_physical_sub_zero
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) (M D : ℕ) :
    (M : ℂ) ^ rho.1 * (pairedEtaCompletedMomentOriginalFamily rho k a M D -
      pairedEtaMomentParityCoefficient rho k * pairedEtaCompletedMoebiusPartialAggregate rho M D) =
      ∑ d ∈ Finset.Icc 1 D, (M : ℂ) ^ rho.1 *
        (pairedEtaCompletedMomentMoebiusTerm rho k a M d -
          pairedEtaMomentParityCoefficient rho k * pairedEtaCompletedMoebiusTerm rho M d) := by
  simp only [pairedEtaCompletedMomentOriginalFamily, pairedEtaCompletedMoebiusPartialAggregate,
    Finset.sum_sub_distrib, Finset.mul_sum, mul_sub]

/-- The original summed moment family reduces to its zeroth-order
counterpart with a uniform `D²/M` physical error at every admissible center. -/
theorem norm_pairedEtaCompletedMomentOriginalFamily_physical_sub_zero_le
    (rho : NontrivialZetaZero) {k M D : ℕ} (hk : k < analyticZetaZeroMultiplicity rho)
    (hDM : D ≤ M) {a : ℝ} (ha : Real.log (M : ℝ) ≤ a ∧ a ≤ Real.log (M + 1 : ℝ)) :
    ‖(M : ℂ) ^ rho.1 * (pairedEtaCompletedMomentOriginalFamily rho k a M D -
      pairedEtaMomentParityCoefficient rho k * pairedEtaCompletedMoebiusPartialAggregate rho M D)‖ ≤
      pairedEtaCompletedMomentPhysicalErrorConstant rho k * (D : ℝ) ^ 2 / M := by
  rw [pairedEtaCompletedMomentOriginalFamily_physical_sub_zero]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _d ∈ Finset.Icc 1 D, pairedEtaCompletedMomentPhysicalErrorConstant rho k * D / (M : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdm : d ∈ Finset.Icc 1 M := Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hd).1, (Finset.mem_Icc.mp hd).2.trans hDM⟩
      apply (norm_pairedEtaCompletedMomentMoebiusTerm_physical_sub_zero_le rho hk hdm ha).trans
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg M)
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast (Finset.mem_Icc.mp hd).2)
        (pairedEtaCompletedMomentPhysicalErrorConstant_nonneg rho k)
    _ = _ := by
      simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      ring

/-- The original family square retains the actual common physical
normalization and its exact horizontal decay exponent. -/
theorem pairedEtaCompletedMomentOriginalFamily_norm_sq_eq_physical
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) {M : ℕ} (hM : 1 ≤ M) (D : ℕ) :
    ‖pairedEtaCompletedMomentOriginalFamily rho k a M D‖ ^ 2 =
      (M : ℝ) ^ (-2 * rho.1.re) *
        ‖(M : ℂ) ^ rho.1 * pairedEtaCompletedMomentOriginalFamily rho k a M D‖ ^ 2 := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hp : ‖(M : ℂ) ^ rho.1‖ = (M : ℝ) ^ rho.1.re := by
    simpa only [Complex.ofReal_natCast] using Complex.norm_cpow_eq_rpow_re_of_pos hMR rho.1
  have hs : ((M : ℝ) ^ rho.1.re) ^ 2 = (M : ℝ) ^ (rho.1.re * 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hMR.le]
    norm_num
  rw [norm_mul, hp, mul_pow, hs, ← mul_assoc, ← Real.rpow_add hMR,
    show -2 * rho.1.re + rho.1.re * 2 = 0 by ring, Real.rpow_zero, one_mul]

end

end RiemannGaussian
