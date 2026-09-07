import RiemannGaussian.MoebiusDividedCutoffBlocks
import RiemannGaussian.EtaMomentMoebiusTransform

/-!
# Finite Möbius block cancellation on the original completed eta carrier

Every zeroth-order completed divisor term keeps its original divided
cutoff and possible odd endpoint. Grouping terms with the same quotient
retains their full complex Möbius coefficient. The checked finite arithmetic
cancellation then bounds that actual block with its completion and
zero-dependent endpoint decay. The full inverse and its reflected mixed
energies still require a stronger joint estimate.
-/

open Complex
open scoped ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- A genuine divided-cutoff block of the original zeroth completed moments retains its full complex arithmetic coefficient, completion, and unpaired endpoint. -/
theorem sum_pairedEtaCompletedMomentMoebiusTerm_zero_divided_block
    (rho : NontrivialZetaZero) (a : ℝ) (M q : ℕ) :
    (∑ d ∈ (Finset.Icc 1 M).filter (fun d ↦ M / d = q),
      pairedEtaCompletedMomentMoebiusTerm rho 0 a M d) =
        complexMoebiusDividedCutoffBlock rho.1 M q *
          (pairedEtaXiCompletionFactor rho.1 * pairedEtaUnpairedDirichletPrefix q rho.1) := by
  rw [complexMoebiusDividedCutoffBlock, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [pairedEtaCompletedMomentMoebiusTerm_zero, pairedEtaCompletedMoebiusTerm_eq_completed_prefix,
    (Finset.mem_filter.mp hd).2]

/-- Every prescribed power-scale coefficient has one all-cutoff remainder for the actual completed quotient blocks, retaining their precise zero-dependent endpoint decay. -/
theorem exists_pairedEtaCompletedMoebius_divided_block_remainder
    (rho : NontrivialZetaZero) {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℝ) (M q : ℕ), 0 < q →
      ‖∑ d ∈ (Finset.Icc 1 M).filter (fun d ↦ M / d = q),
        pairedEtaCompletedMomentMoebiusTerm rho 0 a M d‖ ≤
          (eps * ((M / q : ℕ) + 1 : ℝ) ^ (1 - rho.1.re) + C) *
            (‖pairedEtaXiCompletionFactor rho.1‖ * (‖rho.1‖ / rho.1.re + 1) *
              (q : ℝ) ^ (-rho.1.re)) := by
  obtain ⟨C, hC, hblock⟩ := exists_complexMoebiusDividedCutoffBlock_power_remainder
    (NontrivialZetaZero.zero_lt_re rho) (NontrivialZetaZero.re_lt_one rho) heps
  refine ⟨C, hC, fun a M q hq ↦ ?_⟩
  have hpre := norm_pairedEtaUnpairedDirichletPrefix_le rho hq
  have hfactor : ‖pairedEtaXiCompletionFactor rho.1 * pairedEtaUnpairedDirichletPrefix q rho.1‖ ≤
      ‖pairedEtaXiCompletionFactor rho.1‖ * (‖rho.1‖ / rho.1.re + 1) * (q : ℝ) ^ (-rho.1.re) := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hpre (norm_nonneg _)).trans_eq (by ring)
  rw [sum_pairedEtaCompletedMomentMoebiusTerm_zero_divided_block, norm_mul]
  exact mul_le_mul (hblock M q hq) hfactor (norm_nonneg _) (by positivity)

end

end RiemannGaussian
