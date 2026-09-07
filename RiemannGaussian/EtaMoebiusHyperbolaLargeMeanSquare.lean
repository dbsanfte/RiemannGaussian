import RiemannGaussian.EtaMoebiusHyperbolaLowMeanSquare

/-!
# The full signed quotient-block mean square

The large-divisor energy is exactly the sum of the complex correlations
of its zero-extended quotient blocks on the original square window.
All off-diagonal terms and the moving quotient boundary are retained.
No operator estimate or large-half decay is asserted.
-/

open Complex
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- Mean square of the actual large-divisor aggregate on a physical window, with its full window-length normalization. -/
def pairedEtaCompletedMoebiusLargeMeanSquare (rho : NontrivialZetaZero) (A L D : ℕ) : ℝ :=
  (∑ n ∈ Finset.range L, ‖pairedEtaCompletedMoebiusLargeAggregate rho (A + n) D‖ ^ 2) / L

/-- The entire large-divisor mean square is nonnegative. -/
theorem pairedEtaCompletedMoebiusLargeMeanSquare_nonneg
    (rho : NontrivialZetaZero) (A L D : ℕ) :
    0 ≤ pairedEtaCompletedMoebiusLargeMeanSquare rho A L D := by
  exact div_nonneg (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)) (Nat.cast_nonneg L)

/-- The full complex correlation of two actual quotient blocks, retaining the physical window and their moving zero extension. -/
def pairedEtaCompletedMoebiusQuotientBlockCorrelation
    (rho : NontrivialZetaZero) (D A L q r : ℕ) : ℂ :=
  (∑ n ∈ Finset.range L,
    pairedEtaCompletedMoebiusLargeQuotientFamily rho D (A + n) q *
      starRingEnd ℂ (pairedEtaCompletedMoebiusLargeQuotientFamily rho D (A + n) r)) / L

/-- The square of the actual large half equals its complete complex quotient-pair sum at every point of a dyadic square window. -/
theorem pairedEtaCompletedMoebiusLargeAggregate_norm_sq_eq_quotientPairs
    (rho : NontrivialZetaZero) {D M : ℕ} (hD : 1 ≤ D)
    (hMlo : D ^ 2 ≤ M) (hMhi : M < 2 * D ^ 2) :
    (‖pairedEtaCompletedMoebiusLargeAggregate rho M D‖ : ℂ) ^ 2 =
      ∑ q ∈ Finset.Icc 1 (2 * D), ∑ r ∈ Finset.Icc 1 (2 * D),
        pairedEtaCompletedMoebiusLargeQuotientFamily rho D M q *
          starRingEnd ℂ (pairedEtaCompletedMoebiusLargeQuotientFamily rho D M r) := by
  rw [← Complex.mul_conj', pairedEtaCompletedMoebiusLargeAggregate_eq_fixedQuotientFamily rho hD hMlo hMhi]
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The full large-half energy is exactly the double sum of actual block correlations, with every cross term and the factor of the averaging length retained. -/
theorem pairedEtaCompletedMoebiusLargeMeanSquare_eq_quotientCorrelations
    (rho : NontrivialZetaZero) {D : ℕ} (hD : 1 ≤ D) :
    (pairedEtaCompletedMoebiusLargeMeanSquare rho (D ^ 2) (D ^ 2) D : ℂ) =
      ∑ q ∈ Finset.Icc 1 (2 * D), ∑ r ∈ Finset.Icc 1 (2 * D),
        pairedEtaCompletedMoebiusQuotientBlockCorrelation rho D (D ^ 2) (D ^ 2) q r := by
  unfold pairedEtaCompletedMoebiusLargeMeanSquare pairedEtaCompletedMoebiusQuotientBlockCorrelation
  push_cast
  simp only [← Finset.sum_div]
  congr 1
  calc
    _ = ∑ n ∈ Finset.range (D ^ 2), ∑ q ∈ Finset.Icc 1 (2 * D), ∑ r ∈ Finset.Icc 1 (2 * D),
        pairedEtaCompletedMoebiusLargeQuotientFamily rho D (D ^ 2 + n) q *
          starRingEnd ℂ (pairedEtaCompletedMoebiusLargeQuotientFamily rho D (D ^ 2 + n) r) := by
      apply Finset.sum_congr rfl
      intro n hn
      apply pairedEtaCompletedMoebiusLargeAggregate_norm_sq_eq_quotientPairs rho hD (by omega)
      have := Finset.mem_range.mp hn
      omega
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.sum_comm]

end

end RiemannGaussian
