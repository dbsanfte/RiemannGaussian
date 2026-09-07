import RiemannGaussian.EtaMoebiusTwoThirdsMeanSquare
import RiemannGaussian.EtaMoebiusClippedQuotientBlocks

/-!
# The remaining cube-root quotient form

After controlling all divisors through `D²` on `[D³,2D³)`, the entire
remaining source lies in a clipped quotient family on `q ≤ 2D`. Its
complex quadratic form retains all cross terms and the exact physical
window. The source concentration has the proved enlarged-range allowance;
decay of the remaining quotient form is still open.
-/

open Complex Filter
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- The complete complex correlation of two clipped quotient blocks on the original physical window. -/
def pairedEtaCompletedMoebiusClippedQuotientCorrelation
    (rho : NontrivialZetaZero) (A L D q r : ℕ) : ℂ :=
  (∑ n ∈ Finset.range L,
    pairedEtaCompletedMoebiusClippedQuotientBlock rho (A + n) D q *
      starRingEnd ℂ (pairedEtaCompletedMoebiusClippedQuotientBlock rho (A + n) D r)) / L

/-- Every large-half square beyond the two-thirds divisor cutoff retains its exact clipped quotient-pair expansion. -/
theorem pairedEtaCompletedMoebiusLargeAggregate_twoThirds_norm_sq_eq_pairs
    (rho : NontrivialZetaZero) {M D : ℕ} (hM : M < 2 * D ^ 3) :
    (‖pairedEtaCompletedMoebiusLargeAggregate rho M (D ^ 2)‖ : ℂ) ^ 2 =
      ∑ q ∈ Finset.Icc 1 (2 * D), ∑ r ∈ Finset.Icc 1 (2 * D),
        pairedEtaCompletedMoebiusClippedQuotientBlock rho M (D ^ 2) q *
          starRingEnd ℂ (pairedEtaCompletedMoebiusClippedQuotientBlock rho M (D ^ 2) r) := by
  rw [← Complex.mul_conj', pairedEtaCompletedMoebiusLargeAggregate_twoThirds_eq_fixedClippedQuotients rho hM]
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The entire remaining large-half mean square is exactly a cube-root-dimensional quotient correlation form, including the clipped boundary and every off-diagonal term. -/
theorem pairedEtaCompletedMoebiusLargeMeanSquare_twoThirds_eq_quotientCorrelations
    (rho : NontrivialZetaZero) (D : ℕ) :
    (pairedEtaCompletedMoebiusLargeMeanSquare rho (D ^ 3) (D ^ 3) (D ^ 2) : ℂ) =
      ∑ q ∈ Finset.Icc 1 (2 * D), ∑ r ∈ Finset.Icc 1 (2 * D),
        pairedEtaCompletedMoebiusClippedQuotientCorrelation rho (D ^ 3) (D ^ 3) (D ^ 2) q r := by
  unfold pairedEtaCompletedMoebiusLargeMeanSquare pairedEtaCompletedMoebiusClippedQuotientCorrelation
  push_cast
  simp only [← Finset.sum_div]
  congr 1
  calc
    _ = ∑ n ∈ Finset.range (D ^ 3), ∑ q ∈ Finset.Icc 1 (2 * D), ∑ r ∈ Finset.Icc 1 (2 * D),
        pairedEtaCompletedMoebiusClippedQuotientBlock rho (D ^ 3 + n) (D ^ 2) q *
          starRingEnd ℂ (pairedEtaCompletedMoebiusClippedQuotientBlock rho (D ^ 3 + n) (D ^ 2) r) := by
      apply Finset.sum_congr rfl
      intro n hn
      apply pairedEtaCompletedMoebiusLargeAggregate_twoThirds_norm_sq_eq_pairs
      have := Finset.mem_range.mp hn
      omega
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.sum_comm]

/-- The large half beyond the enlarged divisor range concentrates around the original nonzero source with the full new allowance and its signed cross-term cost. -/
theorem pairedEtaCompletedMoebiusLargeMeanSquare_twoThirds_source_error_le
    (rho : NontrivialZetaZero) {D : ℕ} (hD : 2 ≤ D) :
    |pairedEtaCompletedMoebiusLargeMeanSquare rho (D ^ 3) (D ^ 3) (D ^ 2) -
      ‖pairedEtaCompletedMoebiusSource rho‖ ^ 2| ≤ pairedEtaMoebiusTwoThirdsAllowance rho D +
        2 * ‖pairedEtaCompletedMoebiusSource rho‖ * Real.sqrt (pairedEtaMoebiusTwoThirdsAllowance rho D) := by
  have hD2 : 2 ≤ D ^ 2 := by nlinarith
  have h23 : D ^ 2 ≤ D ^ 3 := by nlinarith [Nat.mul_le_mul_left (D ^ 2) (by omega : 1 ≤ D)]
  apply (pairedEtaCompletedMoebiusLargeMeanSquare_source_error_le rho (hD2.trans h23)
    (by omega : 0 < D ^ 3) h23).trans
  have hu := pairedEtaCompletedMoebiusOriginalMeanSquare_twoThirds_le rho (by omega : 1 ≤ D)
  exact add_le_add hu (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hu) (by positivity))

/-- Under a hypothetical right-half-zero assumption, the exact remaining cube-root quotient form retains the positive source square in the limit. -/
theorem pairedEtaCompletedMoebiusLargeMeanSquare_twoThirds_tendsto_source
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    Tendsto (fun D : ℕ ↦ pairedEtaCompletedMoebiusLargeMeanSquare rho (D ^ 3) (D ^ 3) (D ^ 2))
      atTop (𝓝 (‖pairedEtaCompletedMoebiusSource rho‖ ^ 2)) := by
  have hu := pairedEtaMoebiusTwoThirdsAllowance_tendsto_zero rho hrho
  have hb := hu.add (hu.sqrt.const_mul (2 * ‖pairedEtaCompletedMoebiusSource rho‖))
  simp only [Real.sqrt_zero, mul_zero, add_zero] at hb
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [Real.norm_eq_abs]
  exact squeeze_zero' (Eventually.of_forall (fun _ ↦ abs_nonneg _))
    ((eventually_ge_atTop 2).mono fun _ hD ↦ pairedEtaCompletedMoebiusLargeMeanSquare_twoThirds_source_error_le rho hD) hb

/-- The retained source limit holds on the dyadic cubic windows used by the enlarged divisor schedule. -/
theorem pairedEtaCompletedMoebiusLargeMeanSquare_twoThirds_dyadic_tendsto_source
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    Tendsto (fun k ↦ pairedEtaCompletedMoebiusLargeMeanSquare rho
      (pairedEtaMoebiusHyperbolaCutoff k ^ 3) (pairedEtaMoebiusHyperbolaCutoff k ^ 3)
      (pairedEtaMoebiusHyperbolaCutoff k ^ 2)) atTop (𝓝 (‖pairedEtaCompletedMoebiusSource rho‖ ^ 2)) :=
  (pairedEtaCompletedMoebiusLargeMeanSquare_twoThirds_tendsto_source rho hrho).comp
    pairedEtaMoebiusHyperbolaCutoff_tendsto_atTop

end

end RiemannGaussian
