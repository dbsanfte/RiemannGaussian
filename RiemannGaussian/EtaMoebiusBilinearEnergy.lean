import RiemannGaussian.EtaAlternatingHyperbolicCoefficients

/-!
# The full physical energy with fixed alternating Möbius coefficients

For a fixed divisor cutoff, the high aggregate is a partial Dirichlet sum
of one fixed alternating coefficient sequence. The actual completed
quotient carrier differs only by the already vanishing single fibre.
Both the exact complex boundary and every product-to-product interaction
remain in the energy identities. Coefficient square bounds alone do not
bound this full quadratic form.
-/

open Complex
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The partial Dirichlet sum with one fixed alternating high-divisor coefficient sequence throughout the physical window. -/
def pairedEtaMoebiusHighProductPrefix (rho : NontrivialZetaZero) (D M : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 M, (pairedEtaMoebiusHighProductCoefficient D n : ℂ) * (n : ℂ) ^ (-rho.1)

private theorem highProductPrefix_eq_divided (rho : NontrivialZetaZero) (D M : ℕ) :
    pairedEtaMoebiusHighProductPrefix rho D M =
      ∑ d ∈ Finset.Ioc D M, (μ d : ℂ) * (d : ℂ) ^ (-rho.1) *
        pairedEtaUnpairedDirichletPrefix (M / d) rho.1 := by
  have he : (Finset.Icc 1 M).filter (fun d ↦ D < d) = Finset.Ioc D M := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  calc
    _ = ∑ n ∈ Finset.Icc 1 M, ∑ p ∈ n.divisorsAntidiagonal,
        if D < p.2 then (pairedEtaDirichletSign p.1 : ℂ) * (μ p.2 : ℂ) *
          ((p.1 * p.2 : ℕ) : ℂ) ^ (-rho.1) else 0 := by
      apply Finset.sum_congr rfl
      intro n _
      rw [pairedEtaMoebiusHighProductCoefficient, Int.cast_sum, Finset.sum_mul, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Nat.mem_divisorsAntidiagonal.mp hp).1]
      split_ifs <;> simp only [Int.cast_mul]
    _ = ∑ n ∈ Finset.Icc 1 M, ∑ p ∈ n.divisorsAntidiagonal,
        if D < p.1 then (μ p.1 : ℂ) * (p.1 : ℂ) ^ (-rho.1) *
          ((pairedEtaDirichletSign p.2 : ℂ) * (p.2 : ℂ) ^ (-rho.1)) else 0 := by
      apply Finset.sum_congr rfl
      intro n _
      conv_lhs => rw [← Nat.map_swap_divisorsAntidiagonal, Finset.sum_map]
      apply Finset.sum_congr rfl
      rintro ⟨q, d⟩ _
      change (if D < q then (pairedEtaDirichletSign d : ℂ) * (μ q : ℂ) *
        ((d * q : ℕ) : ℂ) ^ (-rho.1) else 0) = _
      rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
      split_ifs <;> ring
    _ = ∑ d ∈ Finset.Icc 1 M, ∑ q ∈ Finset.Icc 1 (M / d),
        if D < d then (μ d : ℂ) * (d : ℂ) ^ (-rho.1) *
          ((pairedEtaDirichletSign q : ℂ) * (q : ℂ) ^ (-rho.1)) else 0 :=
      sum_Icc_divisorsAntidiagonal_eq_sum_divided_prefix M
        (fun d q ↦ if D < d then (μ d : ℂ) * (d : ℂ) ^ (-rho.1) *
          ((pairedEtaDirichletSign q : ℂ) * (q : ℂ) ^ (-rho.1)) else 0)
    _ = ∑ d ∈ Finset.Icc 1 M, if D < d then (μ d : ℂ) * (d : ℂ) ^ (-rho.1) *
        pairedEtaUnpairedDirichletPrefix (M / d) rho.1 else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : D < d
      · simp only [if_pos hd, pairedEtaUnpairedDirichletPrefix, Finset.mul_sum]
      · simp only [if_neg hd, Finset.sum_const_zero]
    _ = _ := by rw [← Finset.sum_filter, he]

/-- The original high-divisor aggregate is exactly the completed partial Dirichlet sum of the fixed alternating product coefficients, at every physical cutoff. -/
theorem pairedEtaCompletedMoebiusLargeAggregate_eq_product_prefix
    (rho : NontrivialZetaZero) (M D : ℕ) :
    pairedEtaCompletedMoebiusLargeAggregate rho M D =
      pairedEtaXiCompletionFactor rho.1 * pairedEtaMoebiusHighProductPrefix rho D M := by
  rw [highProductPrefix_eq_divided, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [pairedEtaCompletedMoebiusTerm_eq_completed_prefix]
  ring

/-- The exact complex difference between the surviving complete shells and the fixed-coefficient bilinear prefix is the single original boundary fibre. -/
theorem pairedEtaCompletedMoebiusCompleteQuotientAggregate_sub_product_prefix
    (rho : NontrivialZetaZero) {M D : ℕ} (hDM : D ≤ M) :
    pairedEtaCompletedMoebiusCompleteQuotientAggregate rho M D -
      pairedEtaXiCompletionFactor rho.1 * pairedEtaMoebiusHighProductPrefix rho D M =
        pairedEtaCompletedMoebiusBoundaryFibre rho M D := by
  rw [pairedEtaCompletedMoebiusCompleteQuotientAggregate_eq_boundary_add_large rho hDM,
    pairedEtaCompletedMoebiusLargeAggregate_eq_product_prefix]
  ring

/-- Passing to a fixed coefficient sequence costs only the already controlled single-fibre allowance, uniformly over the entire original cubic window. -/
theorem norm_pairedEtaCompletedMoebiusCompleteQuotientAggregate_sub_product_prefix_twoThirds_le
    (rho : NontrivialZetaZero) {u M : ℕ} (hu : 1 ≤ u) (hM : u ^ 3 ≤ M) :
    ‖pairedEtaCompletedMoebiusCompleteQuotientAggregate rho M (u ^ 2) -
      pairedEtaXiCompletionFactor rho.1 * pairedEtaMoebiusHighProductPrefix rho (u ^ 2) M‖ ≤
        pairedEtaMoebiusBoundaryAllowance rho u := by
  have h23 : u ^ 2 ≤ u ^ 3 := by nlinarith [Nat.mul_le_mul_left (u ^ 2) hu]
  rw [pairedEtaCompletedMoebiusCompleteQuotientAggregate_sub_product_prefix rho (h23.trans hM)]
  exact norm_pairedEtaCompletedMoebiusBoundaryFibre_twoThirds_le rho hu hM

/-- The full product-prefix square retains every ordered product pair and both signed alternating coefficients before physical averaging. -/
theorem pairedEtaMoebiusHighProductPrefix_norm_sq_eq_pairs
    (rho : NontrivialZetaZero) (D M : ℕ) :
    (‖pairedEtaMoebiusHighProductPrefix rho D M‖ : ℂ) ^ 2 =
      ∑ n ∈ Finset.Icc 1 M, ∑ m ∈ Finset.Icc 1 M,
        (pairedEtaMoebiusHighProductCoefficient D n : ℂ) *
          (pairedEtaMoebiusHighProductCoefficient D m : ℂ) *
          (n : ℂ) ^ (-rho.1) * starRingEnd ℂ ((m : ℂ) ^ (-rho.1)) := by
  rw [← Complex.mul_conj']
  simp only [pairedEtaMoebiusHighProductPrefix, map_sum, map_mul, map_intCast,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- The original whole-window high energy is the full alternating bilinear quadratic form, with a fixed coefficient sequence and every product cross term retained. -/
theorem pairedEtaCompletedMoebiusLargeMeanSquare_eq_bilinear_pairs
    (rho : NontrivialZetaZero) (A L D : ℕ) :
    (pairedEtaCompletedMoebiusLargeMeanSquare rho A L D : ℂ) =
      (‖pairedEtaXiCompletionFactor rho.1‖ : ℂ) ^ 2 *
        ((∑ t ∈ Finset.range L, ∑ n ∈ Finset.Icc 1 (A + t), ∑ m ∈ Finset.Icc 1 (A + t),
          (pairedEtaMoebiusHighProductCoefficient D n : ℂ) *
            (pairedEtaMoebiusHighProductCoefficient D m : ℂ) *
            (n : ℂ) ^ (-rho.1) * starRingEnd ℂ ((m : ℂ) ^ (-rho.1))) / L) := by
  simp only [pairedEtaCompletedMoebiusLargeMeanSquare, Complex.ofReal_div, Complex.ofReal_sum,
    Complex.ofReal_natCast, Complex.ofReal_pow,
    pairedEtaCompletedMoebiusLargeAggregate_eq_product_prefix, norm_mul, Complex.ofReal_mul,
    mul_pow, pairedEtaMoebiusHighProductPrefix_norm_sq_eq_pairs, ← Finset.mul_sum, mul_div_assoc]

/-- The completed shell energy still includes the signed interference with its single boundary when passing to the fixed bilinear coefficients. -/
theorem pairedEtaCompletedMoebiusCompleteQuotientAggregate_norm_sq_eq_bilinear_boundary
    (rho : NontrivialZetaZero) {M D : ℕ} (hDM : D ≤ M) :
    ‖pairedEtaCompletedMoebiusCompleteQuotientAggregate rho M D‖ ^ 2 =
      ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 * ‖pairedEtaMoebiusHighProductPrefix rho D M‖ ^ 2 +
        ‖pairedEtaCompletedMoebiusBoundaryFibre rho M D‖ ^ 2 +
        2 * (pairedEtaXiCompletionFactor rho.1 * pairedEtaMoebiusHighProductPrefix rho D M *
          starRingEnd ℂ (pairedEtaCompletedMoebiusBoundaryFibre rho M D)).re := by
  rw [pairedEtaCompletedMoebiusCompleteQuotientAggregate_eq_boundary_add_large rho hDM,
    pairedEtaCompletedMoebiusLargeAggregate_eq_product_prefix, add_comm,
    Complex.sq_norm, Complex.normSq_add]
  simp only [← Complex.sq_norm, norm_mul, mul_pow]

end

end RiemannGaussian
