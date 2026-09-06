import RiemannGaussian.EtaMomentDivisorEndpoints

/-!
# Exact Möbius cancellation at every centered eta moment order

The full growing divisor sum of actual completed moment prefixes reduces
to two explicit endpoint polynomials. Each divisor translates the center
by its own logarithm; every odd last endpoint and complex Mellin phase is
retained. The resulting bound is uniform in the arithmetic cutoff for a
fixed center. A moving physical center remains an explicit parameter.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The exact centered moment convolution is supported at the two eta
source endpoints. Translation is performed before divisor cancellation. -/
theorem sum_moebius_mul_pairedEtaUnpairedCenteredMomentPrefix
    (k : ℕ) (s : ℂ) (a : ℝ) {M : ℕ} (hM : 2 ≤ M) :
    (∑ d ∈ Finset.Icc 1 M, (μ d : ℂ) * (d : ℂ) ^ (-s) *
      pairedEtaUnpairedCenteredMomentPrefix k s (a - Real.log d) (M / d)) =
        pairedEtaCenteredMomentEndpointPolynomial k s a 0 -
          2 * (2 : ℂ) ^ (-s) * pairedEtaCenteredMomentEndpointPolynomial k s a (Real.log 2) := by
  simp only [pairedEtaUnpairedCenteredMomentPrefix, Finset.mul_sum]
  rw [← sum_Icc_divisorsAntidiagonal_eq_sum_divided_prefix]
  calc
    _ = ∑ n ∈ Finset.Icc 1 M, pairedEtaDyadicDirichletSource n * (n : ℂ) ^ (-s) *
        pairedEtaCenteredMomentEndpointPolynomial k s a (Real.log n) := by
      apply Finset.sum_congr rfl
      intro n hn
      calc
        _ = (∑ p ∈ n.divisorsAntidiagonal, (μ p.1 : ℂ) * (p.1 : ℂ) ^ (-s) *
            ((pairedEtaDirichletSign p.2 : ℂ) * (p.2 : ℂ) ^ (-s))) *
              pairedEtaCenteredMomentEndpointPolynomial k s a (Real.log n) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro p hp
          obtain ⟨hd, he⟩ := Nat.ne_zero_of_mem_divisorsAntidiagonal hp
          rw [pairedEtaCenteredMomentEndpointPolynomial_log_mul k s a
            (Nat.pos_of_ne_zero hd) (Nat.pos_of_ne_zero he),
            (Nat.mem_divisorsAntidiagonal.mp hp).1]
          ring
        _ = _ := by rw [sum_moebius_mul_pairedEtaDirichletTerm s n (Finset.mem_Icc.mp hn).1]
    _ = _ := by
      simp only [pairedEtaDyadicDirichletSource, sub_mul, Finset.sum_sub_distrib,
        ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
      simp [Finset.sum_ite_eq', Finset.mem_Icc, hM, show 1 ≤ M by omega]

/-- One complete moment divisor term, with the literal translated
center, divided cutoff, and both original completion factors. -/
def pairedEtaCompletedMomentMoebiusTerm
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) (M d : ℕ) : ℂ :=
  (μ d : ℂ) * (d : ℂ) ^ (-rho.1) *
    ((pairedEtaXiCompletionFactor rho.1 * rho.1) *
      pairedEtaUnpairedCenteredMomentPrefix k rho.1 (a - Real.log d) (M / d))

/-- Every divisor term is the actual finite centered eta moment plus
its necessary odd last endpoint, at that divisor's translated center. -/
theorem pairedEtaCompletedMomentMoebiusTerm_eq_actual_prefix
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) (M d : ℕ) :
    pairedEtaCompletedMomentMoebiusTerm rho k a M d =
      (μ d : ℂ) * (d : ℂ) ^ (-rho.1) * ((pairedEtaXiCompletionFactor rho.1 * rho.1) *
        (pairedEtaLogLaplaceMomentCenteredPartialSum k rho.1 (a - Real.log d) ((M / d) / 2) +
          if Odd (M / d) then ((M / d : ℕ) : ℂ) ^ (-rho.1) *
            pairedEtaCenteredMomentEndpointPolynomial k rho.1 (a - Real.log d)
              (Real.log (M / d : ℕ)) else 0)) := by
  rw [pairedEtaCompletedMomentMoebiusTerm,
    pairedEtaUnpairedCenteredMomentPrefix_eq_paired_add_endpoint k (NontrivialZetaZero.coe_ne_zero rho)]

/-- The new all-order divisor feature agrees exactly with the existing
completed Möbius term at order zero, independently of the center. -/
theorem pairedEtaCompletedMomentMoebiusTerm_zero
    (rho : NontrivialZetaZero) (a : ℝ) (M d : ℕ) :
    pairedEtaCompletedMomentMoebiusTerm rho 0 a M d = pairedEtaCompletedMoebiusTerm rho M d := by
  rw [pairedEtaCompletedMomentMoebiusTerm, pairedEtaUnpairedCenteredMomentPrefix_zero,
    pairedEtaCompletedMoebiusTerm_eq_completed_prefix]
  field_simp [NontrivialZetaZero.coe_ne_zero rho]

/-- The entire growing divisor family at one moment order and center. -/
def pairedEtaCompletedMomentMoebiusAggregate
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) (M : ℕ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 M, pairedEtaCompletedMomentMoebiusTerm rho k a M d

/-- The two exact completed endpoint terms surviving moment inversion. -/
def pairedEtaCompletedMomentMoebiusSource (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) : ℂ :=
  (pairedEtaXiCompletionFactor rho.1 * rho.1) *
    (pairedEtaCenteredMomentEndpointPolynomial k rho.1 a 0 -
      2 * (2 : ℂ) ^ (-rho.1) *
        pairedEtaCenteredMomentEndpointPolynomial k rho.1 a (Real.log 2))

/-- Every complete moment divisor aggregate equals its evaluated source
once both physical source endpoints are included. -/
theorem pairedEtaCompletedMomentMoebiusAggregate_eq_source
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) {M : ℕ} (hM : 2 ≤ M) :
    pairedEtaCompletedMomentMoebiusAggregate rho k a M =
      pairedEtaCompletedMomentMoebiusSource rho k a := by
  unfold pairedEtaCompletedMomentMoebiusAggregate pairedEtaCompletedMomentMoebiusTerm
    pairedEtaCompletedMomentMoebiusSource
  calc
    _ = (pairedEtaXiCompletionFactor rho.1 * rho.1) *
        ∑ d ∈ Finset.Icc 1 M, (μ d : ℂ) * (d : ℂ) ^ (-rho.1) *
          pairedEtaUnpairedCenteredMomentPrefix k rho.1 (a - Real.log d) (M / d) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = _ := by rw [sum_moebius_mul_pairedEtaUnpairedCenteredMomentPrefix k rho.1 a hM]

/-- There are no moment divisor terms at cutoff zero. -/
theorem pairedEtaCompletedMomentMoebiusAggregate_zero
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) :
    pairedEtaCompletedMomentMoebiusAggregate rho k a 0 = 0 := by
  simp [pairedEtaCompletedMomentMoebiusAggregate]

/-- The first cutoff retains exactly its completed first endpoint. -/
theorem pairedEtaCompletedMomentMoebiusAggregate_one
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) :
    pairedEtaCompletedMomentMoebiusAggregate rho k a 1 =
      (pairedEtaXiCompletionFactor rho.1 * rho.1) *
        pairedEtaCenteredMomentEndpointPolynomial k rho.1 a 0 := by
  norm_num [pairedEtaCompletedMomentMoebiusAggregate, pairedEtaCompletedMomentMoebiusTerm,
    pairedEtaUnpairedCenteredMomentPrefix, pairedEtaDirichletSign]

/-- The all-cutoff bound depends explicitly on the moment order,
completion, and center; a moving center has not been replaced by a constant. -/
def pairedEtaCompletedMomentMoebiusConstant (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) : ℝ :=
  ‖pairedEtaXiCompletionFactor rho.1 * rho.1‖ * (1 + 2 * ‖(2 : ℂ) ^ (-rho.1)‖) *
    pairedEtaMomentEndpointBound rho.1 k (|a| + Real.log 2)

/-- The moment aggregate constant is nonnegative. -/
theorem pairedEtaCompletedMomentMoebiusConstant_nonneg
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) :
    0 ≤ pairedEtaCompletedMomentMoebiusConstant rho k a := by
  have hB := pairedEtaMomentEndpointBound_nonneg rho.1 k
    (add_nonneg (abs_nonneg a) (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)))
  unfold pairedEtaCompletedMomentMoebiusConstant
  positivity

/-- The full growing family of completed centered moments has a
discharged uniform cutoff bound at every order and every fixed center. -/
theorem norm_pairedEtaCompletedMomentMoebiusAggregate_le
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) (M : ℕ) :
    ‖pairedEtaCompletedMomentMoebiusAggregate rho k a M‖ ≤
      pairedEtaCompletedMomentMoebiusConstant rho k a := by
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hQ0 := norm_pairedEtaCenteredMomentEndpointPolynomial_le rho.1 k
    (a := a) (t := 0) (R := |a| + Real.log 2)
    (by simpa only [zero_sub, abs_neg] using le_add_of_nonneg_right hl)
  have hQ2 := norm_pairedEtaCenteredMomentEndpointPolynomial_le rho.1 k
    (a := a) (t := Real.log 2) (R := |a| + Real.log 2)
    ((abs_sub _ _).trans_eq (by rw [abs_of_nonneg hl]; ring))
  have hB := pairedEtaMomentEndpointBound_nonneg rho.1 k (add_nonneg (abs_nonneg a) hl)
  by_cases hM : 2 ≤ M
  · rw [pairedEtaCompletedMomentMoebiusAggregate_eq_source rho k a hM,
      pairedEtaCompletedMomentMoebiusSource, norm_mul]
    calc
      _ ≤ ‖pairedEtaXiCompletionFactor rho.1 * rho.1‖ *
          (‖pairedEtaCenteredMomentEndpointPolynomial k rho.1 a 0‖ +
            ‖2 * (2 : ℂ) ^ (-rho.1) *
              pairedEtaCenteredMomentEndpointPolynomial k rho.1 a (Real.log 2)‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
      _ ≤ ‖pairedEtaXiCompletionFactor rho.1 * rho.1‖ *
          (pairedEtaMomentEndpointBound rho.1 k (|a| + Real.log 2) +
            2 * ‖(2 : ℂ) ^ (-rho.1)‖ * pairedEtaMomentEndpointBound rho.1 k (|a| + Real.log 2)) := by
        simp only [norm_mul, Complex.norm_ofNat]
        exact mul_le_mul_of_nonneg_left
          (add_le_add hQ0 (mul_le_mul_of_nonneg_left hQ2 (by positivity))) (by positivity)
      _ = _ := by unfold pairedEtaCompletedMomentMoebiusConstant; ring
  · interval_cases M
    · simpa only [pairedEtaCompletedMomentMoebiusAggregate_zero, norm_zero] using
        pairedEtaCompletedMomentMoebiusConstant_nonneg rho k a
    · rw [pairedEtaCompletedMomentMoebiusAggregate_one, norm_mul]
      calc
        _ ≤ ‖pairedEtaXiCompletionFactor rho.1 * rho.1‖ *
            pairedEtaMomentEndpointBound rho.1 k (|a| + Real.log 2) :=
          mul_le_mul_of_nonneg_left hQ0 (norm_nonneg _)
        _ ≤ _ := by
          unfold pairedEtaCompletedMomentMoebiusConstant
          apply mul_le_mul_of_nonneg_right _ hB
          exact le_mul_of_one_le_right (norm_nonneg _)
            (le_add_of_nonneg_right (by positivity))

end

end RiemannGaussian
