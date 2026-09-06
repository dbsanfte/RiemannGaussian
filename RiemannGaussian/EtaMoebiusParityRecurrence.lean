import RiemannGaussian.EtaMoebiusDyadicCorrelation

/-!
# Exact global parity recurrences for the actual completed Möbius tails

Every divisor up to the current cutoff is retained. The even contribution
is the odd contribution at half the cutoff multiplied by the exact complex
factor `-2^(-rho)`. Finite Möbius inversion therefore gives a contractive
recurrence for the complete odd aggregate, before any norm estimate.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- Doubling an odd Möbius index reverses its coefficient; doubling an
even index introduces the square factor four and gives zero. -/
theorem moebius_two_mul_eq_odd (d : ℕ) :
    μ (2 * d) = if Odd d then -μ d else 0 := by
  by_cases hd : Odd d
  · rw [if_pos hd, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (Nat.coprime_two_left.mpr hd), ArithmeticFunction.moebius_apply_prime Nat.prime_two]
    ring
  · rw [if_neg hd]
    apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
    intro hsq
    apply (Nat.squarefree_iff_prime_squarefree.mp hsq) 2 Nat.prime_two
    obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.mp hd
    exact ⟨k, by omega⟩

/-- The complete odd-divisor contribution to the original tail aggregate. -/
def pairedEtaCompletedMoebiusOddAggregate (rho : NontrivialZetaZero) (M : ℕ) : ℂ :=
  ∑ d ∈ (Finset.Icc 1 M).filter Odd, pairedEtaCompletedMoebiusTerm rho M d

/-- The complete even-divisor contribution, retaining every actual endpoint. -/
def pairedEtaCompletedMoebiusEvenAggregate (rho : NontrivialZetaZero) (M : ℕ) : ℂ :=
  ∑ d ∈ (Finset.Icc 1 M).filter Even, pairedEtaCompletedMoebiusTerm rho M d

/-- Both full parity contributions sum to the original signed aggregate. -/
theorem pairedEtaCompletedMoebiusOdd_add_even (rho : NontrivialZetaZero) (M : ℕ) :
    pairedEtaCompletedMoebiusOddAggregate rho M + pairedEtaCompletedMoebiusEvenAggregate rho M =
      pairedEtaCompletedMoebiusTailAggregate rho M := by
  simpa only [pairedEtaCompletedMoebiusOddAggregate, pairedEtaCompletedMoebiusEvenAggregate,
    Nat.not_odd_iff_even, sum_pairedEtaCompletedMoebiusTerm] using
      Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 M) Odd (pairedEtaCompletedMoebiusTerm rho M)

/-- The literal even divisor term has the exact halved-cutoff phase
relation, including the Möbius square-factor zero and all unpaired endpoints. -/
theorem pairedEtaCompletedMoebiusTerm_two_mul (rho : NontrivialZetaZero) (M d : ℕ) :
    pairedEtaCompletedMoebiusTerm rho M (2 * d) =
      -(2 : ℂ) ^ (-rho.1) * (if Odd d then pairedEtaCompletedMoebiusTerm rho (M / 2) d else 0) := by
  simp only [pairedEtaCompletedMoebiusTerm_eq_completed_prefix, moebius_two_mul_eq_odd,
    Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ← Nat.div_div_eq_div_mul]
  split_ifs <;> push_cast <;> ring

/-- Reindexing all even divisors by their halves is a finite bijection
with the exact divided upper cutoff. -/
theorem sum_even_Icc_eq_sum_half (M : ℕ) (f : ℕ → ℂ) :
    (∑ d ∈ (Finset.Icc 1 M).filter Even, f d) = ∑ d ∈ Finset.Icc 1 (M / 2), f (2 * d) := by
  apply Finset.sum_bij (fun d _ ↦ d / 2)
  · intro d hd
    obtain ⟨hdM, hde⟩ := Finset.mem_filter.mp hd
    obtain ⟨hdp, hdM⟩ := Finset.mem_Icc.mp hdM
    have he := Nat.even_iff.mp hde
    exact Finset.mem_Icc.mpr ⟨by omega, Nat.div_le_div_right hdM⟩
  · intro a ha b hb hab
    have hea := Nat.even_iff.mp (Finset.mem_filter.mp ha).2
    have heb := Nat.even_iff.mp (Finset.mem_filter.mp hb).2
    omega
  · intro d hd
    obtain ⟨hdp, hdM⟩ := Finset.mem_Icc.mp hd
    refine ⟨2 * d, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, ?_⟩, even_two_mul d⟩, by omega⟩
    have h := (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).1 hdM
    omega
  · intro d hd
    have he := Nat.even_iff.mp (Finset.mem_filter.mp hd).2
    congr 1
    omega

/-- The complete even aggregate equals a single exact complex multiple
of the complete odd aggregate at half the cutoff. -/
theorem pairedEtaCompletedMoebiusEvenAggregate_eq_half_odd (rho : NontrivialZetaZero) (M : ℕ) :
    pairedEtaCompletedMoebiusEvenAggregate rho M =
      -(2 : ℂ) ^ (-rho.1) * pairedEtaCompletedMoebiusOddAggregate rho (M / 2) := by
  rw [pairedEtaCompletedMoebiusEvenAggregate, sum_even_Icc_eq_sum_half]
  simp only [pairedEtaCompletedMoebiusTerm_two_mul, ← Finset.mul_sum, ← Finset.sum_filter,
    pairedEtaCompletedMoebiusOddAggregate]

/-- Finite Möbius inversion gives a recurrence for the complete growing
odd-divisor family with its exact complex dyadic multiplier. -/
theorem pairedEtaCompletedMoebiusOddAggregate_recurrence
    (rho : NontrivialZetaZero) {M : ℕ} (hM : 2 ≤ M) :
    pairedEtaCompletedMoebiusOddAggregate rho M = pairedEtaCompletedMoebiusSource rho +
      (2 : ℂ) ^ (-rho.1) * pairedEtaCompletedMoebiusOddAggregate rho (M / 2) := by
  have h := pairedEtaCompletedMoebiusOdd_add_even rho M
  rw [pairedEtaCompletedMoebiusTailAggregate_eq_source rho hM,
    pairedEtaCompletedMoebiusEvenAggregate_eq_half_odd] at h
  linear_combination h

/-- There are no odd divisor terms at cutoff zero. -/
theorem pairedEtaCompletedMoebiusOddAggregate_zero (rho : NontrivialZetaZero) :
    pairedEtaCompletedMoebiusOddAggregate rho 0 = 0 := by
  simp [pairedEtaCompletedMoebiusOddAggregate]

/-- The cutoff-one initial value is the original completion factor. -/
theorem pairedEtaCompletedMoebiusOddAggregate_one (rho : NontrivialZetaZero) :
    pairedEtaCompletedMoebiusOddAggregate rho 1 = pairedEtaXiCompletionFactor rho.1 := by
  have hfilter : (Finset.Icc 1 1).filter Odd = ({1} : Finset ℕ) := by decide
  rw [pairedEtaCompletedMoebiusOddAggregate, hfilter, Finset.sum_singleton,
    pairedEtaCompletedMoebiusTerm_eq_completed_prefix]
  norm_num [pairedEtaUnpairedDirichletPrefix, pairedEtaDirichletSign]

end

end RiemannGaussian
