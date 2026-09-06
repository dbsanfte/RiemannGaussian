import RiemannGaussian.EtaMoebiusParityBlocks

/-!
# Recovering the original completed prefixes from the odd Möbius aggregates

Finite odd-divisor inversion gives the exact complex reconstruction at all
cutoffs. The inverse weights and their divided physical cutoffs remain in
the formula. This supplies an identity needed to assess a transfer from the
uniform aggregate bounds to the unchanged arithmetic current.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The odd-restricted Möbius convolution is supported exactly at one.
Both factor parities are retained until their product is identified. -/
theorem sum_odd_divisorsAntidiagonal_moebius (n : ℕ) :
    (∑ p ∈ n.divisorsAntidiagonal, if Odd p.1 ∧ Odd p.2 then (μ p.2 : ℂ) else 0) =
      if n = 1 then 1 else 0 := by
  by_cases hn : Odd n
  · calc
      _ = ∑ p ∈ n.divisorsAntidiagonal, (μ p.2 : ℂ) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
        exact if_pos (Nat.odd_mul.mp (hprod ▸ hn))
      _ = _ := by
        rw [Nat.sum_divisorsAntidiagonal' (fun _ k ↦ (μ k : ℂ))]
        simpa only [ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.intCoe_apply,
          ArithmeticFunction.one_apply] using
            congrArg (fun f : ArithmeticFunction ℂ ↦ f n)
              (ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℂ))
  · have hn1 : n ≠ 1 := by intro h; apply hn; simpa only [h] using (show Odd (1 : ℕ) by decide)
    rw [if_neg hn1]
    apply Finset.sum_eq_zero
    intro p hp
    apply if_neg
    intro hpodd
    apply hn
    rw [← (Nat.mem_divisorsAntidiagonal.mp hp).1]
    exact hpodd.1.mul hpodd.2

/-- The inverse and Möbius weights combine to their exact product phase
before applying the odd divisor convolution. -/
theorem odd_moebius_weights_mul (s : ℂ) (d e : ℕ) :
    (if Odd d then (d : ℂ) ^ (-s) else 0) *
      (if Odd e then (μ e : ℂ) * (e : ℂ) ^ (-s) else 0) =
        (if Odd d ∧ Odd e then (μ e : ℂ) else 0) * ((d * e : ℕ) : ℂ) ^ (-s) := by
  rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  split_ifs <;> simp_all
  ring

/-- Finite inversion of the complete odd-divisor transform recovers the
original sequence, with the literal divided cutoffs and complex weights. -/
theorem sum_odd_divided_moebius_inverse (s : ℂ) (f : ℕ → ℂ) (hf : f 0 = 0) (M : ℕ) :
    (∑ d ∈ (Finset.Icc 1 M).filter Odd, (d : ℂ) ^ (-s) *
      ∑ e ∈ (Finset.Icc 1 (M / d)).filter Odd,
        (μ e : ℂ) * (e : ℂ) ^ (-s) * f ((M / d) / e)) = f M := by
  have he : (∑ d ∈ (Finset.Icc 1 M).filter Odd, (d : ℂ) ^ (-s) *
      ∑ e ∈ (Finset.Icc 1 (M / d)).filter Odd,
        (μ e : ℂ) * (e : ℂ) ^ (-s) * f ((M / d) / e)) =
      ∑ d ∈ Finset.Icc 1 M, ∑ e ∈ Finset.Icc 1 (M / d),
        ((if Odd d then (d : ℂ) ^ (-s) else 0) *
          (if Odd e then (μ e : ℂ) * (e : ℂ) ^ (-s) else 0)) * f (M / (d * e)) := by
    simp_rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hdo : Odd d
    · rw [if_pos hdo, if_pos hdo, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      rw [Nat.div_div_eq_div_mul]
      split_ifs <;> ring
    · simp [hdo]
  rw [he, ← sum_Icc_divisorsAntidiagonal_eq_sum_divided_prefix]
  calc
    _ = ∑ n ∈ Finset.Icc 1 M, (if n = 1 then 1 else 0) *
        ((n : ℂ) ^ (-s) * f (M / n)) := by
      apply Finset.sum_congr rfl
      intro n hn
      calc
        _ = ∑ p ∈ n.divisorsAntidiagonal,
            (if Odd p.1 ∧ Odd p.2 then (μ p.2 : ℂ) else 0) *
              ((n : ℂ) ^ (-s) * f (M / n)) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [odd_moebius_weights_mul, (Nat.mem_divisorsAntidiagonal.mp hp).1]
          ring
        _ = _ := by rw [← Finset.sum_mul, sum_odd_divisorsAntidiagonal_moebius]
    _ = f M := by
      by_cases hM : M = 0
      · simp [hM, hf]
      · simp [ite_mul, Finset.sum_ite_eq', Finset.mem_Icc, Nat.one_le_iff_ne_zero.mpr hM]

/-- One inverse divisor feature of the original completed eta prefix.
Its complex arithmetic weight and its own physical cutoff are explicit. -/
def pairedEtaCompletedOddInverseTerm (rho : NontrivialZetaZero) (M d : ℕ) : ℂ :=
  (d : ℂ) ^ (-rho.1) * pairedEtaCompletedMoebiusOddAggregate rho (M / d)

/-- The completed unpaired eta prefix is exactly the inverse-weighted
sum of whole odd aggregates. No norm or endpoint correction is omitted. -/
theorem sum_pairedEtaCompletedOddInverseTerm (rho : NontrivialZetaZero) (M : ℕ) :
    (∑ d ∈ (Finset.Icc 1 M).filter Odd, pairedEtaCompletedOddInverseTerm rho M d) =
      pairedEtaXiCompletionFactor rho.1 * pairedEtaUnpairedDirichletPrefix M rho.1 := by
  simp only [pairedEtaCompletedOddInverseTerm, pairedEtaCompletedMoebiusOddAggregate,
    pairedEtaCompletedMoebiusTerm_eq_completed_prefix]
  exact sum_odd_divided_moebius_inverse rho.1
    (fun k ↦ pairedEtaXiCompletionFactor rho.1 * pairedEtaUnpairedDirichletPrefix k rho.1)
    (by simp [pairedEtaUnpairedDirichletPrefix]) M

/-- At an even physical endpoint the inverse sum reconstructs the
repository's original order-zero finite completed moment exactly. -/
theorem pairedEtaFiniteCompletedMoment_zero_eq_oddInverse (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaFiniteCompletedMoment rho N 0 =
      ∑ d ∈ (Finset.Icc 1 (2 * N)).filter Odd, pairedEtaCompletedOddInverseTerm rho (2 * N) d := by
  rw [sum_pairedEtaCompletedOddInverseTerm, pairedEtaUnpairedDirichletPrefix_even,
    pairedEtaFiniteCompletedMoment_zero_eq_completed_prefix]

end

end RiemannGaussian
