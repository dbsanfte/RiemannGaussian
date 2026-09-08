import RiemannGaussian.EtaMoebiusPrimeExclusion

/-!
# Simultaneous odd-prime exclusion in the original product prefix

Coprimality with an odd modulus removes all its prime factors at once.
Finite Möbius inversion retains every intersection in that exclusion.
The exact surviving product prefix is the original nonzero source minus
a finite sum of selected original divisor families at divided physical
cutoffs. The modulus is allowed to vary; all analytic costs of doing so
must still be paid in the subsequent mean-square estimate.
-/

open Complex
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- Finite Möbius inversion of a common-divisor selection is the exact coprimality indicator. -/
theorem sum_divisors_moebius_dvd_eq_coprime {P : ℕ} (hP : 0 < P) (n : ℕ) :
    (∑ e ∈ P.divisors.filter (fun e ↦ e ∣ n), (μ e : ℂ)) =
      if n.Coprime P then 1 else 0 := by
  have he : P.divisors.filter (fun e ↦ e ∣ n) = (Nat.gcd n P).divisors := by
    ext e
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    have hp0 : P ≠ 0 := hP.ne'
    have hg0 : Nat.gcd n P ≠ 0 := (Nat.gcd_pos_of_pos_right n hP).ne'
    tauto
  rw [he]
  simpa only [ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.one_apply, Nat.Coprime] using
      congrArg (fun f : ArithmeticFunction ℂ ↦ f (Nat.gcd n P))
        (ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℂ))

private theorem odd_divisor {P e : ℕ} (hP : Odd P) (he : e ∣ P) : Odd e := by
  obtain ⟨k, rfl⟩ := he
  exact (Nat.odd_mul.mp hP).1

/-- Sieving the actual alternating eta prefix keeps the full finite inclusion-exclusion sum and its complex factors. -/
theorem pairedEtaUnpairedDirichletPrefix_coprime_eq_sieve
    (s : ℂ) {P : ℕ} (hP : 0 < P) (hodd : Odd P) (M : ℕ) :
    (∑ q ∈ (Finset.Icc 1 M).filter (fun q ↦ q.Coprime P),
      (pairedEtaDirichletSign q : ℂ) * (q : ℂ) ^ (-s)) =
      ∑ e ∈ P.divisors, (μ e : ℂ) * (e : ℂ) ^ (-s) *
        pairedEtaUnpairedDirichletPrefix (M / e) s := by
  calc
    _ = ∑ q ∈ Finset.Icc 1 M,
        (∑ e ∈ P.divisors.filter (fun e ↦ e ∣ q), (μ e : ℂ)) *
          ((pairedEtaDirichletSign q : ℂ) * (q : ℂ) ^ (-s)) := by
      simp_rw [sum_divisors_moebius_dvd_eq_coprime hP, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro q _
      split_ifs <;> simp
    _ = ∑ e ∈ P.divisors, (μ e : ℂ) *
        ∑ q ∈ (Finset.Icc 1 M).filter (fun q ↦ e ∣ q),
          (pairedEtaDirichletSign q : ℂ) * (q : ℂ) ^ (-s) := by
      simp only [Finset.sum_filter, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro q _
      split_ifs <;> ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e he
      rw [sum_Icc_dvd_eq_divided (Nat.pos_of_mem_divisors he) M]
      simp only [pairedEtaDirichletSign_odd_mul (odd_divisor hodd (Nat.dvd_of_mem_divisors he)),
        Nat.cast_mul, Complex.natCast_mul_natCast_cpow, pairedEtaUnpairedDirichletPrefix,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring

/-- The original low divisor selection surviving simultaneous exclusion of all primes dividing the modulus. -/
def pairedEtaMoebiusCoprimeDivisors (P D : ℕ) : Finset ℕ :=
  (Finset.Icc 1 D).filter (fun d ↦ d.Coprime P)

/-- Every selected coprime divisor retains the original positive divisor cutoff. -/
theorem pairedEtaMoebiusCoprimeDivisors_subset (P D : ℕ) :
    pairedEtaMoebiusCoprimeDivisors P D ⊆ Finset.Icc 1 D :=
  Finset.filter_subset _ _

/-- The low divisor family with coprimality imposed on both original factors. -/
def pairedEtaCompletedMoebiusCoprimeLowAggregate
    (rho : NontrivialZetaZero) (P D M : ℕ) : ℂ :=
  pairedEtaXiCompletionFactor rho.1 *
    ∑ d ∈ pairedEtaMoebiusCoprimeDivisors P D, (μ d : ℂ) * (d : ℂ) ^ (-rho.1) *
      ∑ q ∈ (Finset.Icc 1 (M / d)).filter (fun q ↦ q.Coprime P),
        (pairedEtaDirichletSign q : ℂ) * (q : ℂ) ^ (-rho.1)

/-- Every prime intersection is retained as an exact selected-family term at its own divided cutoff. -/
theorem pairedEtaCompletedMoebiusCoprimeLowAggregate_eq_sieve
    (rho : NontrivialZetaZero) {P : ℕ} (hP : 0 < P) (hodd : Odd P) (D M : ℕ) :
    pairedEtaCompletedMoebiusCoprimeLowAggregate rho P D M =
      ∑ e ∈ P.divisors, (μ e : ℂ) * (e : ℂ) ^ (-rho.1) *
        pairedEtaCompletedMoebiusSelectedAggregate rho (pairedEtaMoebiusCoprimeDivisors P D) (M / e) := by
  simp only [pairedEtaCompletedMoebiusCoprimeLowAggregate,
    pairedEtaUnpairedDirichletPrefix_coprime_eq_sieve rho.1 hP hodd,
    Finset.mul_sum, pairedEtaCompletedMoebiusSelectedAggregate,
    pairedEtaCompletedMoebiusTerm_eq_completed_prefix]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro d _
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm d e]
  ring

/-- The literal completed high product prefix after all prime factors of the modulus are excluded simultaneously. -/
def pairedEtaCompletedMoebiusCoprimeAggregate
    (rho : NontrivialZetaZero) (P D M : ℕ) : ℂ :=
  pairedEtaXiCompletionFactor rho.1 *
    ∑ n ∈ (Finset.Icc 1 M).filter (fun n ↦ n.Coprime P),
      (pairedEtaMoebiusHighProductCoefficient D n : ℂ) * (n : ℂ) ^ (-rho.1)

private theorem sum_coprime_product_prefix (P M : ℕ) (f : ℕ → ℕ → ℂ) :
    (∑ n ∈ (Finset.Icc 1 M).filter (fun n ↦ n.Coprime P),
      ∑ a ∈ n.divisorsAntidiagonal, f a.1 a.2) =
      ∑ d ∈ (Finset.Icc 1 M).filter (fun d ↦ d.Coprime P),
        ∑ q ∈ (Finset.Icc 1 (M / d)).filter (fun q ↦ q.Coprime P), f q d := by
  calc
    _ = ∑ n ∈ Finset.Icc 1 M, ∑ a ∈ n.divisorsAntidiagonal,
        if a.1.Coprime P ∧ a.2.Coprime P then f a.1 a.2 else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _
      have he (a : ℕ × ℕ) (ha : a ∈ n.divisorsAntidiagonal) :
          (a.1.Coprime P ∧ a.2.Coprime P) ↔ n.Coprime P := by
        rw [← (Nat.mem_divisorsAntidiagonal.mp ha).1, Nat.coprime_mul_iff_left]
      by_cases hn : n.Coprime P
      · rw [if_pos hn]
        apply Finset.sum_congr rfl
        intro a ha
        rw [if_pos ((he a ha).mpr hn)]
      · rw [if_neg hn]
        symm
        apply Finset.sum_eq_zero
        intro a ha
        exact if_neg (fun h ↦ hn ((he a ha).mp h))
    _ = ∑ n ∈ Finset.Icc 1 M, ∑ a ∈ n.divisorsAntidiagonal,
        if a.2.Coprime P ∧ a.1.Coprime P then f a.2 a.1 else 0 := by
      apply Finset.sum_congr rfl
      intro n _
      conv_lhs => rw [← Nat.map_swap_divisorsAntidiagonal, Finset.sum_map]
      rfl
    _ = ∑ d ∈ Finset.Icc 1 M, ∑ q ∈ Finset.Icc 1 (M / d),
        if q.Coprime P ∧ d.Coprime P then f q d else 0 :=
      sum_Icc_divisorsAntidiagonal_eq_sum_divided_prefix M
        (fun d q ↦ if q.Coprime P ∧ d.Coprime P then f q d else 0)
    _ = _ := by
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : d.Coprime P
      · rw [if_pos hd]
        apply Finset.sum_congr rfl
        intro q _
        by_cases hq : q.Coprime P
        · exact (if_pos ⟨hq, hd⟩).trans (if_pos hq).symm
        · exact (if_neg (fun h ↦ hq h.1)).trans (if_neg hq).symm
      · simp only [hd, and_false, if_false, Finset.sum_const_zero]

private theorem coprime_low_eq_product_prefix
    (rho : NontrivialZetaZero) (P : ℕ) {D M : ℕ} (hDM : D ≤ M) :
    pairedEtaCompletedMoebiusCoprimeLowAggregate rho P D M =
      pairedEtaXiCompletionFactor rho.1 *
        ∑ n ∈ (Finset.Icc 1 M).filter (fun n ↦ n.Coprime P),
          ∑ a ∈ n.divisorsAntidiagonal,
            if a.2 ≤ D then (pairedEtaDirichletSign a.1 : ℂ) * (μ a.2 : ℂ) *
              ((a.1 * a.2 : ℕ) : ℂ) ^ (-rho.1) else 0 := by
  rw [sum_coprime_product_prefix P M
    (fun q d ↦ if d ≤ D then (pairedEtaDirichletSign q : ℂ) * (μ d : ℂ) *
      ((q * d : ℕ) : ℂ) ^ (-rho.1) else 0)]
  have hsel : ((Finset.Icc 1 M).filter (fun d ↦ d.Coprime P)).filter (fun d ↦ d ≤ D) =
      pairedEtaMoebiusCoprimeDivisors P D := by
    ext d
    simp only [pairedEtaMoebiusCoprimeDivisors, Finset.mem_filter, Finset.mem_Icc]
    omega
  symm
  calc
    _ = pairedEtaXiCompletionFactor rho.1 *
        ∑ d ∈ (Finset.Icc 1 M).filter (fun d ↦ d.Coprime P),
          if d ≤ D then (μ d : ℂ) * (d : ℂ) ^ (-rho.1) *
            ∑ q ∈ (Finset.Icc 1 (M / d)).filter (fun q ↦ q.Coprime P),
              (pairedEtaDirichletSign q : ℂ) * (q : ℂ) ^ (-rho.1) else 0 := by
      congr 1
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : d ≤ D
      · simp only [if_pos hd, Finset.mul_sum, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
        apply Finset.sum_congr rfl
        intro q _
        ring
      · simp [hd]
    _ = _ := by rw [← Finset.sum_filter, hsel]; rfl

/-- Simultaneous odd-prime exclusion preserves the original dyadic source exactly, with the whole surviving low family retained. -/
theorem pairedEtaCompletedMoebiusCoprimeLow_add_coprime_eq_source
    (rho : NontrivialZetaZero) {P : ℕ} (hodd : Odd P)
    {D M : ℕ} (hM : 2 ≤ M) (hDM : D ≤ M) :
    pairedEtaCompletedMoebiusCoprimeLowAggregate rho P D M +
      pairedEtaCompletedMoebiusCoprimeAggregate rho P D M =
        pairedEtaCompletedMoebiusSource rho := by
  rw [coprime_low_eq_product_prefix rho P hDM,
    pairedEtaCompletedMoebiusCoprimeAggregate, ← mul_add, ← Finset.sum_add_distrib]
  have hterm (n : ℕ) (hn : 1 ≤ n) :
      (∑ a ∈ n.divisorsAntidiagonal,
        if a.2 ≤ D then (pairedEtaDirichletSign a.1 : ℂ) * (μ a.2 : ℂ) *
          ((a.1 * a.2 : ℕ) : ℂ) ^ (-rho.1) else 0) +
        (pairedEtaMoebiusHighProductCoefficient D n : ℂ) * (n : ℂ) ^ (-rho.1) =
          pairedEtaDyadicDirichletSource n * (n : ℂ) ^ (-rho.1) := by
    calc
      _ = ∑ a ∈ n.divisorsAntidiagonal,
          (pairedEtaDirichletSign a.1 : ℂ) * (μ a.2 : ℂ) * (n : ℂ) ^ (-rho.1) := by
        simp only [pairedEtaMoebiusHighProductCoefficient, Int.cast_sum, Finset.sum_mul,
          Finset.sum_filter, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a ha
        rw [(Nat.mem_divisorsAntidiagonal.mp ha).1]
        by_cases hd : a.2 ≤ D <;> simp [hd, Nat.not_lt.mpr, Int.cast_mul]
      _ = _ := by
        rw [← Finset.sum_mul]
        congr 1
        conv_lhs => rw [← Nat.map_swap_divisorsAntidiagonal, Finset.sum_map]
        change (∑ a ∈ n.divisorsAntidiagonal,
          (pairedEtaDirichletSign a.2 : ℂ) * (μ a.1 : ℂ)) = _
        simpa only [mul_comm] using sum_moebius_mul_pairedEtaDirichletSign n hn
  have hsum : (∑ n ∈ (Finset.Icc 1 M).filter (fun n ↦ n.Coprime P),
      ((∑ a ∈ n.divisorsAntidiagonal,
        if a.2 ≤ D then (pairedEtaDirichletSign a.1 : ℂ) * (μ a.2 : ℂ) *
          ((a.1 * a.2 : ℕ) : ℂ) ^ (-rho.1) else 0) +
        (pairedEtaMoebiusHighProductCoefficient D n : ℂ) * (n : ℂ) ^ (-rho.1))) =
      1 - 2 * (2 : ℂ) ^ (-rho.1) := by
    calc
      _ = ∑ n ∈ (Finset.Icc 1 M).filter (fun n ↦ n.Coprime P),
          pairedEtaDyadicDirichletSource n * (n : ℂ) ^ (-rho.1) :=
        Finset.sum_congr rfl (fun n hn ↦ hterm n (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1)
      _ = _ := by
        simp only [pairedEtaDyadicDirichletSource, sub_mul, Finset.sum_sub_distrib,
          ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
        simp [Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_Icc, hM,
          show 1 ≤ M by omega, hodd]
  rw [hsum, pairedEtaCompletedMoebiusSource]

end

end RiemannGaussian
