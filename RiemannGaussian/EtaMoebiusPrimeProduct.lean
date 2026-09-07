import RiemannGaussian.EtaMoebiusSelectedFamily

/-!
# Odd-prime product rows as a short Möbius divisor annulus

The terms whose products are divisible by an odd prime cancel exactly
between the two positions of that prime in the hyperbola. The surviving
divisors lie between `D / p` and `D` and are coprime to `p`. This is an
identity for the original coefficients, including square-factor zeros;
it does not assume cancellation of shifted Möbius sums.
-/

open Complex
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- Multiplication by a prime reverses a coprime Möbius coefficient and annihilates every coefficient already divisible by that prime. -/
theorem moebius_prime_mul_eq_not_dvd {p : ℕ} (hp : p.Prime) (d : ℕ) :
    μ (p * d) = if p ∣ d then 0 else -μ d := by
  by_cases hd : p ∣ d
  · rw [if_pos hd]
    apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
    intro hs
    apply (Nat.squarefree_iff_prime_squarefree.mp hs) p hp
    obtain ⟨k, rfl⟩ := hd
    exact ⟨k, by ring⟩
  · rw [if_neg hd, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (hp.coprime_iff_not_dvd.mpr hd), ArithmeticFunction.moebius_apply_prime hp]
    ring

private theorem etaSign_odd_mul {p : ℕ} (hp : Odd p) (q : ℕ) :
    pairedEtaDirichletSign (p * q) = pairedEtaDirichletSign q := by
  simp only [pairedEtaDirichletSign, Nat.even_mul, Nat.not_even_iff_odd.mpr hp, false_or]

private theorem sum_prime_antidiagonal_dvd {p : ℕ} (hp : 0 < p) (n : ℕ)
    (f : ℕ → ℕ → ℤ) :
    (∑ a ∈ (p * n).divisorsAntidiagonal.filter (fun a ↦ p ∣ a.2), f a.1 a.2) =
      ∑ a ∈ n.divisorsAntidiagonal, f a.1 (p * a.2) := by
  apply Finset.sum_bij (fun a _ ↦ (a.1, a.2 / p))
  · intro a ha
    obtain ⟨ha, hd⟩ := Finset.mem_filter.mp ha
    obtain ⟨he, hn⟩ := Nat.mem_divisorsAntidiagonal.mp ha
    apply Nat.mem_divisorsAntidiagonal.mpr
    refine ⟨?_, (mul_ne_zero_iff.mp hn).2⟩
    apply Nat.eq_of_mul_eq_mul_left hp
    calc
      p * (a.1 * (a.2 / p)) = a.1 * a.2 := by rw [mul_left_comm, Nat.mul_div_cancel' hd]
      _ = p * n := he
  · intro a ha b hb hab
    obtain ⟨ha, hda⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb, hdb⟩ := Finset.mem_filter.mp hb
    apply Prod.ext
    · have he := congrArg Prod.fst hab
      exact he
    have he := congrArg (fun x : ℕ × ℕ ↦ p * x.2) hab
    simpa only [Nat.mul_div_cancel' hda, Nat.mul_div_cancel' hdb] using he
  · intro a ha
    obtain ⟨he, hn⟩ := Nat.mem_divisorsAntidiagonal.mp ha
    refine ⟨(a.1, p * a.2), Finset.mem_filter.mpr ⟨?_, dvd_mul_right p a.2⟩, ?_⟩
    · exact Nat.mem_divisorsAntidiagonal.mpr ⟨by nlinarith [he], Nat.mul_ne_zero hp.ne' hn⟩
    · simp [Nat.mul_div_right _ hp]
  · intro a ha
    have hd := (Finset.mem_filter.mp ha).2
    simp only [Nat.mul_div_cancel' hd]

private theorem sum_prime_antidiagonal_not_dvd {p : ℕ} (hp : p.Prime) (n : ℕ)
    (f : ℕ → ℕ → ℤ) :
    (∑ a ∈ (p * n).divisorsAntidiagonal.filter (fun a ↦ ¬p ∣ a.2), f a.1 a.2) =
      ∑ a ∈ n.divisorsAntidiagonal.filter (fun a ↦ ¬p ∣ a.2), f (p * a.1) a.2 := by
  have hquot (a : ℕ × ℕ) (ha : a ∈ (p * n).divisorsAntidiagonal) (hd : ¬p ∣ a.2) :
      p ∣ a.1 := by
    have he := (Nat.mem_divisorsAntidiagonal.mp ha).1
    exact (hp.dvd_mul.mp (he ▸ dvd_mul_right p n)).resolve_right hd
  apply Finset.sum_bij (fun a _ ↦ (a.1 / p, a.2))
  · intro a ha
    obtain ⟨ha, hd⟩ := Finset.mem_filter.mp ha
    have hq := hquot a ha hd
    obtain ⟨he, hn⟩ := Nat.mem_divisorsAntidiagonal.mp ha
    refine Finset.mem_filter.mpr ⟨Nat.mem_divisorsAntidiagonal.mpr
      ⟨?_, (mul_ne_zero_iff.mp hn).2⟩, hd⟩
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    calc
      p * (a.1 / p * a.2) = a.1 * a.2 := by rw [← mul_assoc, Nat.mul_div_cancel' hq]
      _ = p * n := he
  · intro a ha b hb hab
    obtain ⟨ha, hda⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb, hdb⟩ := Finset.mem_filter.mp hb
    apply Prod.ext
    swap
    · have he := congrArg Prod.snd hab
      exact he
    have he := congrArg (fun x : ℕ × ℕ ↦ p * x.1) hab
    simpa only [Nat.mul_div_cancel' (hquot a ha hda), Nat.mul_div_cancel' (hquot b hb hdb)] using he
  · intro a ha
    obtain ⟨ha, hd⟩ := Finset.mem_filter.mp ha
    obtain ⟨he, hn⟩ := Nat.mem_divisorsAntidiagonal.mp ha
    refine ⟨(p * a.1, a.2), Finset.mem_filter.mpr ⟨?_, hd⟩, ?_⟩
    · exact Nat.mem_divisorsAntidiagonal.mpr ⟨by nlinarith [he], Nat.mul_ne_zero hp.ne_zero hn⟩
    · simp [Nat.mul_div_right _ hp.pos]
  · intro a ha
    obtain ⟨ha, hd⟩ := Finset.mem_filter.mp ha
    simp only [Nat.mul_div_cancel' (hquot a ha hd)]

/-- An entire odd-prime product row reduces exactly to a negative divisor annulus between `D/p` and `D`; divisors carrying that prime are excluded by the Möbius square-factor zero. -/
theorem pairedEtaMoebiusHighProductCoefficient_prime_mul {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (D n : ℕ) :
    pairedEtaMoebiusHighProductCoefficient D (p * n) =
      -∑ a ∈ n.divisorsAntidiagonal.filter
        (fun a ↦ D / p < a.2 ∧ a.2 ≤ D ∧ ¬p ∣ a.2),
          pairedEtaDirichletSign a.1 * μ a.2 := by
  rw [pairedEtaMoebiusHighProductCoefficient, Finset.sum_filter]
  rw [← Finset.sum_filter_add_sum_filter_not (p * n).divisorsAntidiagonal
    (fun a ↦ p ∣ a.2) (fun a ↦ if D < a.2 then pairedEtaDirichletSign a.1 * μ a.2 else 0)]
  rw [sum_prime_antidiagonal_dvd hp.pos n
      (fun q d ↦ if D < d then pairedEtaDirichletSign q * μ d else 0),
    sum_prime_antidiagonal_not_dvd hp n
      (fun q d ↦ if D < d then pairedEtaDirichletSign q * μ d else 0)]
  simp only [moebius_prime_mul_eq_not_dvd hp, etaSign_odd_mul hodd,
    Finset.sum_filter, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  have hcut : D / p < a.2 ↔ D < p * a.2 := by
    rw [Nat.div_lt_iff_lt_mul hp.pos, mul_comm]
  have hmono : D < a.2 → D < p * a.2 := fun h ↦
    h.trans_le (Nat.le_mul_of_pos_left _ hp.pos)
  simp only [hcut]
  by_cases hd : p ∣ a.2
  · simp [hd]
  by_cases hD : D < a.2
  · simp [hd, hD, hmono hD, Nat.not_le.mpr hD]
  · by_cases hDp : D < p * a.2 <;> simp [hd, hD, Nat.le_of_not_gt hD, hDp]

/-- The precise original divisor annulus left after removing an odd prime from the product. -/
def pairedEtaMoebiusPrimeAnnulus (p D : ℕ) : Finset ℕ :=
  (Finset.Ioc (D / p) D).filter (fun d ↦ ¬p ∣ d)

/-- Every divisor in the prime-removal annulus is positive and lies below the original cutoff. -/
theorem pairedEtaMoebiusPrimeAnnulus_subset (p D : ℕ) :
    pairedEtaMoebiusPrimeAnnulus p D ⊆ Finset.Icc 1 D := by
  intro d hd
  obtain ⟨hd, _⟩ := Finset.mem_filter.mp hd
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hd
  exact Finset.mem_Icc.mpr ⟨(Nat.zero_le _).trans_lt hlo, hhi⟩

/-- The literal completed high product prefix restricted to products divisible by `p`. -/
def pairedEtaCompletedMoebiusPrimeProductAggregate
    (rho : NontrivialZetaZero) (p D M : ℕ) : ℂ :=
  pairedEtaXiCompletionFactor rho.1 *
    ∑ n ∈ (Finset.Icc 1 M).filter (fun n ↦ p ∣ n),
      (pairedEtaMoebiusHighProductCoefficient D n : ℂ) * (n : ℂ) ^ (-rho.1)

private theorem sum_Icc_dvd_eq_divided {p : ℕ} (hp : 0 < p) (M : ℕ) (f : ℕ → ℂ) :
    (∑ n ∈ (Finset.Icc 1 M).filter (fun n ↦ p ∣ n), f n) =
      ∑ n ∈ Finset.Icc 1 (M / p), f (p * n) := by
  apply Finset.sum_bij (fun n _ ↦ n / p)
  · intro n hn
    obtain ⟨hn, hd⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hnM⟩ := Finset.mem_Icc.mp hn
    apply Finset.mem_Icc.mpr
    refine ⟨?_, Nat.div_le_div_right hnM⟩
    have he := Nat.mul_div_cancel' hd
    by_contra h
    have hz : n / p = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, mul_zero] at he
    omega
  · intro a ha b hb hab
    have hda := (Finset.mem_filter.mp ha).2
    have hdb := (Finset.mem_filter.mp hb).2
    have h := congrArg (fun n : ℕ ↦ p * n) hab
    simpa only [Nat.mul_div_cancel' hda, Nat.mul_div_cancel' hdb] using h
  · intro n hn
    obtain ⟨hn1, hnM⟩ := Finset.mem_Icc.mp hn
    refine ⟨p * n, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by nlinarith, ?_⟩,
      dvd_mul_right p n⟩, Nat.mul_div_right n hp⟩
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp).mp hnM
  · intro n hn
    rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2]

/-- All products divisible by an odd prime reduce to the original selected Möbius divisor annulus at the exact divided physical cutoff, with the full complex prime multiplier. -/
theorem pairedEtaCompletedMoebiusPrimeProductAggregate_eq_annulus
    (rho : NontrivialZetaZero) {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    {D M : ℕ} (hDM : D ≤ M / p) :
    pairedEtaCompletedMoebiusPrimeProductAggregate rho p D M =
      -(p : ℂ) ^ (-rho.1) *
        pairedEtaCompletedMoebiusSelectedAggregate rho (pairedEtaMoebiusPrimeAnnulus p D) (M / p) := by
  have hS : pairedEtaMoebiusPrimeAnnulus p D ⊆ Finset.Icc 1 (M / p) := by
    intro d hd
    obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.mp (pairedEtaMoebiusPrimeAnnulus_subset p D hd)
    exact Finset.mem_Icc.mpr ⟨hd1, hdD.trans hDM⟩
  have hfilter (n : ℕ) : n.divisorsAntidiagonal.filter
      (fun a ↦ D / p < a.2 ∧ a.2 ≤ D ∧ ¬p ∣ a.2) =
        n.divisorsAntidiagonal.filter (fun a ↦ a.2 ∈ pairedEtaMoebiusPrimeAnnulus p D) := by
    ext a
    simp [pairedEtaMoebiusPrimeAnnulus, and_assoc]
  rw [pairedEtaCompletedMoebiusPrimeProductAggregate,
    sum_Icc_dvd_eq_divided hp.pos M,
    pairedEtaCompletedMoebiusSelectedAggregate_eq_products rho hS]
  simp only [pairedEtaMoebiusHighProductCoefficient_prime_mul hp hodd, hfilter,
    Int.cast_neg, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- On a complete prime-multiple physical window every divided endpoint occurs exactly `p` times. The normalized mean square retains the exact prime norm factor. -/
theorem pairedEtaCompletedMoebiusPrimeProductAggregate_meanSquare_eq_annulus
    (rho : NontrivialZetaZero) {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    {A D : ℕ} (hDA : D ≤ A) (L : ℕ) :
    (∑ t ∈ Finset.range (p * L),
      ‖pairedEtaCompletedMoebiusPrimeProductAggregate rho p D (p * A + t)‖ ^ 2) / (p * L : ℕ) =
      (p : ℝ) ^ (-2 * rho.1.re) *
        ((∑ t ∈ Finset.range L,
          ‖pairedEtaCompletedMoebiusSelectedAggregate rho (pairedEtaMoebiusPrimeAnnulus p D) (A + t)‖ ^ 2) / L) := by
  have hdiv (t : ℕ) : (p * A + t) / p = A + t / p := by
    rw [Nat.add_comm, Nat.add_mul_div_left t A hp.pos, Nat.add_comm]
  have hnorm (t : ℕ) :
      ‖pairedEtaCompletedMoebiusPrimeProductAggregate rho p D (p * A + t)‖ ^ 2 =
        (p : ℝ) ^ (-2 * rho.1.re) *
          ‖pairedEtaCompletedMoebiusSelectedAggregate rho (pairedEtaMoebiusPrimeAnnulus p D) (A + t / p)‖ ^ 2 := by
    rw [pairedEtaCompletedMoebiusPrimeProductAggregate_eq_annulus rho hp hodd
      (by rw [hdiv]; exact hDA.trans (Nat.le_add_right _ _)), hdiv, norm_mul, norm_neg,
      Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re, mul_pow,
      ← Real.rpow_mul_natCast (Nat.cast_nonneg p)]
    norm_num only [Nat.cast_ofNat]
    congr 2
    ring
  simp_rw [hnorm]
  rw [← Finset.mul_sum, sum_range_div_blocks
    (fun t ↦ ‖pairedEtaCompletedMoebiusSelectedAggregate rho (pairedEtaMoebiusPrimeAnnulus p D) (A + t)‖ ^ 2)
    hp.pos L, nsmul_eq_mul]
  push_cast
  by_cases hL : L = 0
  · simp [hL]
  · have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast hL
    field_simp

/-- The whole odd-prime product family has an unconditional physical mean-square estimate from its exact selected low-divisor annulus, including the complete sampling-window loss. -/
theorem pairedEtaCompletedMoebiusPrimeProductAggregate_meanSquare_le_window
    (rho : NontrivialZetaZero) {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    {A L D : ℕ} (hA : 1 ≤ A) (hL : 0 < L) (hD : 1 ≤ D) (hDA : D ≤ A) :
    (∑ t ∈ Finset.range (p * L),
      ‖pairedEtaCompletedMoebiusPrimeProductAggregate rho p D (p * A + t)‖ ^ 2) / (p * L : ℕ) ≤
      (p : ℝ) ^ (-2 * rho.1.re) * (A : ℝ) ^ (-2 * rho.1.re) *
        (‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 2 * finiteCircleSamplingConstant *
          ((4 * (D : ℝ) ^ 2 + L) / L) * (1 + Real.log D) ^ 2 * D +
          2 * (pairedEtaCompletedMoebiusPhysicalErrorConstant rho +
            2 * pairedEtaCompletedMoebiusPhaseErrorConstant rho) ^ 2 *
            (D : ℝ) ^ 4 / (A : ℝ) ^ 2) := by
  rw [pairedEtaCompletedMoebiusPrimeProductAggregate_meanSquare_eq_annulus rho hp hodd hDA L,
    mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (pairedEtaCompletedMoebiusSelectedAggregate_meanSquare_le_window rho
      (pairedEtaMoebiusPrimeAnnulus_subset p D) hA hL hD hDA) (by positivity)

end

end RiemannGaussian
