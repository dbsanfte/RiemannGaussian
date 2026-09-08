import RiemannGaussian.EtaMoebiusPrimeFirstMean

/-!
# Joint cancellation in products carrying a large prime

Above twice the square root of the physical starting cutoff, a product
has at most one prime from the selected family. Removing that prime keeps
the entire smaller-cutoff Möbius coefficient, including its composites.
The difference between this whole product group and its explicit prime
and twice-prime sum is exactly a selection of the original low divisors.
Its complex first mean therefore has a vanishing quartic allowance.

The explicit prime sum remains paired with the complementary product
group. This theorem does not bound their combined residual below the
source, and does not assert a whole-window mean-square bound or RH.
-/

open Complex Filter
open scoped Classical Topology ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

private theorem high_coefficient_prime_small_cofactor {p D n : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hn : n ≤ D) (hcop : ¬p ∣ n) :
    pairedEtaMoebiusHighProductCoefficient D (p * n) =
      -pairedEtaMoebiusHighProductCoefficient (D / p) n := by
  rw [pairedEtaMoebiusHighProductCoefficient_prime_mul hp hodd,
    pairedEtaMoebiusHighProductCoefficient]
  congr 2
  apply Finset.filter_congr
  intro a ha
  have hd : a.2 ∣ n := ⟨a.1, by
    have he := (Nat.mem_divisorsAntidiagonal.mp ha).1
    nlinarith⟩
  have hnpos : 0 < n := Nat.pos_of_ne_zero (Nat.mem_divisorsAntidiagonal.mp ha).2
  have haD : a.2 ≤ D := (Nat.le_of_dvd hnpos hd).trans hn
  have hap : ¬p ∣ a.2 := fun h ↦ hcop (h.trans hd)
  simp [haD, hap]

/-- Removing a prime larger than every cofactor retains the full original high-divisor aggregate at the exact divided cutoffs. -/
theorem pairedEtaCompletedMoebiusPrimeProductAggregate_eq_divided_large
    (rho : NontrivialZetaZero) {p D M : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hMD : M / p ≤ D) (hMp : M < p * p) :
    pairedEtaCompletedMoebiusPrimeProductAggregate rho p D M =
      -(p : ℂ) ^ (-rho.1) *
        pairedEtaCompletedMoebiusLargeAggregate rho (M / p) (D / p) := by
  have hmp : M / p < p := (Nat.div_lt_iff_lt_mul hp.pos).mpr hMp
  rw [pairedEtaCompletedMoebiusPrimeProductAggregate,
    sum_Icc_dvd_eq_divided hp.pos M,
    pairedEtaCompletedMoebiusLargeAggregate_eq_product_prefix,
    pairedEtaMoebiusHighProductPrefix]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hn1, hnM⟩ := Finset.mem_Icc.mp hn
  have hcop : ¬p ∣ n := fun h ↦ by
    have hpn := Nat.le_of_dvd hn1 h
    omega
  rw [high_coefficient_prime_small_cofactor hp hodd (hnM.trans hMD) hcop,
    Int.cast_neg, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  ring

private theorem prime_low_eq_divided (rho : NontrivialZetaZero)
    {p D M : ℕ} (hp : p.Prime) (hDM : D ≤ M) (hMp : M < p * p) :
    pairedEtaCompletedMoebiusSelectedAggregate rho
        ((Finset.Icc 1 D).filter (fun d ↦ p ∣ d)) M =
      -(p : ℂ) ^ (-rho.1) *
        pairedEtaCompletedMoebiusPartialAggregate rho (M / p) (D / p) := by
  have hdp : D / p < p := (Nat.div_lt_iff_lt_mul hp.pos).mpr (hDM.trans_lt hMp)
  rw [pairedEtaCompletedMoebiusSelectedAggregate,
    sum_Icc_dvd_eq_divided hp.pos D,
    pairedEtaCompletedMoebiusPartialAggregate, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.mp hd
  have hcop : ¬p ∣ d := fun h ↦ by
    have hpd := Nat.le_of_dvd hd1 h
    omega
  rw [pairedEtaCompletedMoebiusTerm_eq_completed_prefix,
    pairedEtaCompletedMoebiusTerm_eq_completed_prefix,
    moebius_prime_mul_eq_not_dvd hp, if_neg hcop, Int.cast_neg,
    Nat.cast_mul, Complex.natCast_mul_natCast_cpow, Nat.div_div_eq_div_mul]
  ring

/-- The explicit prime and twice-prime contribution, with their literal physical cutoffs and complex powers. -/
def pairedEtaMoebiusLargePrimeModelTerm (rho : NontrivialZetaZero) (p M : ℕ) : ℂ :=
  pairedEtaXiCompletionFactor rho.1 *
    ((if 2 * p ≤ M then 2 * ((2 * p : ℕ) : ℂ) ^ (-rho.1) else 0) -
      if p ≤ M then (p : ℂ) ^ (-rho.1) else 0)

private theorem tail_aggregate_all_cutoffs (rho : NontrivialZetaZero) (M : ℕ) :
    pairedEtaCompletedMoebiusTailAggregate rho M =
      pairedEtaXiCompletionFactor rho.1 *
        ((if 1 ≤ M then 1 else 0) - (if 2 ≤ M then 2 * (2 : ℂ) ^ (-rho.1) else 0)) := by
  by_cases hM : 2 ≤ M
  · rw [pairedEtaCompletedMoebiusTailAggregate_eq_source rho hM]
    simp [pairedEtaCompletedMoebiusSource, hM, show 1 ≤ M by omega]
  have h : M = 0 ∨ M = 1 := by omega
  rcases h with rfl | rfl
  · rw [← sum_pairedEtaCompletedMoebiusTerm]
    simp
  · rw [← sum_pairedEtaCompletedMoebiusTerm]
    simp only [Finset.Icc_self, Finset.sum_singleton]
    rw [pairedEtaCompletedMoebiusTerm_eq_completed_prefix]
    norm_num [pairedEtaUnpairedDirichletPrefix, pairedEtaDirichletSign]

/-- The prime model is the negative exact finite eta source at the divided endpoint, including the exceptional zero and one cutoffs. -/
theorem pairedEtaMoebiusLargePrimeModelTerm_eq_divided_source
    (rho : NontrivialZetaZero) {p : ℕ} (hp : 0 < p) (M : ℕ) :
    pairedEtaMoebiusLargePrimeModelTerm rho p M =
      -(p : ℂ) ^ (-rho.1) * pairedEtaCompletedMoebiusTailAggregate rho (M / p) := by
  rw [tail_aggregate_all_cutoffs, pairedEtaMoebiusLargePrimeModelTerm]
  have h1 : 1 ≤ M / p ↔ p ≤ M := by simpa using Nat.le_div_iff_mul_le hp (x := 1)
  have h2 : 2 ≤ M / p ↔ 2 * p ≤ M := Nat.le_div_iff_mul_le hp
  have hpow : ((2 * p : ℕ) : ℂ) ^ (-rho.1) =
      (2 : ℂ) ^ (-rho.1) * (p : ℂ) ^ (-rho.1) := by
    rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    norm_num
  simp only [h1, h2, hpow]
  split_ifs <;> ring

/-- The entire large-prime product row differs from its explicit prime pair by exactly the original low divisors carrying that prime. -/
theorem pairedEtaCompletedMoebiusPrimeProductAggregate_sub_model
    (rho : NontrivialZetaZero) {p D M : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hDM : D ≤ M) (hMD : M / p ≤ D) (hMp : M < p * p) :
    pairedEtaCompletedMoebiusPrimeProductAggregate rho p D M -
        pairedEtaMoebiusLargePrimeModelTerm rho p M =
      -pairedEtaCompletedMoebiusSelectedAggregate rho
        ((Finset.Icc 1 D).filter (fun d ↦ p ∣ d)) M := by
  rw [pairedEtaCompletedMoebiusPrimeProductAggregate_eq_divided_large rho hp hodd hMD hMp,
    pairedEtaMoebiusLargePrimeModelTerm_eq_divided_source rho hp.pos,
    prime_low_eq_divided rho hp hDM hMp]
  have he := pairedEtaCompletedMoebiusPartial_add_large rho
    (M := M / p) (D := D / p) (Nat.div_le_div_right hDM)
  rw [← he]
  ring

/-- The odd primes above twice the square-root scale, through the largest physical endpoint. -/
def pairedEtaMoebiusLargePrimeFamily (u : ℕ) : Finset ℕ :=
  (pairedEtaMoebiusOddPrimeMeanFamily (2 * u ^ 4)).filter (fun p ↦ 2 * u ^ 2 < p)

/-- A product has a selected large odd prime as a factor. -/
def pairedEtaMoebiusHasLargePrime (u n : ℕ) : Prop :=
  ∃ p ∈ pairedEtaMoebiusLargePrimeFamily u, p ∣ n

/-- The original low divisors carrying one of the selected large primes. -/
def pairedEtaMoebiusLargePrimeLowDivisors (u : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (u ^ 3)).filter (pairedEtaMoebiusHasLargePrime u)

private theorem large_prime_geometry {u p M : ℕ} (hu : 1 ≤ u)
    (hp : p ∈ pairedEtaMoebiusLargePrimeFamily u) (hM : M ≤ 2 * u ^ 4) :
    p.Prime ∧ Odd p ∧ M / p ≤ u ^ 3 ∧ M < p * p := by
  obtain ⟨hp, hcut⟩ := Finset.mem_filter.mp hp
  obtain ⟨_, hprime, hodd⟩ := Finset.mem_filter.mp hp
  have hu2 : 0 < u ^ 2 := pow_pos (by omega) 2
  have hprod := Nat.mul_lt_mul_of_pos_right hcut hu2
  have hdiv : M / p < u ^ 2 := by
    apply (Nat.div_lt_iff_lt_mul hprime.pos).mpr
    nlinarith
  have h23 : u ^ 2 ≤ u ^ 3 := Nat.pow_le_pow_right hu (by norm_num)
  refine ⟨hprime, hodd, hdiv.le.trans h23, ?_⟩
  have hs := Nat.mul_self_lt_mul_self hcut
  nlinarith

/-- At most one selected large prime can divide a positive product in the complete physical window. -/
theorem pairedEtaMoebiusLargePrimeFamily_unique {u n p q : ℕ}
    (hu : 1 ≤ u) (hn : 1 ≤ n) (hnM : n ≤ 2 * u ^ 4)
    (hp : p ∈ pairedEtaMoebiusLargePrimeFamily u)
    (hq : q ∈ pairedEtaMoebiusLargePrimeFamily u) (hpn : p ∣ n) (hqn : q ∣ n) : p = q := by
  by_contra hne
  have hpp := (large_prime_geometry hu hp hnM).1
  have hqp := (large_prime_geometry hu hq hnM).1
  have hprod := Nat.le_of_dvd hn (Nat.Prime.dvd_mul_of_dvd_ne hne hpp hqp hpn hqn)
  have hpB := (Finset.mem_filter.mp hp).2
  have hqB := (Finset.mem_filter.mp hq).2
  have hh := Nat.mul_lt_mul_of_lt_of_lt hpB hqB
  have hu4 : 0 < u ^ 4 := pow_pos (by omega) 4
  nlinarith

private theorem sum_large_prime_dvd {u n : ℕ} (hu : 1 ≤ u)
    (hn : 1 ≤ n) (hnM : n ≤ 2 * u ^ 4) (z : ℂ) :
    (∑ p ∈ pairedEtaMoebiusLargePrimeFamily u, if p ∣ n then z else 0) =
      if pairedEtaMoebiusHasLargePrime u n then z else 0 := by
  by_cases h : pairedEtaMoebiusHasLargePrime u n
  · rw [if_pos h]
    obtain ⟨p, hp, hpn⟩ := h
    calc
      _ = if p ∣ n then z else 0 := by
        apply Finset.sum_eq_single p
        · intro q hq hqp
          have hqn : ¬q ∣ n := fun h ↦
            hqp (pairedEtaMoebiusLargePrimeFamily_unique hu hn hnM hq hp h hpn)
          simp [hqn]
        · intro hnot
          exact (hnot hp).elim
      _ = z := if_pos hpn
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro p hp
    have hpn : ¬p ∣ n := fun hd ↦ h ⟨p, hp, hd⟩
    simp [hpn]

/-- The literal original product group containing a large prime, including all its composite products. -/
def pairedEtaMoebiusLargePrimeProductAggregate (rho : NontrivialZetaZero) (u M : ℕ) : ℂ :=
  pairedEtaXiCompletionFactor rho.1 *
    ∑ n ∈ (Finset.Icc 1 M).filter (pairedEtaMoebiusHasLargePrime u),
      (pairedEtaMoebiusHighProductCoefficient (u ^ 3) n : ℂ) * (n : ℂ) ^ (-rho.1)

/-- The full explicit prime-pair sum, with no prime-density approximation. -/
def pairedEtaMoebiusLargePrimeModelAggregate (rho : NontrivialZetaZero) (u M : ℕ) : ℂ :=
  ∑ p ∈ pairedEtaMoebiusLargePrimeFamily u, pairedEtaMoebiusLargePrimeModelTerm rho p M

/-- The disjoint large-prime product classes sum to their literal union, without an overlap error. -/
theorem sum_pairedEtaCompletedMoebiusPrimeProductAggregate_large
    (rho : NontrivialZetaZero) {u M : ℕ} (hu : 1 ≤ u) (hM : M ≤ 2 * u ^ 4) :
    (∑ p ∈ pairedEtaMoebiusLargePrimeFamily u,
      pairedEtaCompletedMoebiusPrimeProductAggregate rho p (u ^ 3) M) =
        pairedEtaMoebiusLargePrimeProductAggregate rho u M := by
  simp only [pairedEtaCompletedMoebiusPrimeProductAggregate,
    pairedEtaMoebiusLargePrimeProductAggregate, Finset.sum_filter]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  exact sum_large_prime_dvd hu (Finset.mem_Icc.mp hn).1
    ((Finset.mem_Icc.mp hn).2.trans hM) _

private theorem sum_large_prime_low (rho : NontrivialZetaZero) {u : ℕ} (hu : 1 ≤ u) (M : ℕ) :
    (∑ p ∈ pairedEtaMoebiusLargePrimeFamily u,
      pairedEtaCompletedMoebiusSelectedAggregate rho
        ((Finset.Icc 1 (u ^ 3)).filter (fun d ↦ p ∣ d)) M) =
      pairedEtaCompletedMoebiusSelectedAggregate rho (pairedEtaMoebiusLargePrimeLowDivisors u) M := by
  have h34 : u ^ 3 ≤ u ^ 4 := Nat.pow_le_pow_right hu (by norm_num)
  simp only [pairedEtaCompletedMoebiusSelectedAggregate,
    pairedEtaMoebiusLargePrimeLowDivisors, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  exact sum_large_prime_dvd hu (Finset.mem_Icc.mp hd).1
    ((Finset.mem_Icc.mp hd).2.trans (by omega)) _

/-- Jointly retaining all prime and composite products above the large-prime threshold leaves exactly a selected low-divisor correction to the explicit prime-pair model. -/
theorem pairedEtaMoebiusLargePrimeProductAggregate_sub_model
    (rho : NontrivialZetaZero) {u M : ℕ} (hu : 1 ≤ u)
    (hMlo : u ^ 3 ≤ M) (hMhi : M ≤ 2 * u ^ 4) :
    pairedEtaMoebiusLargePrimeProductAggregate rho u M -
        pairedEtaMoebiusLargePrimeModelAggregate rho u M =
      -pairedEtaCompletedMoebiusSelectedAggregate rho (pairedEtaMoebiusLargePrimeLowDivisors u) M := by
  rw [← sum_pairedEtaCompletedMoebiusPrimeProductAggregate_large rho hu hMhi,
    pairedEtaMoebiusLargePrimeModelAggregate, ← Finset.sum_sub_distrib]
  calc
    _ = ∑ p ∈ pairedEtaMoebiusLargePrimeFamily u,
        -pairedEtaCompletedMoebiusSelectedAggregate rho
          ((Finset.Icc 1 (u ^ 3)).filter (fun d ↦ p ∣ d)) M := by
      apply Finset.sum_congr rfl
      intro p hp
      obtain ⟨hprime, hodd, hMD, hMp⟩ := large_prime_geometry hu hp hMhi
      exact pairedEtaCompletedMoebiusPrimeProductAggregate_sub_model rho
        hprime hodd hMlo hMD hMp
    _ = _ := by rw [Finset.sum_neg_distrib, sum_large_prime_low rho hu]

/-- The complex mean of the literal large-prime product group over every quartic physical endpoint. -/
def pairedEtaMoebiusLargePrimeProductFirstMean (rho : NontrivialZetaZero) (u : ℕ) : ℂ :=
  (∑ t ∈ Finset.range (u ^ 4), pairedEtaMoebiusLargePrimeProductAggregate rho u (u ^ 4 + t)) / u ^ 4

/-- The complex mean of the explicit prime-pair model on the same complete physical window. -/
def pairedEtaMoebiusLargePrimeModelFirstMean (rho : NontrivialZetaZero) (u : ℕ) : ℂ :=
  (∑ t ∈ Finset.range (u ^ 4), pairedEtaMoebiusLargePrimeModelAggregate rho u (u ^ 4 + t)) / u ^ 4

/-- The exact joint large-prime error in the first mean is an unchanged selected low-divisor mean. -/
theorem pairedEtaMoebiusLargePrimeProductFirstMean_sub_model
    (rho : NontrivialZetaZero) {u : ℕ} (hu : 1 ≤ u) :
    pairedEtaMoebiusLargePrimeProductFirstMean rho u - pairedEtaMoebiusLargePrimeModelFirstMean rho u =
      -pairedEtaCompletedMoebiusSelectedFirstMean rho (pairedEtaMoebiusLargePrimeLowDivisors u) (u ^ 4) := by
  have h34 : u ^ 3 ≤ u ^ 4 := Nat.pow_le_pow_right hu (by norm_num)
  unfold pairedEtaMoebiusLargePrimeProductFirstMean pairedEtaMoebiusLargePrimeModelFirstMean
    pairedEtaCompletedMoebiusSelectedFirstMean
  rw [← sub_div, ← Finset.sum_sub_distrib, ← neg_div, ← Finset.sum_neg_distrib]
  simp only [Nat.cast_pow]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  exact pairedEtaMoebiusLargePrimeProductAggregate_sub_model rho hu (by omega)
    (by have := Finset.mem_range.mp ht; omega)

/-- The whole large-prime group, including its composites, differs from the explicit prime model by a negative-power allowance to the right of one half. -/
theorem norm_pairedEtaMoebiusLargePrimeProductFirstMean_sub_model_le
    (rho : NontrivialZetaZero) {u : ℕ} (hu : 1 ≤ u) :
    ‖pairedEtaMoebiusLargePrimeProductFirstMean rho u - pairedEtaMoebiusLargePrimeModelFirstMean rho u‖ ≤
      pairedEtaMoebiusFirstMeanConstant rho * (u : ℝ) ^ (2 - 4 * rho.1.re) := by
  rw [pairedEtaMoebiusLargePrimeProductFirstMean_sub_model rho hu, norm_neg]
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hb := norm_pairedEtaCompletedMoebiusSelectedFirstMean_le rho
    (S := pairedEtaMoebiusLargePrimeLowDivisors u) (A := u ^ 4) (D := u ^ 3)
    (Finset.filter_subset _ _) (Nat.one_le_pow _ _ hu)
    (Nat.pow_le_pow_right hu (by norm_num))
  apply hb.trans_eq
  simp only [Nat.cast_pow]
  rw [← Real.rpow_natCast_mul huR.le, ← pow_mul,
    ← Real.rpow_natCast (u : ℝ) (3 * 2), mul_assoc, ← Real.rpow_add huR]
  congr 2
  norm_num
  ring

/-- At a hypothetical right-half zero the full large-prime group minus its explicit prime model tends to zero. The model itself is not asserted to decay. -/
theorem pairedEtaMoebiusLargePrimeProductFirstMean_sub_model_tendsto_zero
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    Tendsto (fun u : ℕ ↦ pairedEtaMoebiusLargePrimeProductFirstMean rho u -
      pairedEtaMoebiusLargePrimeModelFirstMean rho u) atTop (𝓝 0) := by
  have hp : Tendsto (fun u : ℕ ↦ (u : ℝ) ^ (2 - 4 * rho.1.re)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (by linarith : 0 < 4 * rho.1.re - 2)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)) using 1
    ext u
    simp only [Function.comp_apply]
    congr 1
    ring
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _))
    ((eventually_ge_atTop 1).mono fun _ hu ↦
      norm_pairedEtaMoebiusLargePrimeProductFirstMean_sub_model_le rho hu)
  simpa only [mul_zero] using hp.const_mul (pairedEtaMoebiusFirstMeanConstant rho)

/-- The literal complementary product group, containing no selected large prime. -/
def pairedEtaMoebiusSmoothProductAggregate (rho : NontrivialZetaZero) (u M : ℕ) : ℂ :=
  pairedEtaXiCompletionFactor rho.1 *
    ∑ n ∈ (Finset.Icc 1 M).filter (fun n ↦ ¬pairedEtaMoebiusHasLargePrime u n),
      (pairedEtaMoebiusHighProductCoefficient (u ^ 3) n : ℂ) * (n : ℂ) ^ (-rho.1)

/-- Both original product groups reconstruct the full high-divisor carrier with their complex signs unchanged. -/
theorem pairedEtaMoebiusLargePrime_add_smooth
    (rho : NontrivialZetaZero) (u M : ℕ) :
    pairedEtaMoebiusLargePrimeProductAggregate rho u M +
      pairedEtaMoebiusSmoothProductAggregate rho u M =
        pairedEtaCompletedMoebiusLargeAggregate rho M (u ^ 3) := by
  rw [pairedEtaMoebiusLargePrimeProductAggregate, pairedEtaMoebiusSmoothProductAggregate,
    ← mul_add, Finset.sum_filter_add_sum_filter_not,
    pairedEtaCompletedMoebiusLargeAggregate_eq_product_prefix,
    pairedEtaMoebiusHighProductPrefix]

/-- The full first mean pairing the explicit prime model with every complementary product, before taking any norm. -/
def pairedEtaMoebiusPrimeSmoothFirstMean (rho : NontrivialZetaZero) (u : ℕ) : ℂ :=
  (∑ t ∈ Finset.range (u ^ 4),
    (pairedEtaMoebiusLargePrimeModelAggregate rho u (u ^ 4 + t) +
      pairedEtaMoebiusSmoothProductAggregate rho u (u ^ 4 + t))) / u ^ 4

/-- The prime model and complementary products retain the whole original first mean minus precisely the controlled joint large-prime error. -/
theorem pairedEtaMoebiusPrimeSmoothFirstMean_eq_high_sub_error
    (rho : NontrivialZetaZero) (u : ℕ) :
    pairedEtaMoebiusPrimeSmoothFirstMean rho u =
      pairedEtaCompletedMoebiusLargeFirstMean rho (u ^ 4) (u ^ 3) -
        (pairedEtaMoebiusLargePrimeProductFirstMean rho u -
          pairedEtaMoebiusLargePrimeModelFirstMean rho u) := by
  unfold pairedEtaMoebiusPrimeSmoothFirstMean pairedEtaCompletedMoebiusLargeFirstMean
    pairedEtaMoebiusLargePrimeProductFirstMean pairedEtaMoebiusLargePrimeModelFirstMean
  simp only [Nat.cast_pow]
  rw [← sub_div, ← sub_div, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  have he := pairedEtaMoebiusLargePrime_add_smooth rho u (u ^ 4 + t)
  linear_combination he

/-- Replacing all large-prime products by their exact prime model costs only the vanishing joint first-mean allowance. -/
theorem norm_pairedEtaMoebiusPrimeSmoothFirstMean_sub_high_le
    (rho : NontrivialZetaZero) {u : ℕ} (hu : 1 ≤ u) :
    ‖pairedEtaMoebiusPrimeSmoothFirstMean rho u -
      pairedEtaCompletedMoebiusLargeFirstMean rho (u ^ 4) (u ^ 3)‖ ≤
        pairedEtaMoebiusFirstMeanConstant rho * (u : ℝ) ^ (2 - 4 * rho.1.re) := by
  rw [pairedEtaMoebiusPrimeSmoothFirstMean_eq_high_sub_error, sub_sub_cancel_left, norm_neg]
  exact norm_pairedEtaMoebiusLargePrimeProductFirstMean_sub_model_le rho hu

/-- The retained joint prime/smooth first mean still approaches the nonzero source, with an explicit power allowance for its two controlled low-divisor errors. -/
theorem norm_pairedEtaMoebiusPrimeSmoothFirstMean_sub_source_le
    (rho : NontrivialZetaZero) {u : ℕ} (hu : 2 ≤ u) :
    ‖pairedEtaMoebiusPrimeSmoothFirstMean rho u - pairedEtaCompletedMoebiusSource rho‖ ≤
      2 * pairedEtaMoebiusFirstMeanConstant rho * (u : ℝ) ^ (2 - 4 * rho.1.re) := by
  apply (norm_sub_le_norm_sub_add_norm_sub _
    (pairedEtaCompletedMoebiusLargeFirstMean rho (u ^ 4) (u ^ 3)) _).trans
  apply (add_le_add (norm_pairedEtaMoebiusPrimeSmoothFirstMean_sub_high_le rho (by omega))
    (norm_pairedEtaCompletedMoebiusLargeFirstMean_quartic_sub_source_le rho hu)).trans_eq
  ring

/-- The explicit prime model paired with all complementary products retains the source limit at a hypothetical right-half zero. An independent upper bound for this full signed mean remains open. -/
theorem pairedEtaMoebiusPrimeSmoothFirstMean_tendsto_source
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    Tendsto (pairedEtaMoebiusPrimeSmoothFirstMean rho) atTop (𝓝 (pairedEtaCompletedMoebiusSource rho)) := by
  have hh := (pairedEtaCompletedMoebiusLargeFirstMean_quartic_tendsto_source rho hrho).sub
    (pairedEtaMoebiusLargePrimeProductFirstMean_sub_model_tendsto_zero rho hrho)
  simpa only [sub_zero, ← pairedEtaMoebiusPrimeSmoothFirstMean_eq_high_sub_error] using hh

end

end RiemannGaussian
