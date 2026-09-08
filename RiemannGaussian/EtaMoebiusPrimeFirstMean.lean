import RiemannGaussian.EtaMoebiusQuarterQuotientMean
import RiemannGaussian.EtaMoebiusPrimeProduct

/-!
# Simultaneous prime cancellation in the complex physical mean

An odd-prime product class is exactly a selection of the original divisor
terms at indices `p*d`. Applying the direct parity estimate at those
indices avoids dividing the physical window, and therefore requires no
divisibility of its starting scale by the prime. On quartic windows the
whole class has first-mean norm at most `C_rho*p*u^(2-4*Re(rho))`.

Summing these norms controls all odd primes through a polynomially growing
cutoff simultaneously. Weighted combinations retain their exact product
multiplicities. This is cancellation of complex first means; it does not
assert a bound for a prime-free union, the whole mean square, or RH.
-/

open Complex Filter
open scoped Classical Topology ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- Moving the odd prime into its coprime divisor rewrites the whole product class as unchanged original terms, without changing the physical cutoff. -/
theorem pairedEtaCompletedMoebiusPrimeProductAggregate_eq_original_annulus
    (rho : NontrivialZetaZero) {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    {D M : ℕ} (hDM : p * D ≤ M) :
    pairedEtaCompletedMoebiusPrimeProductAggregate rho p D M =
      ∑ d ∈ pairedEtaMoebiusPrimeAnnulus p D, pairedEtaCompletedMoebiusTerm rho M (p * d) := by
  rw [pairedEtaCompletedMoebiusPrimeProductAggregate_eq_annulus rho hp hodd
    ((Nat.le_div_iff_mul_le hp.pos).mpr (by simpa only [mul_comm] using hDM)),
    pairedEtaCompletedMoebiusSelectedAggregate, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hpd := (Finset.mem_filter.mp hd).2
  rw [pairedEtaCompletedMoebiusTerm_eq_completed_prefix,
    pairedEtaCompletedMoebiusTerm_eq_completed_prefix, moebius_prime_mul_eq_not_dvd hp,
    if_neg hpd, Int.cast_neg, Nat.cast_mul, Complex.natCast_mul_natCast_cpow,
    Nat.div_div_eq_div_mul]
  ring

/-- The complex physical first mean of an entire odd-prime product class. -/
def pairedEtaMoebiusPrimeProductFirstMean (rho : NontrivialZetaZero) (p A D : ℕ) : ℂ :=
  (∑ t ∈ Finset.range A, pairedEtaCompletedMoebiusPrimeProductAggregate rho p D (A + t)) / A

/-- A whole prime class has a first-mean estimate with linear prime cost and no prime divisibility requirement on the window. -/
theorem norm_pairedEtaMoebiusPrimeProductFirstMean_le
    (rho : NontrivialZetaZero) {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    {A D : ℕ} (hA : 1 ≤ A) (hDA : p * D ≤ A) :
    ‖pairedEtaMoebiusPrimeProductFirstMean rho p A D‖ ≤
      pairedEtaMoebiusFirstMeanConstant rho * p * (D : ℝ) ^ 2 *
        (A : ℝ) ^ (-rho.1.re - 1) := by
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hC := pairedEtaMoebiusFirstMeanConstant_nonneg rho
  have hcard : ((pairedEtaMoebiusPrimeAnnulus p D).card : ℝ) ≤ D := by
    exact_mod_cast (Finset.card_le_card (pairedEtaMoebiusPrimeAnnulus_subset p D)).trans_eq
      (by simp)
  have hsum : ‖∑ t ∈ Finset.range A,
      pairedEtaCompletedMoebiusPrimeProductAggregate rho p D (A + t)‖ ≤
        pairedEtaMoebiusFirstMeanConstant rho * p * (D : ℝ) ^ 2 *
          (A : ℝ) ^ (-rho.1.re) := by
    simp_rw [pairedEtaCompletedMoebiusPrimeProductAggregate_eq_original_annulus rho hp hodd
      (hDA.trans (Nat.le_add_right A _))]
    rw [Finset.sum_comm]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _d ∈ pairedEtaMoebiusPrimeAnnulus p D,
          pairedEtaMoebiusFirstMeanConstant rho * (p * D : ℕ) * (A : ℝ) ^ (-rho.1.re) := by
        apply Finset.sum_le_sum
        intro d hd
        obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.mp (pairedEtaMoebiusPrimeAnnulus_subset p D hd)
        have hpdD := Nat.mul_le_mul_left p hdD
        apply (norm_sum_pairedEtaCompletedMoebiusTerm_le_firstMean rho hA
          (Nat.mul_pos hp.pos hd1) (hpdD.trans hDA)).trans
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by exact_mod_cast hpdD) hC) (by positivity)
      _ ≤ (D : ℝ) * (pairedEtaMoebiusFirstMeanConstant rho * (p * D : ℕ) *
          (A : ℝ) ^ (-rho.1.re)) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by push_cast; ring
  rw [pairedEtaMoebiusPrimeProductFirstMean, norm_div, Complex.norm_natCast]
  apply (div_le_div_of_nonneg_right hsum hAR.le).trans_eq
  rw [Real.rpow_sub hAR, Real.rpow_one]
  ring

/-- Every odd prime through `u` has a quartic first-mean allowance linear in that prime, on every scale `u`. -/
theorem norm_pairedEtaMoebiusPrimeProductFirstMean_quartic_le
    (rho : NontrivialZetaZero) {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    {u : ℕ} (hu : 1 ≤ u) (hpu : p ≤ u) :
    ‖pairedEtaMoebiusPrimeProductFirstMean rho p (u ^ 4) (u ^ 3)‖ ≤
      pairedEtaMoebiusFirstMeanConstant rho * p * (u : ℝ) ^ (2 - 4 * rho.1.re) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hb := norm_pairedEtaMoebiusPrimeProductFirstMean_le rho hp hodd
    (A := u ^ 4) (D := u ^ 3) (Nat.one_le_pow _ _ hu)
    (by nlinarith [Nat.mul_le_mul_right (u ^ 3) hpu])
  apply hb.trans_eq
  simp only [Nat.cast_pow]
  rw [← Real.rpow_natCast_mul huR.le, ← pow_mul,
    ← Real.rpow_natCast (u : ℝ) (3 * 2), mul_assoc, ← Real.rpow_add huR]
  congr 2
  norm_num
  ring

/-- The finite family of odd prime product classes through a stated cutoff. -/
def pairedEtaMoebiusOddPrimeMeanFamily (R : ℕ) : Finset ℕ :=
  (Finset.Icc 1 R).filter (fun p ↦ p.Prime ∧ Odd p)

/-- The sum of the norms of every prime-class mean has a quadratic cutoff allowance, before choosing any weights. -/
theorem sum_norm_pairedEtaMoebiusPrimeProductFirstMean_quartic_le
    (rho : NontrivialZetaZero) {u R : ℕ} (hu : 1 ≤ u) (hRu : R ≤ u) :
    (∑ p ∈ pairedEtaMoebiusOddPrimeMeanFamily R,
      ‖pairedEtaMoebiusPrimeProductFirstMean rho p (u ^ 4) (u ^ 3)‖) ≤
        pairedEtaMoebiusFirstMeanConstant rho * (R : ℝ) ^ 2 *
          (u : ℝ) ^ (2 - 4 * rho.1.re) := by
  have hC := pairedEtaMoebiusFirstMeanConstant_nonneg rho
  have hcard : ((pairedEtaMoebiusOddPrimeMeanFamily R).card : ℝ) ≤ R := by
    exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ (Finset.Icc 1 R))).trans_eq
      (by simp)
  calc
    _ ≤ ∑ _p ∈ pairedEtaMoebiusOddPrimeMeanFamily R,
        pairedEtaMoebiusFirstMeanConstant rho * R * (u : ℝ) ^ (2 - 4 * rho.1.re) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hpR, hprime, hodd⟩ := Finset.mem_filter.mp hp
      have hpR' := (Finset.mem_Icc.mp hpR).2
      apply (norm_pairedEtaMoebiusPrimeProductFirstMean_quartic_le rho hprime hodd hu
        (hpR'.trans hRu)).trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hpR') hC) (by positivity)
    _ ≤ (R : ℝ) * (pairedEtaMoebiusFirstMeanConstant rho * R *
        (u : ℝ) ^ (2 - 4 * rho.1.re)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

/-- A polynomially growing prime cutoff whose entire family has vanishing total first-mean norm to the right of one half. -/
def pairedEtaMoebiusPrimeMeanCutoff (rho : NontrivialZetaZero) (u : ℕ) : ℕ :=
  ⌊(u : ℝ) ^ (rho.1.re - 1 / 2)⌋₊

/-- The simultaneously controlled prime cutoff grows without bound at a hypothetical right-half zero. -/
theorem pairedEtaMoebiusPrimeMeanCutoff_tendsto_atTop
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    Tendsto (pairedEtaMoebiusPrimeMeanCutoff rho) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop (sub_pos.mpr hrho)).comp (tendsto_natCast_atTop_atTop (R := ℝ)))

/-- Simultaneous cancellation of all odd prime classes through the polynomial cutoff has an explicit negative-power allowance. -/
theorem sum_norm_pairedEtaMoebiusPrimeProductFirstMean_growing_le
    (rho : NontrivialZetaZero) {u : ℕ} (hu : 1 ≤ u) :
    (∑ p ∈ pairedEtaMoebiusOddPrimeMeanFamily (pairedEtaMoebiusPrimeMeanCutoff rho u),
      ‖pairedEtaMoebiusPrimeProductFirstMean rho p (u ^ 4) (u ^ 3)‖) ≤
        pairedEtaMoebiusFirstMeanConstant rho * (u : ℝ) ^ (1 - 2 * rho.1.re) := by
  have huR : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hup : (0 : ℝ) < u := by linarith
  have hC := pairedEtaMoebiusFirstMeanConstant_nonneg rho
  have hcut : (pairedEtaMoebiusPrimeMeanCutoff rho u : ℝ) ≤
      (u : ℝ) ^ (rho.1.re - 1 / 2) := Nat.floor_le (Real.rpow_nonneg hup.le _)
  have hRu : pairedEtaMoebiusPrimeMeanCutoff rho u ≤ u := by
    exact_mod_cast hcut.trans (Real.rpow_le_self_of_one_le huR
      (by linarith [NontrivialZetaZero.re_lt_one rho]))
  apply (sum_norm_pairedEtaMoebiusPrimeProductFirstMean_quartic_le rho hu hRu).trans
  calc
    _ ≤ pairedEtaMoebiusFirstMeanConstant rho *
        ((u : ℝ) ^ (rho.1.re - 1 / 2)) ^ 2 * (u : ℝ) ^ (2 - 4 * rho.1.re) := by
      gcongr
    _ = _ := by
      rw [← Real.rpow_mul_natCast hup.le, mul_assoc, ← Real.rpow_add hup]
      congr 2
      norm_num
      ring

/-- The sum of all prime-class mean norms vanishes simultaneously, without requiring a common prime-divisible scale. -/
theorem sum_norm_pairedEtaMoebiusPrimeProductFirstMean_growing_tendsto_zero
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    Tendsto (fun u : ℕ ↦
      ∑ p ∈ pairedEtaMoebiusOddPrimeMeanFamily (pairedEtaMoebiusPrimeMeanCutoff rho u),
        ‖pairedEtaMoebiusPrimeProductFirstMean rho p (u ^ 4) (u ^ 3)‖) atTop (𝓝 0) := by
  have hp : Tendsto (fun u : ℕ ↦ (u : ℝ) ^ (1 - 2 * rho.1.re)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (by linarith : 0 < 2 * rho.1.re - 1)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)) using 1
    ext u
    simp only [Function.comp_apply]
    congr 1
    ring
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _))
    ((eventually_ge_atTop 1).mono fun _ hu ↦
      sum_norm_pairedEtaMoebiusPrimeProductFirstMean_growing_le rho hu)
  simpa only [mul_zero] using hp.const_mul (pairedEtaMoebiusFirstMeanConstant rho)

/-- The exact additive weight of every selected odd prime dividing a product; intersections retain their multiplicity and complex weights. -/
def pairedEtaMoebiusPrimeProductWeight (R : ℕ) (w : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ p ∈ (pairedEtaMoebiusOddPrimeMeanFamily R).filter (fun p ↦ p ∣ n), w p

/-- The full complex combination of the original prime-class first means. -/
def pairedEtaMoebiusWeightedPrimeFirstMean
    (rho : NontrivialZetaZero) (R A D : ℕ) (w : ℕ → ℂ) : ℂ :=
  ∑ p ∈ pairedEtaMoebiusOddPrimeMeanFamily R,
    w p * pairedEtaMoebiusPrimeProductFirstMean rho p A D

private theorem weighted_prime_aggregate_eq_products
    (rho : NontrivialZetaZero) (R D M : ℕ) (w : ℕ → ℂ) :
    (∑ p ∈ pairedEtaMoebiusOddPrimeMeanFamily R,
      w p * pairedEtaCompletedMoebiusPrimeProductAggregate rho p D M) =
        pairedEtaXiCompletionFactor rho.1 * ∑ n ∈ Finset.Icc 1 M,
          (pairedEtaMoebiusHighProductCoefficient D n : ℂ) * (n : ℂ) ^ (-rho.1) *
            pairedEtaMoebiusPrimeProductWeight R w n := by
  simp only [pairedEtaCompletedMoebiusPrimeProductAggregate, Finset.sum_filter,
    Finset.mul_sum, pairedEtaMoebiusPrimeProductWeight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> ring

/-- Weighted prime means are the literal product sum over every original physical endpoint, with all overlap weights retained. -/
theorem pairedEtaMoebiusWeightedPrimeFirstMean_eq_products
    (rho : NontrivialZetaZero) (R A D : ℕ) (w : ℕ → ℂ) :
    pairedEtaMoebiusWeightedPrimeFirstMean rho R A D w =
      (∑ t ∈ Finset.range A, pairedEtaXiCompletionFactor rho.1 *
        ∑ n ∈ Finset.Icc 1 (A + t),
          (pairedEtaMoebiusHighProductCoefficient D n : ℂ) * (n : ℂ) ^ (-rho.1) *
            pairedEtaMoebiusPrimeProductWeight R w n) / A := by
  simp_rw [← weighted_prime_aggregate_eq_products]
  rw [Finset.sum_comm, Finset.sum_div]
  unfold pairedEtaMoebiusWeightedPrimeFirstMean pairedEtaMoebiusPrimeProductFirstMean
  apply Finset.sum_congr rfl
  intro p _
  rw [← Finset.mul_sum, mul_div_assoc]

/-- Removing a weighted prime combination gives the exact residual multiplier `1-sum_(p|n) w(p)`, rather than an indicator of a prime-free union. -/
theorem pairedEtaCompletedMoebiusLargeFirstMean_sub_weightedPrime_eq_products
    (rho : NontrivialZetaZero) (R A D : ℕ) (w : ℕ → ℂ) :
    pairedEtaCompletedMoebiusLargeFirstMean rho A D -
        pairedEtaMoebiusWeightedPrimeFirstMean rho R A D w =
      (∑ t ∈ Finset.range A, pairedEtaXiCompletionFactor rho.1 *
        ∑ n ∈ Finset.Icc 1 (A + t),
          (pairedEtaMoebiusHighProductCoefficient D n : ℂ) * (n : ℂ) ^ (-rho.1) *
            (1 - pairedEtaMoebiusPrimeProductWeight R w n)) / A := by
  rw [pairedEtaMoebiusWeightedPrimeFirstMean_eq_products,
    pairedEtaCompletedMoebiusLargeFirstMean, ← sub_div, ← Finset.sum_sub_distrib]
  apply congrArg (fun z : ℂ ↦ z / A)
  apply Finset.sum_congr rfl
  intro t _
  rw [pairedEtaCompletedMoebiusLargeAggregate_eq_product_prefix,
    pairedEtaMoebiusHighProductPrefix, ← mul_sub, ← Finset.sum_sub_distrib]
  apply congrArg (fun z : ℂ ↦ pairedEtaXiCompletionFactor rho.1 * z)
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- Any bounded complex weighting of the whole polynomial prime family has the same vanishing allowance, uniformly over the choice of weights. -/
theorem norm_pairedEtaMoebiusWeightedPrimeFirstMean_growing_le
    (rho : NontrivialZetaZero) {u : ℕ} (hu : 1 ≤ u) (w : ℕ → ℂ)
    (hw : ∀ p ∈ pairedEtaMoebiusOddPrimeMeanFamily (pairedEtaMoebiusPrimeMeanCutoff rho u),
      ‖w p‖ ≤ 1) :
    ‖pairedEtaMoebiusWeightedPrimeFirstMean rho (pairedEtaMoebiusPrimeMeanCutoff rho u)
      (u ^ 4) (u ^ 3) w‖ ≤
        pairedEtaMoebiusFirstMeanConstant rho * (u : ℝ) ^ (1 - 2 * rho.1.re) := by
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum fun p hp ↦ ?_).trans
    (sum_norm_pairedEtaMoebiusPrimeProductFirstMean_growing_le rho hu)
  rw [norm_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hw p hp) (norm_nonneg _)

/-- Prime weights may vary at every physical scale; their entire weighted first mean still tends to zero under the uniform unit bound. -/
theorem pairedEtaMoebiusWeightedPrimeFirstMean_growing_tendsto_zero
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) (w : ℕ → ℕ → ℂ)
    (hw : ∀ u p, p ∈ pairedEtaMoebiusOddPrimeMeanFamily (pairedEtaMoebiusPrimeMeanCutoff rho u) →
      ‖w u p‖ ≤ 1) :
    Tendsto (fun u : ℕ ↦ pairedEtaMoebiusWeightedPrimeFirstMean rho
      (pairedEtaMoebiusPrimeMeanCutoff rho u) (u ^ 4) (u ^ 3) (w u)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ ↦ norm_nonneg _) _
    (sum_norm_pairedEtaMoebiusPrimeProductFirstMean_growing_tendsto_zero rho hrho)
  intro u
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  rw [norm_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hw u p hp) (norm_nonneg _)

/-- Subtracting any such simultaneous weighted prime family retains the original nonzero source limit; estimating the resulting signed multiplier remains a separate arithmetic task. -/
theorem pairedEtaCompletedMoebiusLargeFirstMean_sub_weightedPrime_growing_tendsto_source
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) (w : ℕ → ℕ → ℂ)
    (hw : ∀ u p, p ∈ pairedEtaMoebiusOddPrimeMeanFamily (pairedEtaMoebiusPrimeMeanCutoff rho u) →
      ‖w u p‖ ≤ 1) :
    Tendsto (fun u : ℕ ↦ pairedEtaCompletedMoebiusLargeFirstMean rho (u ^ 4) (u ^ 3) -
      pairedEtaMoebiusWeightedPrimeFirstMean rho (pairedEtaMoebiusPrimeMeanCutoff rho u)
        (u ^ 4) (u ^ 3) (w u)) atTop (𝓝 (pairedEtaCompletedMoebiusSource rho)) := by
  simpa only [sub_zero] using
    (pairedEtaCompletedMoebiusLargeFirstMean_quartic_tendsto_source rho hrho).sub
      (pairedEtaMoebiusWeightedPrimeFirstMean_growing_tendsto_zero rho hrho w hw)

end

end RiemannGaussian
