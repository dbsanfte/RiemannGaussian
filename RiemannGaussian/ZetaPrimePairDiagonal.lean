/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeQuadraticArithmetic

/-!
# Removing pairs supported on a single prime base

The prime-power restriction of the ordered von-Mangoldt convolution is
bounded by the logarithm times the proper-prime-power coefficient.
Its Dirichlet series is therefore analytic for real part greater than
one half. This identifies a further part of the complete quadratic
whose moments cannot carry an off-line-zero source.
-/

open Complex Filter Metric Set Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The ordered pair coefficient restricted to one prime base.
When a product is a prime power, both nonzero von-Mangoldt factors
are powers of that same prime. -/
def zetaPrimeDiagonalCoefficient (n : ℕ) : ℝ :=
  if IsPrimePow n then zetaPrimePairArithmetic n else 0

/-- The exact contribution from products with distinct prime bases. -/
def zetaDistinctPrimePairCoefficient (n : ℕ) : ℝ :=
  if IsPrimePow n then 0 else zetaPrimePairArithmetic n

/-- The prime-power restriction and its complement retain the whole
ordered pair coefficient without changing either contribution. -/
theorem zetaPrimePairCoefficient_split (n : ℕ) :
    zetaPrimePairArithmetic n = zetaPrimeDiagonalCoefficient n + zetaDistinctPrimePairCoefficient n := by
  by_cases hn : IsPrimePow n <;>
    simp [zetaPrimeDiagonalCoefficient, zetaDistinctPrimePairCoefficient, hn]

/-- The single-prime contribution is nonnegative. -/
theorem zetaPrimeDiagonalCoefficient_nonneg (n : ℕ) : 0 ≤ zetaPrimeDiagonalCoefficient n := by
  by_cases hn : IsPrimePow n <;>
    simp [zetaPrimeDiagonalCoefficient, hn, zetaPrimePairArithmetic_nonneg]

/-- The distinct-prime contribution is also nonnegative before filtering. -/
theorem zetaDistinctPrimePairCoefficient_nonneg (n : ℕ) : 0 ≤ zetaDistinctPrimePairCoefficient n := by
  by_cases hn : IsPrimePow n <;>
    simp [zetaDistinctPrimePairCoefficient, hn, zetaPrimePairArithmetic_nonneg]

/-- No ordered pair of nontrivial prime powers has prime product. -/
theorem zetaPrimePairArithmetic_prime {p : ℕ} (hp : p.Prime) : zetaPrimePairArithmetic p = 0 := by
  rw [zetaPrimePairArithmetic, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b ↦ ArithmeticFunction.vonMangoldt a * ArithmeticFunction.vonMangoldt b),
    hp.divisors]
  simp [Nat.div_self hp.pos]

/-- A nonzero surviving coefficient is supported on a product of
powers of exactly two distinct prime bases, with positive exponents. -/
theorem zetaDistinctPrimePairCoefficient_support (n : ℕ)
    (hn : zetaDistinctPrimePairCoefficient n ≠ 0) :
    ∃ p q a b : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ 0 < a ∧ 0 < b ∧ p ^ a * q ^ b = n := by
  have hnp : ¬ IsPrimePow n := by
    intro h
    simp [zetaDistinctPrimePairCoefficient, h] at hn
  have hc : zetaPrimePairArithmetic n ≠ 0 := by
    simpa [zetaDistinctPrimePairCoefficient, hnp] using hn
  rw [zetaPrimePairArithmetic, ArithmeticFunction.mul_apply] at hc
  obtain ⟨⟨u, v⟩, huv, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  have hu : IsPrimePow u := by
    by_contra h
    exact (mul_ne_zero_iff.mp hc).1 (ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr h)
  have hv : IsPrimePow v := by
    by_contra h
    exact (mul_ne_zero_iff.mp hc).2 (ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr h)
  obtain ⟨p, a, hp, ha, rfl⟩ := (isPrimePow_nat_iff u).mp hu
  obtain ⟨q, b, hq, hb, rfl⟩ := (isPrimePow_nat_iff v).mp hv
  have he : p ^ a * q ^ b = n := (Nat.mem_divisorsAntidiagonal.mp huv).1
  refine ⟨p, q, a, b, hp, hq, ?_, ha, hb, he⟩
  intro hpq
  subst q
  exact hnp ((isPrimePow_nat_iff n).mpr ⟨p, a + b, hp, by omega, by rw [pow_add]; exact he⟩)

private theorem vonMangoldt_divisor_prime_pow_le {p k d : ℕ} (hp : p.Prime)
    (hd : d ∣ p ^ k) : ArithmeticFunction.vonMangoldt d ≤ Real.log p := by
  obtain ⟨j, _, rfl⟩ := (Nat.dvd_prime_pow hp).mp hd
  by_cases hj : j = 0
  · simp [hj, Real.log_natCast_nonneg]
  · rw [ArithmeticFunction.vonMangoldt_apply_pow hj, ArithmeticFunction.vonMangoldt_apply_prime hp]

private theorem prime_pair_prime_pow_le {p k : ℕ} (hp : p.Prime) :
    zetaPrimePairArithmetic (p ^ k) ≤ Real.log (p ^ k : ℕ) * Real.log p := by
  rw [zetaPrimePairArithmetic, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b ↦ ArithmeticFunction.vonMangoldt a * ArithmeticFunction.vonMangoldt b)]
  calc
    _ ≤ ∑ d ∈ (p ^ k).divisors, ArithmeticFunction.vonMangoldt d * Real.log p := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left
        (vonMangoldt_divisor_prime_pow_le hp (Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hd).1))
        ArithmeticFunction.vonMangoldt_nonneg
    _ = _ := by rw [← Finset.sum_mul, ArithmeticFunction.vonMangoldt_sum]

/-- The single-prime part is dominated by a logarithmic weight on
proper prime powers, whose convergence threshold is one half. -/
theorem zetaPrimeDiagonalCoefficient_le (n : ℕ) :
    zetaPrimeDiagonalCoefficient n ≤ Real.log n * zetaProperPrimePowerCoefficient n := by
  by_cases hn : IsPrimePow n
  · rw [zetaPrimeDiagonalCoefficient, if_pos hn]
    by_cases hnp : n.Prime
    · rw [zetaPrimePairArithmetic_prime hnp]
      exact mul_nonneg (Real.log_natCast_nonneg n) (zetaProperPrimePowerCoefficient_nonneg n)
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
    rw [zetaProperPrimePowerCoefficient, if_neg hnp, ArithmeticFunction.vonMangoldt_apply_pow hk.ne',
      ArithmeticFunction.vonMangoldt_apply_prime hp]
    exact prime_pair_prime_pow_le hp
  · rw [zetaPrimeDiagonalCoefficient, if_neg hn]
    exact mul_nonneg (Real.log_natCast_nonneg n) (zetaProperPrimePowerCoefficient_nonneg n)

/-- The single-prime pair series converges absolutely throughout
the larger half-plane, without an RH or zero-free premise. -/
theorem LSeriesSummable_zetaPrimeDiagonal {s : ℂ} (hs : 1 / 2 < s.re) :
    LSeriesSummable (fun n ↦ (zetaPrimeDiagonalCoefficient n : ℂ)) s := by
  have ha : LSeries.abscissaOfAbsConv (fun n ↦ (zetaProperPrimePowerCoefficient n : ℂ)) ≤ (1 / 2 : ℝ) := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro y hy
    exact LSeriesSummable_zetaProperPrimePower (by simpa using hy)
  have h : LSeriesSummable (LSeries.logMul (fun n ↦ (zetaProperPrimePowerCoefficient n : ℂ))) s :=
    LSeriesSummable_logMul_of_lt_re (lt_of_le_of_lt ha (by exact_mod_cast hs))
  apply Summable.of_norm_bounded h.norm
  intro n
  apply LSeries.norm_term_le
  simp only [LSeries.logMul, ← Complex.natCast_log, ← Complex.ofReal_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (zetaPrimeDiagonalCoefficient_nonneg n),
    abs_of_nonneg (mul_nonneg (Real.log_natCast_nonneg n) (zetaProperPrimePowerCoefficient_nonneg n))]
  exact zetaPrimeDiagonalCoefficient_le n

/-- The actual analytic response of the single-prime pair series. -/
def zetaPrimeDiagonalResponse (s : ℂ) : ℂ :=
  LSeries (fun n ↦ (zetaPrimeDiagonalCoefficient n : ℂ)) s

/-- The literal single-prime pair response is analytic throughout
real part greater than one half, including every selected right-half zero. -/
theorem analyticAt_zetaPrimeDiagonalResponse {s : ℂ} (hs : 1 / 2 < s.re) :
    AnalyticAt ℂ zetaPrimeDiagonalResponse s := by
  apply LSeries_analyticOnNhd
  have hb : LSeries.abscissaOfAbsConv (fun n ↦ (zetaPrimeDiagonalCoefficient n : ℂ)) ≤ (1 / 2 : ℝ) := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro y hy
    exact LSeriesSummable_zetaPrimeDiagonal (by simpa using hy)
  exact lt_of_le_of_lt hb (by exact_mod_cast hs)

/-- The single-prime moment uses exactly the same complete cofactor
as the surviving quadratic and the independently bounded mixed product. -/
def zetaPrimeDiagonalMoment (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  signedTaylorMoment N (fun z ↦ zetaPrimeQuadraticCofactor rho z * zetaPrimeDiagonalResponse z)
    (zetaWronskianMomentCenter rho)

private theorem diagonal_abscissa :
    LSeries.abscissaOfAbsConv (fun n ↦ (zetaPrimeDiagonalCoefficient n : ℂ)) ≤ (1 / 2 : ℝ) := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro y hy
  exact LSeriesSummable_zetaPrimeDiagonal (by simpa using hy)

/-- The diagonal moment is the genuinely convergent restriction of
the full prime-pair arithmetic sum, with no change to its complex kernel. -/
theorem hasSum_zetaPrimeDiagonalMoment (rho : NontrivialZetaZero) (N : ℕ) :
    HasSum (fun n ↦ (zetaPrimeDiagonalCoefficient n : ℂ) * zetaPrimeQuadraticKernel rho N n)
      (zetaPrimeDiagonalMoment rho N) := by
  have hs : (1 / 2 : ℝ) < (zetaWronskianMomentCenter rho).re := by norm_num [zetaWronskianMomentCenter]
  have h := hasSum_signedTaylorMoment_mul_LSeries (fun n ↦ (zetaPrimeDiagonalCoefficient n : ℂ))
    (by simp [zetaPrimeDiagonalCoefficient]) (analyticAt_zetaPrimeQuadraticCofactor rho _)
    (lt_of_le_of_lt diagonal_abscissa (by exact_mod_cast hs)) N
  simpa only [zetaPrimeQuadraticKernel, zetaPrimeDiagonalMoment, zetaPrimeDiagonalResponse,
    mul_assoc] using h

private theorem domain_re_gt_half (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    {s : ℂ} (hs : s ∈ zetaWronskianMomentDomain rho) : 1 / 2 < s.re := by
  have hn : ‖s - zetaWronskianMomentCenter rho‖ ≤ zetaWronskianMomentRadius rho := by
    simpa [zetaWronskianMomentDomain, mem_closedBall, dist_eq_norm] using hs
  have hr := (abs_le.mp ((Complex.abs_re_le_norm (s - zetaWronskianMomentCenter rho)).trans hn)).1
  have hc : (zetaWronskianMomentCenter rho).re = 3 / 2 := by simp [zetaWronskianMomentCenter]
  rw [Complex.sub_re, hc] at hr
  have hR := (zetaWronskianMomentRadius_spec rho hrho).2.2
  linarith

/-- The whole diagonal contribution, including every cofactor
derivative, is geometrically negligible at the selected zero's scale. -/
theorem exists_zetaPrimeDiagonalMoment_geometric_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C q : ℝ, 0 < C ∧ 0 < q ∧ q < 1 ∧ ∀ N : ℕ,
      ‖(zetaWronskianMomentCenter rho - rho.1) ^ (N + 2) * zetaPrimeDiagonalMoment rho N‖ ≤ C * q ^ N := by
  have hspec := zetaWronskianMomentRadius_spec rho hrho
  have hR : 0 < zetaWronskianMomentRadius rho := hspec.1.trans hspec.2.1
  let f : ℂ → ℂ := fun z ↦ zetaPrimeQuadraticCofactor rho z * zetaPrimeDiagonalResponse z
  have ha : AnalyticOnNhd ℂ f (zetaWronskianMomentDomain rho) :=
    fun s hs ↦ (analyticAt_zetaPrimeQuadraticCofactor rho s).mul
      (analyticAt_zetaPrimeDiagonalResponse (domain_re_gt_half rho hrho hs))
  obtain ⟨B, hb⟩ := ((isCompact_closedBall _ _).image_of_continuousOn ha.continuousOn).isBounded.exists_norm_le
  have hB : 0 ≤ B := (norm_nonneg _).trans
    (hb _ ⟨zetaWronskianMomentCenter rho, mem_closedBall_self hR.le, rfl⟩)
  have hd : DiffContOnCl ℂ f (ball (zetaWronskianMomentCenter rho) (zetaWronskianMomentRadius rho)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hR.ne']
    exact ha.differentiableOn
  have hbound (N : ℕ) : ‖zetaPrimeDiagonalMoment rho N‖ ≤ (B + 1) / zetaWronskianMomentRadius rho ^ N := by
    exact norm_signedTaylorMoment_le hR hd
      (fun z hz ↦ (hb _ ⟨z, sphere_subset_closedBall hz, rfl⟩).trans (by linarith)) N
  let q := ‖zetaWronskianMomentCenter rho - rho.1‖ / zetaWronskianMomentRadius rho
  refine ⟨‖zetaWronskianMomentCenter rho - rho.1‖ ^ 2 * (B + 1), q,
    mul_pos (pow_pos hspec.1 _) (by linarith), div_pos hspec.1 hR,
    (div_lt_one hR).mpr hspec.2.1, fun N ↦ ?_⟩
  rw [norm_mul, norm_pow]
  calc
    _ ≤ ‖zetaWronskianMomentCenter rho - rho.1‖ ^ (N + 2) *
        ((B + 1) / zetaWronskianMomentRadius rho ^ N) :=
      mul_le_mul_of_nonneg_left (hbound N) (pow_nonneg (norm_nonneg _) _)
    _ = _ := by rw [pow_add, div_pow]; ring

/-- The normalized same-prime sum vanishes. This estimate is
independent of the distinct-prime source and is stronger than needed
to remove this part from the quadratic obstruction. -/
theorem tendsto_zetaPrimeDiagonalMoment (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ ↦
      ((zetaWronskianMomentCenter rho - rho.1) ^ (N + 2) * zetaPrimeDiagonalMoment rho N) /
        ((N + 1 : ℕ) : ℂ)) atTop (𝓝 0) := by
  obtain ⟨C, q, _, hq0, hq1, hb⟩ := exists_zetaPrimeDiagonalMoment_geometric_bound rho hrho
  apply squeeze_zero_norm (fun N ↦ ?_) (by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).const_mul C)
  rw [norm_div, Complex.norm_natCast]
  exact (div_le_self (norm_nonneg _) (by exact_mod_cast (show 1 ≤ N + 1 by omega))).trans (hb N)

/-- The remaining arithmetic is still a genuine convergent sum:
it is the complete quadratic minus the independently negligible
same-prime part, with every phase unchanged. -/
theorem hasSum_zetaDistinctPrimePairMoment (rho : NontrivialZetaZero) (N : ℕ) :
    HasSum (fun n ↦ (zetaDistinctPrimePairCoefficient n : ℂ) * zetaPrimeQuadraticKernel rho N n)
      (zetaPrimeQuadraticMoment rho N - zetaPrimeDiagonalMoment rho N) := by
  have h := (hasSum_zetaPrimeQuadraticMoment rho N).sub (hasSum_zetaPrimeDiagonalMoment rho N)
  apply h.congr_fun
  intro n
  rw [zetaPrimePairCoefficient_split n]
  push_cast
  ring

/-- Every hypothetical right-half zero forces its entire nonzero
quadratic source into the distinct-prime sum. The same-prime and
whole mixed-product contributions have independent vanishing bounds. -/
theorem tendsto_zetaDistinctPrimePair_source (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ ↦ ((zetaWronskianMomentCenter rho - rho.1) ^ (N + 2) *
      (∑' n, (zetaDistinctPrimePairCoefficient n : ℂ) * zetaPrimeQuadraticKernel rho N n)) /
        ((N + 1 : ℕ) : ℂ)) atTop (𝓝 (zetaPrimeQuadraticSource rho)) := by
  simpa only [(hasSum_zetaDistinctPrimePairMoment _ _).tsum_eq, mul_sub, sub_div, sub_zero] using
    (tendsto_zetaPrimeQuadraticMoment rho hrho).sub (tendsto_zetaPrimeDiagonalMoment rho hrho)

end

end RiemannGaussian
