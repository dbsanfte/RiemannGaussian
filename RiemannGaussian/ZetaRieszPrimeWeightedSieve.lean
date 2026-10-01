/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszLowerRadialPayment
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Keeping the prime weights in the canonical-pair sieve cost

The forbidden-prime mask is literal. Its finite comparison factor is
`prod (1+p^(-sigma)+p^(-2*sigma))`, not three per small prime. At exponent
17/32 this costs only `exp(O(N^(31/32)))` for primes up to `N^2`.
The signed density main is not estimated here.
-/

noncomputable section
open Filter Topology Real
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszPrimeWeightedSieve
open ZetaRieszUnsignedDivisorError ZetaRieszRoughCutoffRows

/-- The exact finite intersection factor in the squarefree comparison. -/
def sieveCost (σ : ℝ) (S : Finset ℕ) : ℝ :=
  ∏ p ∈ S, (1+primeSquareCorrectedWeight σ p)

/-- Every literal prime-intersection factor is nonnegative. -/
theorem sieveCost_nonneg (σ : ℝ) (S : Finset ℕ) : 0 ≤ sieveCost σ S := by
  unfold sieveCost
  exact Finset.prod_nonneg (fun p _ => by
    linarith [primeSquareCorrectedWeight_nonneg σ p])

/-- A summable positive mass absorbs the weighted prime prefix. -/
def prefixMass : ℝ := ZetaRieszPrimeCountMass.countMass (65/64)

/-- Cost of all canonical-pair exclusions up to the physical smooth threshold. -/
def polynomialCost (N : ℕ) : ℝ :=
  exp (2*prefixMass*(N : ℝ)^(31/32 : ℝ))

theorem polynomialCost_pos (N : ℕ) : 0 < polynomialCost N := exp_pos _

theorem small_weight_bound {N p : ℕ} (hN : 0 < N) (hp : 0 < p)
    (hle : p ≤ N^2) :
    zetaPrimeExpWeight (17/32) p ≤
      (N : ℝ)^(31/32 : ℝ)*zetaPrimeExpWeight (65/64) p := by
  have hn : (0 : ℝ)<N := by exact_mod_cast hN
  have hpp : (0 : ℝ)<p := by exact_mod_cast hp
  have hl : log p ≤ 2*log N := by
    have h := log_le_log hpp (show (p : ℝ)≤(N : ℝ)^2 by exact_mod_cast hle)
    simpa only [log_pow,Nat.cast_ofNat] using h
  rw [zetaPrimeExpWeight,zetaPrimeExpWeight,rpow_def_of_pos hn,← exp_add]
  apply exp_le_exp.mpr
  nlinarith

theorem sieveCost_small_primes_bound {N : ℕ} (hN : 0 < N) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N^2) :
    sieveCost (17/32) S ≤ polynomialCost N := by
  have hw p (hp : p ∈ S) : primeSquareCorrectedWeight (17/32) p ≤
      2*(N : ℝ)^(31/32 : ℝ)*zetaPrimeExpWeight (65/64) p := by
    have ht : 0 ≤ zetaPrimeExpWeight (17/32) p := (exp_pos _).le
    have hu : zetaPrimeExpWeight (17/32) p ≤ 1 := by
      rw [zetaPrimeExpWeight,exp_le_one_iff]
      nlinarith [log_natCast_nonneg p]
    have hh := small_weight_bound hN (hS p hp).1.pos (hS p hp).2
    unfold primeSquareCorrectedWeight
    nlinarith [mul_le_mul_of_nonneg_left hu ht]
  have hmass : (∑ p ∈ S, zetaPrimeExpWeight (65/64) p) ≤ prefixMass := by
    exact (summable_zetaPrimeExpWeight (by norm_num : (1 : ℝ)<65/64)).sum_le_tsum S
      (fun _ _ => (exp_pos _).le)
  calc
    _ ≤ exp (∑ p ∈ S, primeSquareCorrectedWeight (17/32) p) :=
      Real.prod_one_add_le_exp_sum S (fun p => primeSquareCorrectedWeight_nonneg _ p)
    _ ≤ exp (2*(N : ℝ)^(31/32 : ℝ)*∑ p ∈ S, zetaPrimeExpWeight (65/64) p) := by
      apply exp_le_exp.mpr
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hw
    _ ≤ _ := by
      apply exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left hmass
        (by positivity : (0 : ℝ)≤2*(N : ℝ)^(31/32 : ℝ))
      exact h.trans_eq (by ring)

theorem sieveCost_union_le (σ : ℝ) (S T : Finset ℕ) :
    sieveCost σ (S ∪ T) ≤ sieveCost σ S*sieveCost σ T := by
  have hi : 1 ≤ sieveCost σ (S ∩ T) :=
    Finset.one_le_prod (fun p _ => by linarith [primeSquareCorrectedWeight_nonneg σ p])
  have hu : 0 ≤ sieveCost σ (S ∪ T) := by
    unfold sieveCost
    exact Finset.prod_nonneg (fun p _ => by linarith [primeSquareCorrectedWeight_nonneg σ p])
  have he : sieveCost σ (S ∪ T)*sieveCost σ (S ∩ T)=sieveCost σ S*sieveCost σ T := by
    exact Finset.prod_union_inter
  exact (le_mul_of_one_le_right hu hi).trans_eq he

theorem sieveCost_le_three_pow {σ : ℝ} (hσ : 0 ≤ σ) (S : Finset ℕ) :
    sieveCost σ S ≤ (3 : ℝ)^S.card := by
  calc
    _ ≤ ∏ _p ∈ S, (3 : ℝ) := by
      apply Finset.prod_le_prod
      · intro p _
        linarith [primeSquareCorrectedWeight_nonneg σ p]
      · intro p _
        have ht : 0 ≤ zetaPrimeExpWeight σ p := (exp_pos _).le
        have hu : zetaPrimeExpWeight σ p ≤ 1 := by
          rw [zetaPrimeExpWeight,exp_le_one_iff]
          nlinarith [log_natCast_nonneg p]
        unfold primeSquareCorrectedWeight
        nlinarith [mul_le_mul_of_nonneg_left hu ht]
    _ = _ := by simp

/-- All original outer coprimality primes and every small-prime
exclusion remain in the actual forbidden set. Only their error cost changes. -/
theorem forbidden_cost_bound {N p b : ℕ} (hN : 0 < N)
    (hsmall : secondPrime b ≤ N^2) :
    sieveCost (17/32) (forbidden p b) ≤
      (3 : ℝ)^(p*b).primeFactors.card*polynomialCost N := by
  apply (sieveCost_union_le _ _ _).trans
  exact mul_le_mul (sieveCost_le_three_pow (by norm_num) _)
    (sieveCost_small_primes_bound hN (smallPrimes b) (fun q hq =>
      ⟨(Finset.mem_filter.mp hq).2,((Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).2).trans hsmall⟩))
    (by unfold sieveCost; exact Finset.prod_nonneg (fun q _ => by
      linarith [primeSquareCorrectedWeight_nonneg (17/32) q])) (by positivity)

/-- The exact product factor can be kept in the existing weighted
squarefree-error theorem, before any variation is bounded. -/
theorem weighted_error_exponential_product (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {σ : ℝ} (hσ : 1/2 < σ) (hσ1 : σ ≤ 1)
    (X N : ℕ) (w : ℕ → ℝ) (β : ℝ) (hend : w (X+1)=0)
    (hlower : ∀ k ∈ Finset.Icc 1 X, w k ≠ w (k+1) → exp (β*N) ≤ k) :
    |(∑ d ∈ Finset.Icc 1 X, w d*sieve S d)-
      density S*(∑ d ∈ Finset.Icc 1 X, w d)| ≤
        countingCostAt σ*sieveCost σ S*exp (-((1-σ)*β*N))*
          (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|w k-w (k+1)|) := by
  have hc k : (∑ d ∈ Finset.Icc 1 k, (sieve S d-density S)) =
      (∑ d ∈ Finset.Icc 1 k, sieve S d)-density S*k := by
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Nat.card_Icc,
      Nat.add_sub_cancel,nsmul_eq_mul,mul_comm]
  have he : (∑ d ∈ Finset.Icc 1 X, w d*sieve S d)-
      density S*(∑ d ∈ Finset.Icc 1 X, w d) =
        ∑ k ∈ Finset.Icc 1 X, (w k-w (k+1))*
          ((∑ d ∈ Finset.Icc 1 k, sieve S d)-density S*k) := by
    simp_rw [← hc]
    rw [← ZetaRieszSignedCutoffEnergy.abel_profile X w _ hend]
    simp only [mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [he,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  by_cases hz : w k=w (k+1)
  · simp [hz]
  have hk0 : (0 : ℝ)<k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
  have hl : β*N ≤ log k := by
    simpa only [log_exp] using log_le_log (exp_pos _) (hlower k hk hz)
  have hh : (k : ℝ)^σ ≤ exp (-((1-σ)*β*N))*k := by
    conv_rhs => rw [← exp_log hk0]
    rw [rpow_def_of_pos hk0,← exp_add]
    apply exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hl (by linarith : 0 ≤ 1-σ)]
  rw [abs_mul]
  have hpref : |(∑ d ∈ Finset.Icc 1 k, sieve S d)-density S*k| ≤
      countingCostAt σ*sieveCost σ S*(k : ℝ)^σ :=
    (prefix_error_product_at S hS hσ hσ1 k).trans_eq (by unfold sieveCost; ring)
  have hC : 0 ≤ countingCostAt σ*sieveCost σ S := by
    apply mul_nonneg (countingCostAt_pos σ).le
    unfold sieveCost
    exact Finset.prod_nonneg (fun p _ => by linarith [primeSquareCorrectedWeight_nonneg σ p])
  calc
    _ ≤ |w k-w (k+1)| * (countingCostAt σ*sieveCost σ S*(k : ℝ)^σ) :=
      mul_le_mul_of_nonneg_left hpref (abs_nonneg _)
    _ ≤ |w k-w (k+1)| * (countingCostAt σ*sieveCost σ S*
        (exp (-((1-σ)*β*N))*k)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh hC) (abs_nonneg _)
    _ = _ := by ring

/-- The full polynomial roughness cost is absorbed into the already
proved strict comparison rate. No finite starting order is inferred. -/
theorem eventually_polynomial_cost_geometric :
    ∀ᶠ N : ℕ in atTop,
      ZetaRieszFineDivisorRows.comparisonRate^N*polynomialCost N ≤
        (exp (-(1/20000 : ℝ)))^N := by
  have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<1/32)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hm := ht.const_mul (2*prefixMass)
  simp only [mul_zero] at hm
  filter_upwards [hm.eventually_lt_const (by norm_num : (0 : ℝ)<1/20000),
    eventually_ge_atTop (1 : ℕ)] with N h hN
  simp only [Function.comp_apply] at h
  have hn : (0 : ℝ)<N := by exact_mod_cast hN
  have hpow : (N : ℝ)^(31/32 : ℝ)=(N : ℝ)^(-(1/32 : ℝ))*(N : ℝ) := by
    calc
      _ = (N : ℝ)^(-(1/32 : ℝ)+1) := by norm_num
      _ = (N : ℝ)^(-(1/32 : ℝ))*(N : ℝ)^1 := rpow_add hn _ _
      _ = _ := by rw [rpow_one]
  have hs : 2*prefixMass*(N : ℝ)^(31/32 : ℝ) ≤ (N : ℝ)/20000 := by
    rw [hpow]
    have hh := mul_le_mul_of_nonneg_right h.le hn.le
    nlinarith only [hh]
  unfold ZetaRieszFineDivisorRows.comparisonRate polynomialCost
  rw [← exp_nat_mul,← exp_add,← exp_nat_mul]
  exact exp_le_exp.mpr (by linarith)

end RiemannGaussian.ZetaRieszPrimeWeightedSieve
