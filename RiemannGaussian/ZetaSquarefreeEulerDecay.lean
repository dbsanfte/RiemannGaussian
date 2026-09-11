/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaSquarefreeEulerMarks
import RiemannGaussian.ZetaCoprimeEulerPhase

/-!
# Uniform squarefree decay with moving arithmetic data

The complete squarefree Euler quotient has a Cauchy radius greater than
one. A squarefree divisibility mark has a uniformly bounded local Euler
cost, independently of its size and number of prime factors. Small-prime
exclusion has a separate cardinality cost. These estimates retain the
original arithmetic filters and do not remove their ordinary-prime terms.
-/

namespace RiemannGaussian
noncomputable section
open Complex Filter Topology
open scoped Classical

private theorem weight_lt_one {σ : ℝ} (hσ : 0 < σ) {a : ℕ} (ha : a.Prime) :
    zetaPrimeExpWeight σ a < 1 := by
  apply Real.exp_lt_one_iff.mpr
  have hlog : 0 < Real.log a := Real.log_pos (by exact_mod_cast ha.one_lt)
  nlinarith

private theorem weight_le_two {σ : ℝ} (hσ : 0 < σ) {a : ℕ} (ha : a.Prime) :
    zetaPrimeExpWeight σ a ≤ zetaPrimeExpWeight σ 2 := by
  apply Real.exp_le_exp.mpr
  have hlog : Real.log 2 ≤ Real.log a := Real.log_le_log (by norm_num)
    (by exact_mod_cast ha.two_le)
  norm_num only [Nat.cast_ofNat]
  nlinarith

private theorem weight_tendsto_zero {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (zetaPrimeExpWeight σ) atTop (𝓝 0) := by
  apply ((tendsto_rpow_neg_atTop hσ).comp (tendsto_natCast_atTop_atTop (R := ℝ))).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  dsimp only [Function.comp_apply]
  rw [Real.rpow_def_of_pos (by exact_mod_cast (show 0 < n by omega)), zetaPrimeExpWeight]
  congr 1
  ring

private theorem weight_prime_product {P : ℕ} (hP : Squarefree P) (σ : ℝ) :
    zetaPrimeExpWeight σ P = ∏ a ∈ P.primeFactors, zetaPrimeExpWeight σ a := by
  rw [zetaPrimeExpWeight, CoprimeEulerPhase.squarefree_log_eq_prime_sum hP,
    Finset.mul_sum, Real.exp_sum]
  rfl

/-- The full finite Euler allowance is uniform in every squarefree
divisibility mark. Only the number of excluded primes remains in the
exponential cost; their sizes and the mark size are unrestricted. -/
theorem exists_squarefreeEulerBudget_card_bound {σ : ℝ} (hσ : 0 < σ) :
    ∃ K : ℝ, 1 < K ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (S : Finset ℕ), (∀ a ∈ S, a.Prime) →
        ∀ (P : ℕ), Squarefree P → (∀ a ∈ P.primeFactors, a ∉ S) →
          squarefreeEulerBudget σ S P ≤ C * K ^ S.card := by
  let q := zetaPrimeExpWeight σ
  let K := (1 - q 2)⁻¹
  have hq (a : ℕ) : 0 < q a := Real.exp_pos _
  have hden : 0 < 1 - q 2 := sub_pos.mpr (weight_lt_one hσ Nat.prime_two)
  have hK : 1 < K := by
    dsimp only [K]
    rw [inv_eq_one_div]
    exact (lt_div_iff₀ hden).mpr (by linarith [hq 2])
  have hK0 : 0 < K := zero_lt_one.trans hK
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    ((weight_tendsto_zero hσ).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  have hinv {a : ℕ} (ha : a.Prime) : (1 - q a)⁻¹ ≤ K := by
    exact inv_anti₀ hden (by linarith [weight_le_two hσ ha])
  have hratio {a : ℕ} (ha : a.Prime) : q a * (1 - q a)⁻¹ ≤ K := by
    have hqa := weight_lt_one hσ ha
    have hi : 0 ≤ (1 - q a)⁻¹ := inv_nonneg.mpr (by linarith)
    exact (mul_le_of_le_one_left hi hqa.le).trans (hinv ha)
  have htail {a : ℕ} (ha : a.Prime) (haM : M ≤ a) : q a * (1 - q a)⁻¹ ≤ 1 := by
    have hqa := weight_lt_one hσ ha
    rw [← div_eq_mul_inv]
    apply (div_le_one (by linarith : 0 < 1 - q a)).mpr
    linarith [hM a haM]
  refine ⟨K, hK, K ^ M, by positivity, ?_⟩
  intro S hS P hP hPS
  have hdis : Disjoint S P.primeFactors := Finset.disjoint_left.mpr
    (fun a haS haP ↦ hPS a haP haS)
  have hlocal (a : ℕ) (ha : a ∈ P.primeFactors) : 0 ≤ q a * (1 - q a)⁻¹ := by
    have h := weight_lt_one hσ (Nat.prime_of_mem_primeFactors ha)
    exact mul_nonneg (hq a).le (inv_nonneg.mpr (by linarith))
  have hmark : (∏ a ∈ P.primeFactors, q a * (1 - q a)⁻¹) ≤ K ^ M := by
    calc
      _ ≤ ∏ a ∈ P.primeFactors, if a < M then K else 1 := by
        apply Finset.prod_le_prod hlocal
        intro a ha
        split_ifs with haM
        · exact hratio (Nat.prime_of_mem_primeFactors ha)
        · exact htail (Nat.prime_of_mem_primeFactors ha) (by omega)
      _ = K ^ (P.primeFactors.filter (fun a ↦ a < M)).card := by
        rw [Finset.prod_ite]
        simp
      _ ≤ K ^ M := by
        apply pow_le_pow_right₀ hK.le
        have hsub : P.primeFactors.filter (fun a ↦ a < M) ⊆ Finset.range M := by
          intro a ha
          exact Finset.mem_range.mpr (Finset.mem_filter.mp ha).2
        simpa using Finset.card_le_card hsub
  have hsieve : (∏ a ∈ S, (1 - q a)⁻¹) ≤ K ^ S.card := by
    calc
      _ ≤ ∏ _a ∈ S, K := Finset.prod_le_prod
        (fun a ha ↦ inv_nonneg.mpr (sub_nonneg.mpr (weight_lt_one hσ (hS a ha)).le))
        (fun a ha ↦ hinv (hS a ha))
      _ = _ := by simp
  have he : squarefreeEulerBudget σ S P =
      (∏ a ∈ S, (1 - q a)⁻¹) * (∏ a ∈ P.primeFactors, q a * (1 - q a)⁻¹) := by
    rw [squarefreeEulerBudget, weight_prime_product hP, Finset.prod_union hdis,
      Finset.prod_mul_distrib]
    ring
  rw [he]
  simpa only [mul_comm] using mul_le_mul hsieve hmark
    (Finset.prod_nonneg hlocal) (pow_nonneg hK0.le _)

/-- The actual arithmetic filter has one bound for every natural
divisibility mark, including the vanishing invalid marks. The common
geometric decay is independent of the mark and of the excluded primes. -/
theorem exists_squarefreeEuler_uniform_mark_filter_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ K : ℝ, 1 < K ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (S : Finset ℕ), (∀ a ∈ S, a.Prime) → ∀ (P : ℕ) (p : Polynomial ℂ) (N : ℕ),
        ‖RoughSquarefreeBare.response p S P N (3 / 2 + I * y)‖ ≤
          C * K ^ S.card * (squarefreeEulerRadius y)⁻¹ ^ N *
            ∑ k ∈ p.support, ‖p.coeff k‖ * (squarefreeEulerRadius y)⁻¹ ^ k := by
  have hσ : 0 < 3 / 2 - squarefreeEulerRadius y := by
    linarith [(squarefreeEulerRadius_bounds hy).2.2.1]
  obtain ⟨K, hK, A, hA, hbudget⟩ := exists_squarefreeEulerBudget_card_bound hσ
  obtain ⟨C, hC, hb⟩ := exists_markedSquarefreeEuler_filter_bound y hy
  refine ⟨K, hK, C * A, mul_pos hC hA, ?_⟩
  intro S hS P p N
  have hK0 : 0 < K := zero_lt_one.trans hK
  have hr : 0 < squarefreeEulerRadius y := zero_lt_one.trans (squarefreeEulerRadius_bounds hy).1
  have hn : 0 ≤ (C * A) * K ^ S.card * (squarefreeEulerRadius y)⁻¹ ^ N *
      ∑ k ∈ p.support, ‖p.coeff k‖ * (squarefreeEulerRadius y)⁻¹ ^ k := by positivity
  by_cases hgood : Squarefree P ∧ ∀ a ∈ P.primeFactors, a ∉ S
  · obtain ⟨hP, hPS⟩ := hgood
    apply (hb S hS P hP hPS p N).trans
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hbudget S hS P hP hPS) hC.le)
      (show 0 ≤ (squarefreeEulerRadius y)⁻¹ ^ N *
        ∑ k ∈ p.support, ‖p.coeff k‖ * (squarefreeEulerRadius y)⁻¹ ^ k by positivity)
    simpa only [mul_assoc] using h
  · have hz (n : ℕ) : RoughSquarefreeBare.coefficient S P n = 0 := by
      have h : ¬(Squarefree n ∧ (¬∃ a ∈ S, a ∣ n) ∧ P ∣ n) := by
        rintro ⟨hsf, hrough, hd⟩
        exact hgood ⟨hsf.squarefree_of_dvd hd, fun a ha haS ↦
          hrough ⟨a, haS, (Nat.dvd_of_mem_primeFactors ha).trans hd⟩⟩
      simp only [RoughSquarefreeBare.coefficient, if_neg h]
    simpa [RoughSquarefreeBare.response, hz] using hn

private theorem eventually_card_geometric_bound {K r : ℝ} (hK : 1 < K) (hr : 1 < r)
    (a : ℕ → ℕ) (ha : Tendsto (fun N ↦ (a N : ℝ) / N) atTop (𝓝 0)) :
    ∃ b : ℝ, 0 < b ∧ b < 1 ∧ ∀ᶠ N in atTop, K ^ a N * r⁻¹ ^ N ≤ b ^ N := by
  let b := Real.exp (-Real.log r / 2)
  have hlog : 0 < Real.log r := Real.log_pos hr
  have hb0 : 0 < b := Real.exp_pos _
  have hb1 : b < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hK0 : 0 < K := zero_lt_one.trans hK
  have hr0 : 0 < r := zero_lt_one.trans hr
  have he : ∀ᶠ N in atTop, (a N : ℝ) / N * Real.log K < Real.log r / 2 := by
    have hlim := ha.mul_const (Real.log K)
    simp only [zero_mul] at hlim
    exact hlim.eventually (gt_mem_nhds (by linarith))
  refine ⟨b, hb0, hb1, ?_⟩
  filter_upwards [he, eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hratio : (a N : ℝ) * Real.log K / N < Real.log r / 2 := by
    convert hN using 1
    ring
  have hmul := (div_lt_iff₀ hN0).mp hratio
  have hleft : K ^ a N * r⁻¹ ^ N =
      Real.exp ((a N : ℝ) * Real.log K + (N : ℝ) * Real.log r⁻¹) := by
    rw [Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
      Real.exp_log hK0, Real.exp_log (inv_pos.mpr hr0)]
  have hright : b ^ N = Real.exp ((N : ℝ) * (-Real.log r / 2)) := by
    rw [Real.exp_nat_mul]
  rw [hleft, hright]
  apply Real.exp_le_exp.mpr
  rw [Real.log_inv]
  nlinarith

/-- Every sublinear-cardinality prime sieve preserves geometric decay,
uniformly over all natural divisibility marks at every sufficiently large
moment. The primes themselves may vary arbitrarily with the moment. -/
theorem exists_squarefreeEuler_sublinear_sieve_bound (y : ℝ) (hy : 1 < |y|)
    (S : ℕ → Finset ℕ) (hS : ∀ N a, a ∈ S N → a.Prime)
    (hcard : Tendsto (fun N ↦ ((S N).card : ℝ) / N) atTop (𝓝 0)) :
    ∃ C b : ℝ, 0 < C ∧ 0 < b ∧ b < 1 ∧ ∀ᶠ N in atTop,
      ∀ (P : ℕ) (p : Polynomial ℂ),
        ‖RoughSquarefreeBare.response p (S N) P N (3 / 2 + I * y)‖ ≤
          C * b ^ N * ∑ k ∈ p.support, ‖p.coeff k‖ * (squarefreeEulerRadius y)⁻¹ ^ k := by
  obtain ⟨K, hK, C, hC, hb⟩ := exists_squarefreeEuler_uniform_mark_filter_bound y hy
  obtain ⟨b, hb0, hb1, he⟩ := eventually_card_geometric_bound hK
    (squarefreeEulerRadius_bounds hy).1 (fun N ↦ (S N).card) hcard
  refine ⟨C, b, hC, hb0, hb1, ?_⟩
  filter_upwards [he] with N hN P p
  apply (hb (S N) (hS N) P p N).trans
  have hr : 0 < squarefreeEulerRadius y := zero_lt_one.trans (squarefreeEulerRadius_bounds hy).1
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN hC.le)
    (show 0 ≤ ∑ k ∈ p.support, ‖p.coeff k‖ * (squarefreeEulerRadius y)⁻¹ ^ k by positivity)
  simpa only [mul_assoc] using h

/-- Actual unscaled arithmetic cancellation survives every sublinear
prime-sieve schedule and every moving divisibility mark, with no restriction
on the growth of the mark. The full ordinary-prime contribution is included. -/
theorem tendsto_squarefreeEuler_sublinear_sieve (y : ℝ) (hy : 1 < |y|)
    (S : ℕ → Finset ℕ) (hS : ∀ N a, a ∈ S N → a.Prime)
    (hcard : Tendsto (fun N ↦ ((S N).card : ℝ) / N) atTop (𝓝 0))
    (P : ℕ → ℕ) (p : Polynomial ℂ) :
    Tendsto (fun N ↦ RoughSquarefreeBare.response p (S N) (P N) N (3 / 2 + I * y))
      atTop (𝓝 0) := by
  obtain ⟨C, b, _, hb0, hb1, he⟩ := exists_squarefreeEuler_sublinear_sieve_bound y hy S hS hcard
  apply squeeze_zero_norm' (he.mono (fun N hN ↦ hN (P N) p))
  simpa only [mul_zero, zero_mul] using
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hb0.le hb1).const_mul C).mul_const
      (∑ k ∈ p.support, ‖p.coeff k‖ * (squarefreeEulerRadius y)⁻¹ ^ k)

end
end RiemannGaussian
