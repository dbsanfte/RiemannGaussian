/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointCofactor
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Exact majority allocations of the original factorial orders

The full multinomial expansion proves that the selected majority incidences use at most one original factorial amplitude. Every original unpaid order and prime divisor is retained.
-/

namespace RiemannGaussian.ZetaRieszJointAllocation
noncomputable section
open scoped BigOperators Classical

-- Exact allocation bookkeeping for the original unpaid complementary orders.
-- This is not yet the collapsed prime/cofactor kernel or a bound for F - T.
/-- A derivative allocation can give a strict majority to at most one distinguished factor. -/
theorem selected_card_le_one {ι : Type*} [DecidableEq ι] (S : Finset ι) (U : Finset ℕ) (M : ℕ)
    (hU : ∀ k ∈ U, 2 * k < M) {d : ι → ℕ}
    (hd : d ∈ Finset.piAntidiag S M) :
    (S.filter (fun p => M - d p ∈ U)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp q hq
  obtain ⟨hpS, hpU⟩ := Finset.mem_filter.mp hp
  obtain ⟨hqS, hqU⟩ := Finset.mem_filter.mp hq
  have hdM := (Finset.mem_piAntidiag.mp hd).1
  have hpM : d p ≤ M := by
    rw [← hdM]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hpS
  have hqM : d q ≤ M := by
    rw [← hdM]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hqS
  have hpu := hU _ hpU
  have hqu := hU _ hqU
  by_contra hpq
  have hsub : ({p, q} : Finset ι) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hpS
    · exact hqS
  have hsum : d p + d q ≤ M := by
    rw [← hdM]
    simpa only [Finset.sum_pair hpq] using
      (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
        : (∑ i ∈ ({p, q} : Finset ι), d i) ≤ ∑ i ∈ S, d i)
  omega

/-- The full multinomial weight of one derivative allocation. -/
def allocationWeight {ι : Type*} (S : Finset ι) (x : ι → ℝ) (d : ι → ℕ) : ℝ :=
  (Nat.multinomial S d : ℝ) * ∏ i ∈ S, (x i) ^ d i

/-- Disjoint majority allocations use at most the complete multinomial mass. -/
theorem selected_allocation_le {ι : Type*} [DecidableEq ι] (S : Finset ι) (x : ι → ℝ)
    (hx : ∀ p ∈ S, 0 ≤ x p) (U : Finset ℕ) (M : ℕ)
    (hU : ∀ k ∈ U, 2 * k < M) :
    (∑ p ∈ S, ∑ d ∈ (Finset.piAntidiag S M).filter (fun d => M - d p ∈ U),
      allocationWeight S x d) ≤ (∑ p ∈ S, x p) ^ M := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm, Finset.sum_pow_eq_sum_piAntidiag]
  apply Finset.sum_le_sum
  intro d hd
  have hw : 0 ≤ allocationWeight S x d :=
    mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun p hp => pow_nonneg (hx p hp) _))
  have hc := selected_card_le_one S U M hU hd
  have hcR : ((S.filter (fun p => M - d p ∈ U)).card : ℝ) ≤ 1 := by exact_mod_cast hc
  calc
    _ = ((S.filter (fun p => M - d p ∈ U)).card : ℝ) * allocationWeight S x d := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ allocationWeight S x d := by nlinarith
    _ = _ := rfl

/-- Every original unpaid cofactor order is below half the complete derivative order. -/
theorem unpaid_orders_submajority (N : ℕ) :
    ∀ k ∈ RiemannGaussian.ZetaRieszWingHighOrders.unpaidOrders N, 2 * k < N + 1 := by
  intro k hk
  have h := (RiemannGaussian.ZetaRieszWingHighOrders.unpaidOrders_support hk).2.1
  omega


-- Exact collapse at one distinguished prime. Positivity is not needed here.
/-- Exact binomial collapse of the full multinomial allocations at one distinguished factor. -/
theorem marked_allocation_cons {ι : Type*} [DecidableEq ι] (S : Finset ι) (p : ι) (hp : p ∉ S)
    (x : ι → ℝ) (M : ℕ) (E : ℕ → Prop) [DecidablePred E] :
    (∑ d ∈ Finset.piAntidiag (S.cons p hp) M,
      if E (d p) then allocationWeight (S.cons p hp) x d else 0) =
    ∑ b ∈ Finset.HasAntidiagonal.antidiagonal M,
      if E b.1 then (M.choose b.1 : ℝ) * x p ^ b.1 * (∑ q ∈ S, x q) ^ b.2 else 0 := by
  rw [Finset.piAntidiag_cons, Finset.sum_disjiUnion]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [Finset.sum_map]
  have hbM := Finset.HasAntidiagonal.mem_antidiagonal.mp hb
  calc
    _ = ∑ d ∈ Finset.piAntidiag S b.2,
        if E b.1 then ((M.choose b.1 : ℝ) * x p ^ b.1) * allocationWeight S x d else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdm := Finset.mem_piAntidiag.mp hd
      have hdp : d p = 0 := by
        by_contra h
        exact hp (hdm.2 p h)
      simp only [addRightEmbedding_apply, Pi.add_apply, if_true, hdp, zero_add]
      split_ifs with hE
      · unfold allocationWeight
        rw [Nat.multinomial_cons, Finset.prod_cons]
        simp only [Pi.add_apply, if_true, hdp, zero_add]
        have hsum : (∑ q ∈ S, (d q + if q = p then b.1 else 0)) = b.2 := by
          simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', hp, if_false, add_zero] using hdm.1
        have hm : Nat.multinomial S (d + fun q => if q = p then b.1 else 0) = Nat.multinomial S d := by
          apply Nat.multinomial_congr
          intro q hq
          simp only [Pi.add_apply, if_neg (ne_of_mem_of_not_mem hq hp), add_zero]
        have hprod : (∏ q ∈ S, x q ^ (d q + if q = p then b.1 else 0)) = ∏ q ∈ S, x q ^ d q := by
          apply Finset.prod_congr rfl
          intro q hq
          rw [if_neg (ne_of_mem_of_not_mem hq hp), add_zero]
        rw [hsum, hbM, hm, hprod, Nat.cast_mul]
        ring
      · rfl
    _ = _ := by
      by_cases hE : E b.1
      · simp only [if_pos hE, ← Finset.mul_sum]
        congr 1
        exact (Finset.sum_pow_eq_sum_piAntidiag S x b.2).symm
      · simp [hE]


/-- The selected cofactor orders retain their exact binomial and complementary-factor weights. -/
theorem marked_allocation {ι : Type*} [DecidableEq ι] (S : Finset ι) {p : ι} (hp : p ∈ S)
    (x : ι → ℝ) (M : ℕ) (U : Finset ℕ) (hU : ∀ k ∈ U, k ≤ M) :
    (∑ d ∈ (Finset.piAntidiag S M).filter (fun d => M - d p ∈ U),
      allocationWeight S x d) =
    ∑ k ∈ U, (M.choose (M - k) : ℝ) * x p ^ (M - k) * (∑ q ∈ S.erase p, x q) ^ k := by
  have h := marked_allocation_cons (S.erase p) p (Finset.notMem_erase p S) x M
    (fun l => M - l ∈ U)
  have hcons : (S.erase p).cons p (Finset.notMem_erase p S) = S := by
    rw [Finset.cons_eq_insert, Finset.insert_erase hp]
  rw [hcons, Finset.Nat.antidiagonal_eq_map', Finset.sum_map] at h
  rw [Finset.sum_filter, h]
  calc
    _ = ∑ k ∈ Finset.range (M + 1),
        if k ∈ U then (M.choose (M - k) : ℝ) * x p ^ (M - k) * (∑ q ∈ S.erase p, x q) ^ k else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkM : k ≤ M := by simpa using Finset.mem_range.mp hk
      change (if M - (M - k) ∈ U then (M.choose (M - k) : ℝ) * x p ^ (M - k) *
        (∑ q ∈ S.erase p, x q) ^ k else 0) = _
      rw [Nat.sub_sub_self hkM]
    _ = _ := by
      rw [← Finset.sum_filter]
      congr 1
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨fun h => h.2, fun hk => ⟨by have := hU k hk; omega, hk⟩⟩

/-- Summing all selected majority factors introduces no factor-counting loss. -/
theorem marked_binomial_le {ι : Type*} [DecidableEq ι] (S : Finset ι) (x : ι → ℝ)
    (hx : ∀ p ∈ S, 0 ≤ x p) (U : Finset ℕ) (M : ℕ)
    (hU : ∀ k ∈ U, 2 * k < M) :
    (∑ p ∈ S, ∑ k ∈ U, (M.choose (M - k) : ℝ) * x p ^ (M - k) *
      (∑ q ∈ S.erase p, x q) ^ k) ≤ (∑ p ∈ S, x p) ^ M := by
  have h := selected_allocation_le S x hx U M hU
  have hkM : ∀ k ∈ U, k ≤ M := by intro k hk; have := hU k hk; omega
  convert h using 1
  apply Finset.sum_congr rfl
  intro p hp
  exact (marked_allocation S hp x M U hkM).symm


open RiemannGaussian

/-- The other squarefree prime logarithms sum to the literal quotient logarithm. -/
theorem sum_log_erase_eq_log_cofactor {n p : ℕ} (hn : Squarefree n)
    (hp : p ∈ n.primeFactors) :
    (∑ q ∈ n.primeFactors.erase p, Real.log q) = Real.log (n / p : ℕ) := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have hsum := Finset.sum_erase_add n.primeFactors (fun q : ℕ => Real.log q) hp
  have hlog := CoprimeEulerPhase.squarefree_log_eq_prime_sum hn
  have hdlog : Real.log (n / p : ℕ) = Real.log n - Real.log p := by
    rw [Nat.cast_div hpd (by exact_mod_cast hpp.ne_zero), Real.log_div
      (by exact_mod_cast hn.ne_zero) (by exact_mod_cast hpp.ne_zero)]
  linarith

/-- The actual unpaid orders over all prime divisors are bounded by one full product-log power. -/
theorem original_unpaid_prime_allocation_le {n : ℕ} (hn : Squarefree n) (N : ℕ) :
    (∑ p ∈ n.primeFactors, ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
      ((N + 1).choose (N + 1 - k) : ℝ) * Real.log p ^ (N + 1 - k) *
        Real.log (n / p : ℕ) ^ k) ≤ Real.log n ^ (N + 1) := by
  have h := marked_binomial_le n.primeFactors (fun p : ℕ => Real.log p)
    (fun p _ => Real.log_natCast_nonneg p) (ZetaRieszWingHighOrders.unpaidOrders N)
    (N + 1) (unpaid_orders_submajority N)
  rw [← CoprimeEulerPhase.squarefree_log_eq_prime_sum hn] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg (fun t : ℝ => ((N + 1).choose (N + 1 - k) : ℝ) *
    Real.log p ^ (N + 1 - k) * t ^ k) (sum_log_erase_eq_log_cofactor hn hp).symm


-- Restore the factorial normalization before comparing actual arithmetic atoms.
/-- Exact conversion between the complementary factorial weights and their binomial coefficient. -/
theorem factorial_split (x y : ℝ) (M k : ℕ) (hk : k ≤ M) :
    x ^ k / (k.factorial : ℝ) * (y ^ (M - k) / ((M - k).factorial : ℝ)) =
      (M.choose (M - k) : ℝ) * y ^ (M - k) * x ^ k / (M.factorial : ℝ) := by
  have hc := Nat.choose_mul_factorial_mul_factorial (Nat.sub_le M k)
  rw [Nat.sub_sub_self hk] at hc
  have hcR : (M.choose (M - k) : ℝ) * ((M - k).factorial : ℝ) * (k.factorial : ℝ) =
      (M.factorial : ℝ) := by exact_mod_cast hc
  have hM : (M.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero M
  have hkf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hlf : ((M - k).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (M-k)
  field_simp
  linear_combination -(x ^ k * y ^ (M-k)) * hcR

/-- The full prime-divisor allocation mass at the actual unpaid orders. -/
def primeAllocation (n N : ℕ) : ℝ :=
  ∑ p ∈ n.primeFactors, ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
    Real.log (n / p : ℕ) ^ k / (k.factorial : ℝ) *
      (Real.log p ^ (N + 1 - k) / ((N + 1 - k).factorial : ℝ))

/-- The actual prime-divisor allocation mass is nonnegative. -/
theorem primeAllocation_nonneg (n N : ℕ) : 0 ≤ primeAllocation n N := by
  unfold primeAllocation
  exact Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun k _ => by positivity))

/-- All distinguished prime incidences together cost at most one original factorial moment. -/
theorem primeAllocation_le {n : ℕ} (hn : Squarefree n) (N : ℕ) :
    primeAllocation n N ≤ Real.log n ^ (N + 1) / ((N + 1).factorial : ℝ) := by
  have h := div_le_div_of_nonneg_right (original_unpaid_prime_allocation_le hn N)
    (show 0 ≤ ((N + 1).factorial : ℝ) by positivity)
  apply le_of_eq_of_le _ h
  unfold primeAllocation
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro k hk
  exact factorial_split _ _ _ _ (by have := unpaid_orders_submajority N k hk; omega)



end
end RiemannGaussian.ZetaRieszJointAllocation
