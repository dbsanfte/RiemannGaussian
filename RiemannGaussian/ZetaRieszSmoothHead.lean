/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszEulerPrimeHeadDensity
import RiemannGaussian.ZetaPrimeKernelSecondDifference

/-!
# Prime-density bounds for actual smooth Riesz sums

The original divisor weights and complete fixed factorial filter have an explicit
geometric allowance on every squarefree class supported through N^2. The
eventual threshold is uniform over all classes, filters, ordinates and positive
physical lengths; the full coefficient cost is displayed. No zero is assumed.
-/

namespace RiemannGaussian.ZetaRieszSmoothHead
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszEulerPrimeHeadDensity

/-- Actual squarefreeness identifies the divisor count with the full
prime-subset count, including the unit and both complementary divisors. -/
theorem card_divisors_of_squarefree {n : ℕ} (hn : Squarefree n) :
    n.divisors.card = 2 ^ n.primeFactors.card := by
  have h := Nat.sum_divisors_filter_squarefree hn.ne_zero (f := fun _ => (1 : ℕ))
  rw [Nat.divisors_filter_squarefree_of_squarefree hn, Nat.factors_eq] at h
  simpa using h

/-- The original divisor-logarithm majorant has a prime-count allowance
on every squarefree integer, without changing its arithmetic coefficient. -/
theorem logMajorant_le_prime_count {n : ℕ} (hn : Squarefree n) :
    zetaMoebiusLogMajorant n ≤ Real.log n * (2 : ℝ) ^ n.primeFactors.card := by
  rw [zetaMoebiusLogMajorant, Nat.sum_divisorsAntidiagonal' (fun _ d => Real.log d)]
  calc
    _ ≤ ∑ _d ∈ n.divisors, Real.log n := by
      apply Finset.sum_le_sum
      intro d hd
      apply Real.log_le_log (by exact_mod_cast Nat.pos_of_mem_divisors hd)
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn.ne_zero) (Nat.dvd_of_mem_divisors hd)
    _ = _ := by simp [card_divisors_of_squarefree hn, mul_comm]

/-- Every exact squarefree atom factors into its complete local prime
allowance; the factor two counts all divisor choices. -/
theorem prime_count_weight_eq_product {n : ℕ} (hn : Squarefree n) (sigma : ℝ) :
    (2 : ℝ) ^ n.primeFactors.card * Real.exp (-sigma * Real.log n) =
      ∏ p ∈ n.primeFactors, (2 * Real.exp (-sigma * Real.log p)) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const,
    CoprimeEulerPhase.squarefree_log_eq_prime_sum hn, Finset.mul_sum, Real.exp_sum]

/-- Any finite class of actual squarefree integers supported on the
head is bounded by one Euler product, even with arbitrary size restrictions. -/
theorem squarefree_head_mass_le (D S : Finset ℕ)
    (hD : ∀ n ∈ D, Squarefree n) (hS : ∀ n ∈ D, n.primeFactors ⊆ S) (sigma : ℝ) :
    (∑ n ∈ D, (2 : ℝ) ^ n.primeFactors.card * Real.exp (-sigma * Real.log n)) ≤
      ∏ p ∈ S, (1 + 2 * Real.exp (-sigma * Real.log p)) := by
  have hinj : Set.InjOn Nat.primeFactors (D : Set ℕ) := by
    intro n hn m hm he
    rw [← Nat.prod_primeFactors_of_squarefree (hD n hn),
      ← Nat.prod_primeFactors_of_squarefree (hD m hm), he]
  calc
    _ = ∑ n ∈ D, ∏ p ∈ n.primeFactors, (2 * Real.exp (-sigma * Real.log p)) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact prime_count_weight_eq_product (hD n hn) sigma
    _ = ∑ T ∈ D.image Nat.primeFactors, ∏ p ∈ T, (2 * Real.exp (-sigma * Real.log p)) :=
      (Finset.sum_image (s := D) (g := Nat.primeFactors)
        (f := fun T : Finset ℕ => ∏ p ∈ T, (2 * Real.exp (-sigma * Real.log p))) hinj).symm
    _ ≤ ∑ T ∈ S.powerset, ∏ p ∈ T, (2 * Real.exp (-sigma * Real.log p)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro T hT
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hT
        exact Finset.mem_powerset.mpr (hS n hn)
      · intro T _hT _hT'
        positivity
    _ = _ := (Finset.prod_one_add S).symm

/-- The original log band supplies an exact linear logarithmic cost. -/
theorem log_le_of_mem_band {N n : ℕ} (hn : n ∈ zetaPrimeLogBand N) :
    Real.log n ≤ 32 * (N : ℝ) * Real.log 2 := by
  have hp := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
  have hle : (n : ℝ) ≤ (2 : ℝ) ^ (32 * N) := by exact_mod_cast hp.2
  have h := Real.log_le_log (by exact_mod_cast hp.1 : (0 : ℝ) < n) hle
  rw [Real.log_pow] at h
  simpa using h

/-- The complete original Riesz filter over any actual squarefree
head class has an Euler-product allowance. The physical length is arbitrary
and positive; the bound is uniform in the ordinate and retains the full filter. -/
theorem norm_actual_head_sum_le (D S : Finset ℕ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {L q : ℝ} (hL : 0 < L) (hq : 0 < q)
    (hD : ∀ n ∈ D, Squarefree n) (hband : D ⊆ zetaPrimeLogBand N)
    (hS : ∀ n ∈ D, n.primeFactors ⊆ S) :
    ‖∑ n ∈ D, SquarefreeVaughanLogSource.coefficient L n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
      (32 * (N : ℝ) * Real.log 2 * q⁻¹ ^ N *
        ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
      ∏ p ∈ S, (1 + 2 * Real.exp (-(3 / 2 - q) * Real.log p)) := by
  let C := 32 * (N : ℝ) * Real.log 2 * q⁻¹ ^ N *
    ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    _ ≤ ∑ n ∈ D, ‖SquarefreeVaughanLogSource.coefficient L n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ D, C * ((2 : ℝ) ^ n.primeFactors.card *
        Real.exp (-(3 / 2 - q) * Real.log n)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hb := hband hn
      have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
      have hc := (SquarefreeVaughanLogSource.norm_coefficient_le hL n).trans
        ((logMajorant_le_prime_count (hD n hn)).trans
          (mul_le_mul_of_nonneg_right (log_le_of_mem_band hb) (by positivity)))
      have hk := norm_zetaPrimeFilterKernel_le_tilt P N (3 / 2 + Complex.I * y) hn1 hq
      have h := mul_le_mul hc hk (norm_nonneg _) (by positivity)
      rw [norm_mul]
      apply h.trans_eq
      have hs : (3 / 2 + Complex.I * (y : ℂ)).re = (3 / 2 : ℝ) := by norm_num
      rw [hs]
      dsimp [C]
      ring
    _ = C * ∑ n ∈ D, (2 : ℝ) ^ n.primeFactors.card *
        Real.exp (-(3 / 2 - q) * Real.log n) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (squarefree_head_mass_le D S hD hS (3 / 2 - q)) hC

/-- An explicit geometric allowance for all quadratic smooth classes
at once. The eventual threshold is independent of the class, polynomial,
ordinate and positive physical length; the polynomial cost is displayed. -/
theorem eventually_norm_quadratic_head_sum_le_sqrt {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    ∀ᶠ N : ℕ in atTop, ∀ (D S : Finset ℕ) (P : Polynomial ℂ) (y L : ℝ),
      (∀ n ∈ D, Squarefree n) → D ⊆ zetaPrimeLogBand N →
      (∀ n ∈ D, n.primeFactors ⊆ S) → (∀ p ∈ S, p.Prime ∧ p ≤ N ^ 2) → 0 < L →
        ‖(u : ℂ) ^ (N + 1) * ∑ n ∈ D, SquarefreeVaughanLogSource.coefficient L n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
          (32 * Real.log 2 * (∑ k ∈ P.support, ‖P.coeff k‖) * u) *
            (N : ℝ) * Real.sqrt u ^ N := by
  let eps : ℝ := -Real.log u / 2
  have heps : 0 < eps := by dsimp [eps]; linarith [Real.log_neg hu hu1]
  have hrate : u * Real.exp eps = Real.sqrt u := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hu]
    conv_lhs => lhs; rw [← Real.exp_log hu]
    rw [← Real.exp_add]
    congr 1
    dsimp [eps]
    ring
  filter_upwards [eventually_quadratic_head_product_le heps] with N hN D S P y L hD hb hS hp hL
  have hc := norm_actual_head_sum_le D S P N y hL (by norm_num : (0 : ℝ) < 1) hD hb hS
  simp only [inv_one, one_pow, mul_one, show (3 / 2 - 1 : ℝ) = 1 / 2 by norm_num] at hc
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  apply (mul_le_mul_of_nonneg_left hc (pow_nonneg hu.le _)).trans
  calc
    _ ≤ u ^ (N + 1) * ((32 * (N : ℝ) * Real.log 2 * (∑ k ∈ P.support, ‖P.coeff k‖)) *
        Real.exp (eps * N)) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hu.le _)
      exact mul_le_mul_of_nonneg_left (hN S hp (1 / 2) le_rfl) (by positivity)
    _ = (32 * Real.log 2 * (∑ k ∈ P.support, ‖P.coeff k‖) * u) *
        (N : ℝ) * (u * Real.exp eps) ^ N := by
      rw [show eps * (N : ℝ) = (N : ℝ) * eps by ring, Real.exp_nat_mul, pow_succ, mul_pow]
      ring
    _ = _ := by rw [hrate]

/-- Actual prime density pays every squarefree class supported through
the square of the order. The statement covers all class families, all positive
physical-length schedules and the full fixed filter at every original order. -/
theorem tendsto_actual_quadratic_head_sum (D S : ℕ → Finset ℕ)
    (hD : ∀ N n, n ∈ D N → Squarefree n)
    (hband : ∀ N, D N ⊆ zetaPrimeLogBand N)
    (hsupport : ∀ N n, n ∈ D N → n.primeFactors ⊆ S N)
    (hS : ∀ N p, p ∈ S N → p.Prime ∧ p ≤ N ^ 2)
    (P : Polynomial ℂ) (y : ℝ) (L : ℕ → ℝ) (hL : ∀ N, 0 < L N)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      ∑ n ∈ D N, SquarefreeVaughanLogSource.coefficient (L N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) atTop (nhds 0) := by
  let q : ℝ := (u + 1) / 2
  have hq : 0 < q := by dsimp [q]; linarith
  have huq : u < q := by dsimp [q]; linarith
  have hhalf : 1 / 2 ≤ (3 / 2 : ℝ) - q := by dsimp [q]; linarith
  let r : ℝ := u / q
  have hr : 0 < r := div_pos hu hq
  have hr1 : r < 1 := (div_lt_one hq).mpr huq
  obtain ⟨eps, heps, hsmall⟩ := exists_small_exponential_factor hr hr1
  let F : ℝ := ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k
  have hF : 0 ≤ F := by dsimp [F]; positivity
  let C : ℝ := 32 * Real.log 2 * F * u
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb : ∀ᶠ N : ℕ in atTop, ‖(u : ℂ) ^ (N + 1) *
      ∑ n ∈ D N, SquarefreeVaughanLogSource.coefficient (L N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
      C * (((N : ℝ) + 1) * (r * Real.exp eps) ^ N) := by
    filter_upwards [eventually_quadratic_head_product_le heps] with N hN
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
    apply (mul_le_mul_of_nonneg_left
      (norm_actual_head_sum_le (D N) (S N) P N y (hL N) hq
        (hD N) (hband N) (hsupport N)) (pow_nonneg hu.le _)).trans
    calc
      _ ≤ u ^ (N + 1) * ((32 * (N : ℝ) * Real.log 2 * q⁻¹ ^ N * F) *
          Real.exp (eps * N)) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hu.le _)
        exact mul_le_mul_of_nonneg_left (hN (S N) (hS N) _ hhalf) (by positivity)
      _ = C * ((N : ℝ) * (r * Real.exp eps) ^ N) := by
        rw [show eps * (N : ℝ) = (N : ℝ) * eps by ring, Real.exp_nat_mul]
        dsimp [C, r]
        rw [pow_succ, div_eq_mul_inv, mul_pow, mul_pow]
        ring
      _ ≤ _ := by gcongr; linarith
  apply squeeze_zero_norm' hb
  simpa only [pow_one, mul_zero] using
    (tendsto_successor_pow_mul_geometric 1 (mul_pos hr (Real.exp_pos eps)) hsmall).const_mul C

end
end RiemannGaussian.ZetaRieszSmoothHead
