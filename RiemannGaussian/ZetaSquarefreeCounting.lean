/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRoughDivisorLinearBound
import RiemannGaussian.ZetaSquarefreeDivisibilityPrefix

/-!
# Centered counts of marked squarefree integers

Finite square exclusion has an exact signed floor expansion. Subtracting
its exact density leaves lattice errors with a factor-sensitive bound,
uniform over every finite square sieve. Passing to the complete square
sieve gives arithmetic prefix estimates; no cancellation hypothesis for
the ordinary-prime tail is used.
-/

namespace RiemannGaussian.SquarefreeCounting
noncomputable section
open Complex Filter Topology
open scoped Classical

/-- A first-power mark with a finite collection of prime squares
excluded. The zero physical index is not used in the positive prefix. -/
def finiteCoefficient (W Q : Finset ℕ) (n : ℕ) : ℝ :=
  if (∏ p ∈ W, p) ∣ n ∧ (¬∃ p ∈ Q, p ^ 2 ∣ n) then 1 else 0

/-- The actual positive-integer prefix for the finite square sieve. -/
def finiteCount (W Q : Finset ℕ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 N, finiteCoefficient W Q n

/-- The exact rational density of the finite periodic sieve, with
all shared-prime intersections retained. -/
def finiteDensity (W Q : Finset ℕ) : ℝ :=
  ∑ V ∈ Q.powerset, (-1 : ℝ) ^ V.card / primeSquareIntersection W V

/-- The complete signed square expansion holds coefficientwise. -/
theorem finiteCoefficient_eq_subsets (W Q : Finset ℕ)
    (hW : ∀ p ∈ W, p.Prime) (hQ : ∀ p ∈ Q, p.Prime) (n : ℕ) :
    finiteCoefficient W Q n = ∑ V ∈ Q.powerset,
      (-1 : ℝ) ^ V.card * (if primeSquareIntersection W V ∣ n then 1 else 0) := by
  have hc := primeSquareMultipleMask_mul_eq W Q hW hQ (fun _ ↦ (1 : ℂ)) n
  have he : (∑ V ∈ Q.powerset, (-1 : ℂ) ^ V.card *
      (if primeSquareIntersection W V ∣ n then 1 else 0)).re =
      ∑ V ∈ Q.powerset, (-1 : ℝ) ^ V.card *
        (if primeSquareIntersection W V ∣ n then 1 else 0) := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro V _
    have heq : (-1 : ℂ) ^ V.card = (((-1 : ℝ) ^ V.card : ℝ) : ℂ) := by
      simp only [Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one]
    split_ifs
    · simpa only [mul_one, Complex.ofReal_re] using congrArg Complex.re heq
    · simp
  have hh := congrArg Complex.re hc
  rw [Complex.sub_re, he] at hh
  by_cases hw : (∏ p ∈ W, p) ∣ n <;> by_cases hq : ∃ p ∈ Q, p ^ 2 ∣ n <;>
    simp [primeSquareMultipleMask, finiteCoefficient, hw, hq] at hh ⊢ <;> linarith

/-- Counting multiples turns every finite intersection into an exact
integer quotient, before any floor error is estimated. -/
theorem finiteCount_eq_floor_sum (W Q : Finset ℕ)
    (hW : ∀ p ∈ W, p.Prime) (hQ : ∀ p ∈ Q, p.Prime) (N : ℕ) :
    finiteCount W Q N = ∑ V ∈ Q.powerset,
      (-1 : ℝ) ^ V.card * (N / primeSquareIntersection W V : ℕ) := by
  simp only [finiteCount, finiteCoefficient_eq_subsets W Q hW hQ]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro V _
  rw [← Finset.mul_sum]
  congr 1
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
    Nat.Ioc_filter_dvd_card_eq_div]

/-- The floor error admits every exponent between zero and one,
retaining its small-argument gain as well as the unit bound. -/
theorem abs_floor_sub_le_rpow {x σ : ℝ} (hx : 0 ≤ x) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    |(⌊x⌋₊ : ℝ) - x| ≤ x ^ σ := by
  have hf := Nat.floor_le hx
  rw [abs_of_nonpos (sub_nonpos.mpr hf)]
  by_cases hx1 : x ≤ 1
  · have hp : x ≤ x ^ σ := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge' hx hx1 hσ hσ1
    have hn := Nat.cast_nonneg (α := ℝ) ⌊x⌋₊
    linarith
  · have hp := Real.one_le_rpow (le_of_not_ge hx1) hσ
    have hlt := Nat.lt_floor_add_one x
    linarith

/-- The original lattice remainder has a multiplicative divisor
weight at every exponent in the stated interval. -/
theorem abs_nat_div_sub_le (N : ℕ) {P : ℕ} (hP : 0 < P)
    {σ : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    |((N / P : ℕ) : ℝ) - (N : ℝ) / P| ≤ (N : ℝ) ^ σ * zetaPrimeExpWeight σ P := by
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  have h := abs_floor_sub_le_rpow (show 0 ≤ (N : ℝ) / P by positivity) hσ hσ1
  rw [Nat.floor_div_natCast, Nat.floor_natCast] at h
  apply h.trans_eq
  rw [Real.div_rpow (Nat.cast_nonneg N) hPR.le]
  have he : zetaPrimeExpWeight σ P = ((P : ℝ) ^ σ)⁻¹ := by
    rw [zetaPrimeExpWeight, Real.rpow_def_of_pos hPR, ← Real.exp_neg]
    congr 1
    ring
  rw [he, div_eq_mul_inv]

/-- The centered finite count is the full signed sum of the lattice
remainders; its density and every square overlap stay explicit. -/
theorem finiteCount_sub_density_eq (W Q : Finset ℕ)
    (hW : ∀ p ∈ W, p.Prime) (hQ : ∀ p ∈ Q, p.Prime) (N : ℕ) :
    finiteCount W Q N - finiteDensity W Q * N =
      ∑ V ∈ Q.powerset, (-1 : ℝ) ^ V.card *
        (((N / primeSquareIntersection W V : ℕ) : ℝ) - (N : ℝ) / primeSquareIntersection W V) := by
  rw [finiteCount_eq_floor_sum W Q hW hQ, finiteDensity, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun _ _ ↦ by ring)

/-- The complete finite square sieve has a centered power bound,
uniform over the number and sizes of the excluded prime squares. -/
theorem finiteCount_centered_bound (W Q : Finset ℕ)
    (hW : ∀ p ∈ W, p.Prime) (hQ : ∀ p ∈ Q, p.Prime)
    {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1) (N : ℕ) :
    |finiteCount W Q N - finiteDensity W Q * N| ≤
      Real.exp (primeSquareWeightMass σ) * (N : ℝ) ^ σ *
        ∏ p ∈ W, primeSquareCorrectedWeight σ p := by
  rw [finiteCount_sub_density_eq W Q hW hQ]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ V ∈ Q.powerset,
      (N : ℝ) ^ σ * zetaPrimeExpWeight σ (primeSquareIntersection W V) := by
      apply Finset.sum_le_sum
      intro V hV
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact abs_nat_div_sub_le N (primeSquareIntersection_pos W V hW
        (fun p hp ↦ hQ p (Finset.mem_powerset.mp hV hp))) (by linarith) hσ1
    _ = (N : ℝ) ^ σ * ∑ V ∈ Q.powerset, zetaPrimeExpWeight σ (primeSquareIntersection W V) :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := (mul_le_mul_of_nonneg_left (sum_primeSquareIntersection_weight_le W Q hW hQ hσ)
      (Real.rpow_nonneg (Nat.cast_nonneg N) σ)).trans_eq (by
        unfold primeSquareCorrectedWeight
        ring)

private theorem tendsto_div_of_centered_bound {f : ℕ → ℝ} {d C σ : ℝ}
    (hσ : σ < 1) (hb : ∀ N : ℕ, |f N - d * N| ≤ C * (N : ℝ) ^ σ) :
    Tendsto (fun N : ℕ ↦ f N / N) atTop (𝓝 d) := by
  have hz : Tendsto (fun N : ℕ ↦ C * (N : ℝ) ^ (σ - 1)) atTop (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop (show 0 < 1 - σ by linarith)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul C
    simpa only [Function.comp_def, neg_sub, mul_zero] using h
  have he : Tendsto (fun N : ℕ ↦ (f N - d * N) / N) atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ hz
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hn]
    calc
      _ ≤ C * (N : ℝ) ^ σ / N := div_le_div_of_nonneg_right (hb N) hn.le
      _ = _ := by rw [Real.rpow_sub hn, Real.rpow_one]; ring
  have h := he.add_const d
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  field_simp
  ring

/-- The finite signed reciprocal sum is the actual asymptotic
density of its periodic arithmetic sequence. -/
theorem finiteCount_div_tendsto (W Q : Finset ℕ)
    (hW : ∀ p ∈ W, p.Prime) (hQ : ∀ p ∈ Q, p.Prime) :
    Tendsto (fun N : ℕ ↦ finiteCount W Q N / N) atTop (𝓝 (finiteDensity W Q)) := by
  apply tendsto_div_of_centered_bound (σ := 3 / 4)
    (C := Real.exp (primeSquareWeightMass (3 / 4)) *
      ∏ p ∈ W, primeSquareCorrectedWeight (3 / 4) p) (by norm_num)
  intro N
  have h := finiteCount_centered_bound W Q hW hQ (by norm_num : (1 / 2 : ℝ) < 3 / 4)
    (by norm_num : (3 / 4 : ℝ) ≤ 1) N
  exact h.trans_eq (by ring)

/-- Finite sieve coefficients retain their original nonnegative sign. -/
theorem finiteCoefficient_nonneg (W Q : Finset ℕ) (n : ℕ) : 0 ≤ finiteCoefficient W Q n := by
  unfold finiteCoefficient
  split_ifs <;> norm_num

/-- The finite sieve counts actual integers, so it lies between zero
and the full positive-integer count. -/
theorem finiteCount_bounds (W Q : Finset ℕ) (N : ℕ) :
    0 ≤ finiteCount W Q N ∧ finiteCount W Q N ≤ N := by
  refine ⟨Finset.sum_nonneg (fun n _ ↦ finiteCoefficient_nonneg W Q n), ?_⟩
  calc
    _ ≤ ∑ _n ∈ Finset.Ioc 0 N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n _
      unfold finiteCoefficient
      split_ifs <;> norm_num
    _ = _ := by simp

/-- Adding square exclusions can only decrease the actual count. -/
theorem finiteCount_antitone_squares (W : Finset ℕ) {Q Q' : Finset ℕ}
    (hQQ : Q ⊆ Q') (N : ℕ) : finiteCount W Q' N ≤ finiteCount W Q N := by
  apply Finset.sum_le_sum
  intro n _
  by_cases h : (∏ p ∈ W, p) ∣ n ∧ (¬∃ p ∈ Q', p ^ 2 ∣ n)
  · have h' : (∏ p ∈ W, p) ∣ n ∧ (¬∃ p ∈ Q, p ^ 2 ∣ n) :=
      ⟨h.1, fun ⟨p, hp, hd⟩ ↦ h.2 ⟨p, hQQ hp, hd⟩⟩
    simp [finiteCoefficient, h, h']
  · simp only [finiteCoefficient, if_neg h]
    split_ifs <;> norm_num

/-- The signed finite density is nonnegative because it is the limit
of the actual normalized counts, not because its signs were discarded. -/
theorem finiteDensity_nonneg (W Q : Finset ℕ)
    (hW : ∀ p ∈ W, p.Prime) (hQ : ∀ p ∈ Q, p.Prime) : 0 ≤ finiteDensity W Q := by
  apply ge_of_tendsto (finiteCount_div_tendsto W Q hW hQ)
  exact Eventually.of_forall (fun N ↦ div_nonneg (finiteCount_bounds W Q N).1 (Nat.cast_nonneg N))

/-- Density monotonicity follows from the full signed counting
identity and holds with every shared-prime correction. -/
theorem finiteDensity_antitone_squares (W : Finset ℕ) {Q Q' : Finset ℕ}
    (hW : ∀ p ∈ W, p.Prime) (hQ : ∀ p ∈ Q, p.Prime) (hQ' : ∀ p ∈ Q', p.Prime)
    (hQQ : Q ⊆ Q') : finiteDensity W Q' ≤ finiteDensity W Q := by
  exact le_of_tendsto_of_tendsto (finiteCount_div_tendsto W Q' hW hQ')
    (finiteCount_div_tendsto W Q hW hQ) (Eventually.of_forall (fun N ↦
      div_le_div_of_nonneg_right (finiteCount_antitone_squares W hQQ N) (Nat.cast_nonneg N)))

/-- The canonical density of marked squarefree integers is the
decreasing limit of their exact finite periodic sieve densities. -/
def density (W : Finset ℕ) : ℝ :=
  ⨅ K : ℕ, finiteDensity W (zetaSquarePrimesThrough K)

/-- The full density is approached by genuine finite square sieves. -/
theorem finiteDensity_tendsto (W : Finset ℕ) (hW : ∀ p ∈ W, p.Prime) :
    Tendsto (fun K : ℕ ↦ finiteDensity W (zetaSquarePrimesThrough K)) atTop (𝓝 (density W)) := by
  have ha : Antitone (fun K : ℕ ↦ finiteDensity W (zetaSquarePrimesThrough K)) := by
    intro i j hij
    apply finiteDensity_antitone_squares W hW (zetaSquarePrimesThrough_prime i)
      (zetaSquarePrimesThrough_prime j)
    exact Finset.filter_subset_filter _ (Finset.Icc_subset_Icc le_rfl hij)
  apply tendsto_atTop_ciInf ha
  refine ⟨0, ?_⟩
  rintro _ ⟨K, rfl⟩
  exact finiteDensity_nonneg W _ hW (zetaSquarePrimesThrough_prime K)

/-- The actual count of all squarefree positive integers carrying
the complete first-power prime mark. -/
def count (W : Finset ℕ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 N, if Squarefree n ∧ (∏ p ∈ W, p) ∣ n then 1 else 0

/-- For each finite physical prefix the complete square sieve agrees
with the actual squarefree condition in the limit. -/
theorem finiteCount_tendsto (W : Finset ℕ) (N : ℕ) :
    Tendsto (fun K : ℕ ↦ finiteCount W (zetaSquarePrimesThrough K) N)
      atTop (𝓝 (count W N)) := by
  apply tendsto_finsetSum
  intro n _
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_no_primeSquareThrough_iff n] with K hK
  by_cases hd : (∏ p ∈ W, p) ∣ n <;>
    simp [finiteCoefficient, hK, hd]

/-- All prime squares have now been included. The independent
centered arithmetic bound is uniform in the physical prefix and retains
the full multiplicative cost of the first-power mark. -/
theorem count_centered_bound (W : Finset ℕ) (hW : ∀ p ∈ W, p.Prime)
    {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1) (N : ℕ) :
    |count W N - density W * N| ≤
      Real.exp (primeSquareWeightMass σ) * (N : ℝ) ^ σ *
        ∏ p ∈ W, primeSquareCorrectedWeight σ p := by
  apply le_of_tendsto (((finiteCount_tendsto W N).sub
    ((finiteDensity_tendsto W hW).mul_const (N : ℝ))).abs)
  exact Eventually.of_forall (fun K ↦ finiteCount_centered_bound W _ hW
    (zetaSquarePrimesThrough_prime K) hσ hσ1 N)

/-- The canonical density is the asymptotic density of the actual
marked squarefree sequence, with no prime-distribution premise. -/
theorem count_div_tendsto (W : Finset ℕ) (hW : ∀ p ∈ W, p.Prime) :
    Tendsto (fun N : ℕ ↦ count W N / N) atTop (𝓝 (density W)) := by
  apply tendsto_div_of_centered_bound (σ := 3 / 4)
    (C := Real.exp (primeSquareWeightMass (3 / 4)) *
      ∏ p ∈ W, primeSquareCorrectedWeight (3 / 4) p) (by norm_num)
  intro N
  exact (count_centered_bound W hW (by norm_num : (1 / 2 : ℝ) < 3 / 4)
    (by norm_num : (3 / 4 : ℝ) ≤ 1) N).trans_eq (by ring)

end
end RiemannGaussian.SquarefreeCounting
