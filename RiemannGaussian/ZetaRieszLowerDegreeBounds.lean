/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFourExtremeDeletion

/-!
# Degree-dependent bounds for the actual physical-cutoff prime classes

The source factor stays inside a general logarithmic tilt with the original
floor-dependent physical length and every fixed polynomial filter. The
entire two-or-more-extreme class decays for u<exp(-2/3), and the entire
three-or-more class for u<exp(-9/16), with exact subunit geometric rates.
The finite selections may change freely and the bounds are uniform in the
ordinate. No hypothetical zero or independent whole-carrier floor is used.
-/

namespace RiemannGaussian.ZetaRieszLowerDegreeBounds
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszExtremePrimeCount

/-- An arbitrary positive exponential comparison supplies the actual
floor-dependent length bound, with no invented starting order. -/
theorem eventually_length_ge_exponent {u h : ℝ} (hu : 0 < u) (hh : 0 ≤ h)
    (huh : u < Real.exp (-h)) :
    ∀ᶠ N : ℕ in atTop, 2 * h * N ≤ SquarefreeVaughanLogSource.length u N := by
  have hprod : u * Real.exp h < 1 := by
    calc
      _ < Real.exp (-h) * Real.exp h := mul_lt_mul_of_pos_right huh (Real.exp_pos h)
      _ = 1 := by rw [← Real.exp_add]; simp
  simpa only [Real.log_exp] using eventually_length_ge_tilt hu
    (Real.one_le_exp_iff.mpr hh) hprod

/-- The exact degree-dependent geometric rate keeps the source factor
inside the tilt and is applicable to every actual finite prime selection. -/
def degreeRate (k : ℕ) (h q σ : ℝ) : ℝ :=
  q⁻¹ * Real.exp (2 * k * h * (q + σ - 3 / 2) - h)

/-- An independently proved arithmetic estimate for any prime degree
and admissible tilt. Decay requires this explicit rate to be below one. -/
theorem eventually_norm_degree_sum_le (S : ℕ → Finset ℕ) (P : Polynomial ℂ) (y : ℝ)
    {u h q σ : ℝ} (hu : 0 < u) (hh : 0 ≤ h) (huh : u < Real.exp (-h))
    (hq : 0 < q) (hσ : 1 < σ) (hsign : q + σ - 3 / 2 ≤ 0) (k : ℕ)
    (hS : ∀ N n, n ∈ S N → k ≤ (extremePrimes u N n).card) :
    ∀ᶠ N : ℕ in atTop,
      ‖(u : ℂ) ^ (N + 1) * ∑ n ∈ S N,
        SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
      degreeRate k h q σ ^ N * (u * ZetaArithmeticLogWindow.tiltConstant P q σ) := by
  let a : ℝ := 2 * k * h * (q + σ - 3 / 2)
  have hC := ZetaArithmeticLogWindow.tiltConstant_nonneg P (σ := σ) hq
  have hr : u * (q⁻¹ * Real.exp a) ≤ degreeRate k h q σ := by
    calc
      _ ≤ Real.exp (-h) * (q⁻¹ * Real.exp a) :=
        mul_le_mul_of_nonneg_right huh.le (by positivity)
      _ = degreeRate k h q σ := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        dsimp [a]
        ring
  filter_upwards [eventually_length_ge_exponent hu hh huh] with N hLN
  have he : (∑ n ∈ S N, SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) =
      ∑ n ∈ (S N).filter Squarefree,
        SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hs : Squarefree n
    · simp only [hs, if_true]
    · simp [SquarefreeVaughanLogSource.coefficient, hs]
  have hb := ZetaArithmeticLogWindow.norm_sum_filter_of_log_bound ((S N).filter Squarefree)
    (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N))
    (fun n _ => SquarefreeVaughanLogSource.norm_coefficient_le
      (SquarefreeVaughanLogSource.length_pos u N) n) P N y σ q a hσ hq (by
      intro n hn
      have hs := (Finset.mem_filter.mp hn).2
      have hc : (k : ℝ) ≤ (extremePrimes u N n).card := by
        exact_mod_cast hS N n (Finset.mem_filter.mp hn).1
      have hmass := extreme_prime_log_budget u N hs
      have hkL := mul_le_mul_of_nonneg_right hc (SquarefreeVaughanLogSource.length_pos u N).le
      have hkN := mul_le_mul_of_nonneg_left hLN (show (0 : ℝ) ≤ k by positivity)
      have hlog : (2 * k * h) * N ≤ Real.log n := by nlinarith
      have he' := mul_le_mul_of_nonpos_left hlog hsign
      dsimp only [a]
      nlinarith only [he'])
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu, he]
  calc
    _ ≤ u ^ (N + 1) * ((q⁻¹ * Real.exp a) ^ N * ZetaArithmeticLogWindow.tiltConstant P q σ) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (u * (q⁻¹ * Real.exp a)) ^ N * (u * ZetaArithmeticLogWindow.tiltConstant P q σ) := by
      rw [pow_succ, mul_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hr N)
      (mul_nonneg hu.le hC)

/-- Every degree and tilt with a checked subunit rate pays the actual
normalized arithmetic class independently of hypothetical zeros. -/
theorem tendsto_degree_sum (S : ℕ → Finset ℕ) (P : Polynomial ℂ) (y : ℝ)
    {u h q σ : ℝ} (hu : 0 < u) (hh : 0 ≤ h) (huh : u < Real.exp (-h))
    (hq : 0 < q) (hσ : 1 < σ) (hsign : q + σ - 3 / 2 ≤ 0) (k : ℕ)
    (hr : degreeRate k h q σ < 1)
    (hS : ∀ N n, n ∈ S N → k ≤ (extremePrimes u N n).card) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) * ∑ n ∈ S N,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (eventually_norm_degree_sum_le S P y hu hh huh hq hσ hsign k hS)
  have hr0 : 0 ≤ degreeRate k h q σ := by unfold degreeRate; positivity
  simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr).mul_const
    (u * ZetaArithmeticLogWindow.tiltConstant P q σ)

/-- A logarithmic rate check proves the exact multiplicative rate is
strictly below one, avoiding numerical approximations in the conclusion. -/
theorem degreeRate_lt_one {k : ℕ} {h q σ : ℝ} (hq : 0 < q)
    (hlog : Real.log q⁻¹ + 2 * k * h * (q + σ - 3 / 2) - h < 0) :
    degreeRate k h q σ < 1 := by
  have he : degreeRate k h q σ =
      Real.exp (Real.log q⁻¹ + (2 * k * h * (q + σ - 3 / 2) - h)) := by
    rw [Real.exp_add, Real.exp_log (inv_pos.mpr hq)]
    rfl
  rw [he, Real.exp_lt_one_iff]
  linarith

/-- Two physical-cutoff primes already have a subunit geometric rate
on the smaller source interval u<exp(-2/3). -/
theorem two_degree_rate_lt_one : degreeRate 2 (2 / 3) (3 / 8) (257 / 256) < 1 := by
  apply degreeRate_lt_one (by norm_num)
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    simpa only [show (2 : ℝ) ^ 3 = 8 by norm_num, Nat.cast_ofNat] using
      (Real.log_pow (2 : ℝ) 3)
  norm_num only [inv_div, Nat.cast_ofNat]
  rw [Real.log_div (by norm_num) (by norm_num), hlog8]
  linarith [Real.log_two_lt_d9, Real.log_three_gt_d9]

/-- The literal two-or-more-extreme-prime arithmetic class vanishes on
0<u<exp(-2/3), uniformly in every changing finite selection and ordinate. -/
theorem tendsto_two_degree_sum (S : ℕ → Finset ℕ) (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ)))
    (hS : ∀ N n, n ∈ S N → 2 ≤ (extremePrimes u N n).card) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) * ∑ n ∈ S N,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) atTop (𝓝 0) := by
  exact tendsto_degree_sum S P y hu (by norm_num) huh
    (by norm_num : (0 : ℝ) < 3 / 8) (by norm_num : (1 : ℝ) < 257 / 256)
    (by norm_num) 2 two_degree_rate_lt_one hS

/-- Three physical-cutoff primes have a subunit geometric rate on
u<exp(-9/16), enlarging the source interval relative to the two-prime bound. -/
theorem three_degree_rate_lt_one : degreeRate 3 (9 / 16) (8 / 27) (257 / 256) < 1 := by
  apply degreeRate_lt_one (by norm_num)
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    simpa only [show (2 : ℝ) ^ 3 = 8 by norm_num, Nat.cast_ofNat] using
      (Real.log_pow (2 : ℝ) 3)
  have hlog27 : Real.log 27 = 3 * Real.log 3 := by
    simpa only [show (3 : ℝ) ^ 3 = 27 by norm_num, Nat.cast_ofNat] using
      (Real.log_pow (3 : ℝ) 3)
  norm_num only [inv_div, Nat.cast_ofNat]
  rw [Real.log_div (by norm_num) (by norm_num), hlog8, hlog27]
  linarith [Real.log_three_lt_d9, Real.log_two_gt_d9]

/-- The literal three-or-more-extreme-prime arithmetic class vanishes on
0<u<exp(-9/16), with every earlier coefficient and factorial shift retained. -/
theorem tendsto_three_degree_sum (S : ℕ → Finset ℕ) (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (huh : u < Real.exp (-(9 / 16 : ℝ)))
    (hS : ∀ N n, n ∈ S N → 3 ≤ (extremePrimes u N n).card) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) * ∑ n ∈ S N,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) atTop (𝓝 0) := by
  exact tendsto_degree_sum S P y hu (by norm_num) huh
    (by norm_num : (0 : ℝ) < 8 / 27) (by norm_num : (1 : ℝ) < 257 / 256)
    (by norm_num) 3 three_degree_rate_lt_one hS

/-- The two-prime rate is given by this exact closed expression. -/
theorem degree_two_rate_eq :
    degreeRate 2 (2 / 3) (3 / 8) (257 / 256) = (8 / 3 : ℝ) * Real.exp (-(95 / 96 : ℝ)) := by
  norm_num [degreeRate]

/-- The three-prime rate is given by this exact closed expression. -/
theorem degree_three_rate_eq :
    degreeRate 3 (9 / 16) (8 / 27) (257 / 256) = (27 / 8 : ℝ) * Real.exp (-(2533 / 2048 : ℝ)) := by
  norm_num [degreeRate]

end
end RiemannGaussian.ZetaRieszLowerDegreeBounds
