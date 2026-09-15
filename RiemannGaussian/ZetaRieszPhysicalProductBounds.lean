/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszIntermediatePrimeSupport

/-!
# Independent bounds by the full physical product

The exact degree-dependent tilt pays all labels above the corresponding
physical product threshold, regardless of their prime counts. In particular,
the whole n>=X_N^2 class decays for 0<u<exp(-2/3), with the original coefficient,
physical floor, fixed factorial filter and arbitrary finite selections.
Every coefficient below X_N is exactly zero. Below X_N^2, a nonzero label
with an extreme prime has a prime cofactor below X_N, with its exact signed
semiprime coefficient. These estimates do not bound the remaining joint sum.
-/

namespace RiemannGaussian.ZetaRieszPhysicalProductBounds
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszLowerDegreeBounds ZetaRieszLowerDegreeDeletion

/-- An independently proved arithmetic estimate for any physical product threshold
and admissible tilt. Decay requires this explicit rate to be below one. -/
theorem eventually_norm_physical_product_sum_le (S : ℕ → Finset ℕ) (P : Polynomial ℂ) (y : ℝ)
    {u h q σ : ℝ} (hu : 0 < u) (hh : 0 ≤ h) (huh : u < Real.exp (-h))
    (hq : 0 < q) (hσ : 1 < σ) (hsign : q + σ - 3 / 2 ≤ 0) (k : ℕ)
    (hS : ∀ N n, n ∈ S N → (k : ℝ) * SquarefreeVaughanLogSource.length u N ≤ Real.log n) :
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
  have hb := ZetaArithmeticLogWindow.norm_sum_filter_of_log_bound (S N)
    (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N))
    (fun n _ => SquarefreeVaughanLogSource.norm_coefficient_le
      (SquarefreeVaughanLogSource.length_pos u N) n) P N y σ q a hσ hq (by
      intro n hn
      have hkN := mul_le_mul_of_nonneg_left hLN (show (0 : ℝ) ≤ k by positivity)
      have hlog : (2 * k * h) * N ≤ Real.log n := by nlinarith [hS N n hn]
      have he' := mul_le_mul_of_nonpos_left hlog hsign
      dsimp only [a]
      nlinarith only [he'])
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
  calc
    _ ≤ u ^ (N + 1) * ((q⁻¹ * Real.exp a) ^ N * ZetaArithmeticLogWindow.tiltConstant P q σ) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (u * (q⁻¹ * Real.exp a)) ^ N * (u * ZetaArithmeticLogWindow.tiltConstant P q σ) := by
      rw [pow_succ, mul_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hr N)
      (mul_nonneg hu.le hC)

/-- Every actual label above the k-th power of the physical cutoff
has the exact logarithmic product budget, including the integer floor. -/
theorem physical_product_log_budget {u : ℝ} {N n k : ℕ}
    (hn : ((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ^ k ≤ n) :
    (k : ℝ) * SquarefreeVaughanLogSource.length u N ≤ Real.log n := by
  have hcast : (((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 : ℕ) : ℝ) ^ k ≤ (n : ℝ) :=
    by exact_mod_cast hn
  have h := Real.log_le_log (by positivity) hcast
  simpa only [SquarefreeVaughanLogSource.length, Nat.cast_pow, Nat.cast_add,
    Nat.cast_ofNat, Real.log_pow] using h

/-- A checked subunit degree rate also pays every actual label above
the corresponding physical product threshold, without a prime-count restriction. -/
theorem tendsto_physical_product_sum (S : ℕ → Finset ℕ) (P : Polynomial ℂ) (y : ℝ)
    {u h q σ : ℝ} (hu : 0 < u) (hh : 0 ≤ h) (huh : u < Real.exp (-h))
    (hq : 0 < q) (hσ : 1 < σ) (hsign : q + σ - 3 / 2 ≤ 0) (k : ℕ)
    (hr : degreeRate k h q σ < 1)
    (hS : ∀ N n, n ∈ S N → ((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ^ k ≤ n) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) * ∑ n ∈ S N,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (eventually_norm_physical_product_sum_le S P y hu hh huh hq hσ hsign k
    (fun N n hn => physical_product_log_budget (hS N n hn)))
  have hr0 : 0 ≤ degreeRate k h q σ := by unfold degreeRate; positivity
  simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr).mul_const
    (u * ZetaArithmeticLogWindow.tiltConstant P q σ)

/-- The entire actual class n>=X_N^2 vanishes at source scale for
0<u<exp(-2/3), uniformly in the ordinate and changing finite selection. -/
theorem tendsto_above_physical_square (S : ℕ → Finset ℕ) (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ)))
    (hS : ∀ N n, n ∈ S N → ((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ^ 2 ≤ n) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) * ∑ n ∈ S N,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) atTop (𝓝 0) := by
  exact tendsto_physical_product_sum S P y hu (by norm_num) huh
    (by norm_num : (0 : ℝ) < 3 / 8) (by norm_num : (1 : ℝ) < 257 / 256)
    (by norm_num) 2 two_degree_rate_lt_one hS

/-- At or below the physical cutoff every actual Riesz coefficient is
exactly zero. Prime labels and the unit retain their original deletion. -/
theorem coefficient_eq_zero_below_physical {u : ℝ} {N n : ℕ}
    (hn : n ≤ (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n = 0 := by
  by_cases hs : Squarefree n
  · by_cases hp : n.Prime
    · simp [SquarefreeVaughanLogSource.coefficient, hp]
    · by_cases h1 : n = 1
      · simp [SquarefreeVaughanLogSource.coefficient, h1]
      · have hL : Real.log n ≤ SquarefreeVaughanLogSource.length u N := by
          apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hs.ne_zero)
          exact_mod_cast hn
        rw [SquarefreeVaughanLogSource.coefficient, if_pos ⟨hs, hp⟩,
          ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated hs h1 hp hL]
        simp
  · simp [SquarefreeVaughanLogSource.coefficient, hs]

/-- A whole arbitrary finite response may discard its physical lower
prefix exactly, before taking any norm or limit. -/
theorem sum_filter_physical_lower (S : Finset ℕ) (f : ℕ → ℂ) (u : ℝ) (N : ℕ) :
    (∑ n ∈ S.filter (fun n => (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 < n),
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n * f n) =
    ∑ n ∈ S, SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n * f n := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 < n
  · simp only [if_pos hn]
  · rw [if_neg hn, coefficient_eq_zero_below_physical (le_of_not_gt hn), zero_mul]

/-- A nonzero actual label below X_N^2 with an extreme prime factor
must be a semiprime. The entire cofactor is forced to be a prime below X_N. -/
theorem nonzero_extreme_below_square_is_semiprime {u : ℝ} {N n p : ℕ}
    (hp : p.Prime) (hpn : p ∣ n)
    (hpX : (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ p)
    (hnX : n < ((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ^ 2)
    (hc : SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n ≠ 0) :
    ∃ a : ℕ, a.Prime ∧ a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ∧
      n = p * a ∧ ¬ p ∣ a ∧
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n =
        ((-Real.log n * Real.log a / SquarefreeVaughanLogSource.length u N : ℝ) : ℂ) := by
  obtain ⟨a, rfl⟩ := hpn
  have hfull : Squarefree (p * a) := by
    by_contra hs
    exact hc (by simp [SquarefreeVaughanLogSource.coefficient, hs])
  have haX : a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 := by
    by_contra h
    have hm := Nat.mul_le_mul hpX (le_of_not_gt h)
    rw [← pow_two] at hm
    omega
  have ha1 : a ≠ 1 := by
    intro h
    subst a
    exact hc (by simp [SquarefreeVaughanLogSource.coefficient, hp])
  have hlarge : ∀ q ∈ p.primeFactors,
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ q := by
    intro q hq
    have hqp : q = p := (Nat.dvd_prime hp).mp (Nat.dvd_of_mem_primeFactors hq) |>.resolve_left
      (Nat.prime_of_mem_primeFactors hq).ne_one
    simpa only [hqp] using hpX
  have hap : a.Prime := by
    by_contra ha
    exact hc (ZetaRieszExtremePrimeProfile.coefficient_eq_zero_of_physical_extreme
      hfull ha1 ha haX.le hlarge)
  have hpa : ¬ p ∣ a := hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hfull)
  refine ⟨a, hap, haX, rfl, hpa, ?_⟩
  apply ZetaRieszFixedCofactor.coefficient_prime_pair_above_cutoff hap hp hpa
  · apply Real.log_le_log (by exact_mod_cast hap.pos)
    exact_mod_cast haX.le
  · apply Real.log_le_log (by positivity)
    exact_mod_cast hpX

end
end RiemannGaussian.ZetaRieszPhysicalProductBounds
