/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszExtremeDegreeBounds

/-!
# Source-normalized decay of the actual four-extreme-prime class

Keeping u^(N+1) inside the estimate pays the entire class with at least
four prime factors at or above X_N, for 0<u<exp(-1/2). Its explicit
geometric rate is 4*exp(-23/16)<1. This reaches degrees four and five
inside the already narrowed window. Actual coefficients, arbitrary finite
selections, full product phases and all fixed factorial shifts are kept.
No zero premise or whole-residual lower bound is assumed or proved here.
-/

namespace RiemannGaussian.ZetaRieszFourExtremeBound
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszExtremePrimeCount
open ZetaRieszExtremeDegreeBounds

/-- The source-normalized rate for four physical-cutoff prime factors
on the complete-composite interval. -/
def fourRate : ℝ := 4 * Real.exp (-(23 / 16 : ℝ))

/-- The four-prime rate is positive and strictly below one. -/
theorem fourRate_mem : 0 < fourRate ∧ fourRate < 1 := by
  refine ⟨by unfold fourRate; positivity, ?_⟩
  have hlog : 2 * Real.log 2 < (23 / 16 : ℝ) := by linarith [Real.log_two_lt_d9]
  have he := Real.exp_lt_exp.mpr hlog
  have h2 := Real.exp_nat_mul (Real.log 2) 2
  norm_num only [Nat.cast_ofNat] at h2
  rw [h2, Real.exp_log (by norm_num)] at he
  norm_num at he
  calc
    fourRate < Real.exp (23 / 16 : ℝ) * Real.exp (-(23 / 16 : ℝ)) :=
      mul_lt_mul_of_pos_right he (Real.exp_pos _)
    _ = 1 := by rw [← Real.exp_add]; norm_num

/-- Keeping the source factor pays the whole actual four-or-more-extreme
prime class, including terms inside the previously retained window. The
bound preserves arbitrary finite selections and all fixed filter shifts. -/
theorem eventually_norm_four_extreme_sum_le (S : ℕ → Finset ℕ) (P : Polynomial ℂ)
    (y : ℝ) {u : ℝ} (hu : 0 < u) (hcontact : u < Real.exp (-(1 / 2 : ℝ)))
    (hS : ∀ N n, n ∈ S N → 4 ≤ (extremePrimes u N n).card) :
    ∀ᶠ N : ℕ in atTop,
      ‖(u : ℂ) ^ (N + 1) *
        ∑ n ∈ S N, SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
        fourRate ^ N * (u * ZetaArithmeticLogWindow.tiltConstant P (1 / 4) (65 / 64)) := by
  have hC := ZetaArithmeticLogWindow.tiltConstant_nonneg P (σ := (65 / 64 : ℝ))
    (by norm_num : (0 : ℝ) < 1 / 4)
  have hr : u * (4 * Real.exp (-(15 / 16 : ℝ))) ≤ fourRate := by
    calc
      _ ≤ Real.exp (-(1 / 2 : ℝ)) * (4 * Real.exp (-(15 / 16 : ℝ))) :=
        mul_le_mul_of_nonneg_right hcontact.le (by positivity)
      _ = fourRate := by
        rw [mul_left_comm, ← Real.exp_add]
        norm_num [fourRate]
  filter_upwards [eventually_length_ge_order hu hcontact] with N hLN
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
      (SquarefreeVaughanLogSource.length_pos u N) n) P N y (65 / 64) (1 / 4) (-(15 / 16 : ℝ))
    (by norm_num) (by norm_num) (by
      intro n hn
      have hs := (Finset.mem_filter.mp hn).2
      have hc : (4 : ℝ) ≤ (extremePrimes u N n).card := by
        exact_mod_cast hS N n (Finset.mem_filter.mp hn).1
      have hmass := extreme_prime_log_budget u N hs
      have hh := mul_le_mul_of_nonneg_right hc (SquarefreeVaughanLogSource.length_pos u N).le
      nlinarith)
  norm_num only [one_div, inv_inv] at hb
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu, he]
  calc
    _ ≤ u ^ (N + 1) * ((4 * Real.exp (-(15 / 16 : ℝ))) ^ N *
        ZetaArithmeticLogWindow.tiltConstant P (1 / 4) (65 / 64)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (u * (4 * Real.exp (-(15 / 16 : ℝ)))) ^ N *
        (u * ZetaArithmeticLogWindow.tiltConstant P (1 / 4) (65 / 64)) := by
      rw [pow_succ, mul_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hr N)
      (mul_nonneg hu.le hC)

/-- The entire actual four-or-more-extreme-prime class has vanishing
source-normalized response. This independently pays two further finite
extreme degrees inside the smaller window, on the stated source interval. -/
theorem tendsto_four_extreme_sum (S : ℕ → Finset ℕ) (P : Polynomial ℂ)
    (y : ℝ) {u : ℝ} (hu : 0 < u) (hcontact : u < Real.exp (-(1 / 2 : ℝ)))
    (hS : ∀ N n, n ∈ S N → 4 ≤ (extremePrimes u N n).card) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      ∑ n ∈ S N, SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (eventually_norm_four_extreme_sum_le S P y hu hcontact hS)
  simpa only [zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one fourRate_mem.1.le fourRate_mem.2).mul_const
      (u * ZetaArithmeticLogWindow.tiltConstant P (1 / 4) (65 / 64))

end
end RiemannGaussian.ZetaRieszFourExtremeBound
