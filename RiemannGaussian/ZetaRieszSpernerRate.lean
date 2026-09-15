/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSperner
import Mathlib.Data.Nat.Choose.Central

/-!
# An explicit square-root gain in the middle layer

Quantify the combinatorial saving while retaining the original signed
coefficient bounds as their upstream theorem.
-/

namespace RiemannGaussian.ZetaRieszSpernerRate
noncomputable section
open scoped BigOperators Classical

/-- The elementary central-binomial recurrence already gives a
square-root saving over the full Boolean mass, at every even count. -/
theorem centralBinom_sq_bound (n : ℕ) :
    (n.centralBinom : ℝ) ^ 2 * (2 * n + 1) ≤ (16 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have he : ((n : ℝ) + 1) * ((n + 1).centralBinom : ℝ) =
        2 * (2 * n + 1) * (n.centralBinom : ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ n
    have hN : 0 < ((n : ℝ) + 1) ^ 2 := by positivity
    apply (mul_le_mul_iff_left₀ hN).mp
    calc
      _ = (((n : ℝ) + 1) * ((n + 1).centralBinom : ℝ)) ^ 2 * (2 * n + 3) := by
        push_cast
        ring
      _ = (4 * ((2 * n + 1) * (2 * n + 3))) *
          ((n.centralBinom : ℝ) ^ 2 * (2 * n + 1)) := by rw [he]; ring
      _ ≤ (4 * ((2 * n + 1) * (2 * n + 3))) * (16 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ ≤ (((n : ℝ) + 1) ^ 2) * (16 : ℝ) ^ (n + 1) := by
        rw [pow_succ (16 : ℝ) n]
        have hh : (2 * (n : ℝ) + 1) * (2 * n + 3) ≤ 4 * (n + 1) ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hh (show 0 ≤ (16 : ℝ) ^ n by positivity)]
      _ = _ := by ring

/-- Odd middle layers retain the same square-root saving, with the
exact adjacent-row binomial identity supplying their normalization. -/
theorem odd_middle_choose_sq_bound (n : ℕ) :
    ((2 * n + 1).choose n : ℝ) ^ 2 * (2 * n + 2) ≤ (4 : ℝ) ^ (2 * n + 1) := by
  have he : (n.centralBinom : ℝ) * (2 * n + 1) =
      ((2 * n + 1).choose n : ℝ) * (n + 1) := by
    have hh := Nat.choose_mul_succ_eq (2 * n) n
    rw [show 2 * n + 1 - n = n + 1 by omega] at hh
    exact_mod_cast hh
  have hN : 0 < ((n : ℝ) + 1) ^ 2 := by positivity
  have hp : (4 : ℝ) ^ (2 * n + 1) = 4 * (16 : ℝ) ^ n := by
    rw [pow_add, pow_mul]
    norm_num
    ring
  apply (mul_le_mul_iff_left₀ hN).mp
  calc
    _ = (((2 * n + 1).choose n : ℝ) * ((n : ℝ) + 1)) ^ 2 * (2 * n + 2) := by ring
    _ = ((n.centralBinom : ℝ) ^ 2 * (2 * n + 1)) * ((2 * n + 1) * (2 * n + 2)) := by
      rw [← he]
      ring
    _ ≤ (16 : ℝ) ^ n * ((2 * n + 1) * (2 * n + 2)) :=
      mul_le_mul_of_nonneg_right (centralBinom_sq_bound n) (by positivity)
    _ ≤ (16 : ℝ) ^ n * (4 * ((n : ℝ) + 1) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    _ = _ := by rw [hp]; ring

/-- A uniform middle-layer square-root estimate for every prime count,
with both parity cases checked by exact binomial recurrences. -/
theorem middle_choose_sq_bound (k : ℕ) :
    (k.choose (k / 2) : ℝ) ^ 2 * (k + 1) ≤ (4 : ℝ) ^ k := by
  have hk : k = 2 * (k / 2) ∨ k = 2 * (k / 2) + 1 := by omega
  rcases hk with hk | hk
  · have h := centralBinom_sq_bound (k / 2)
    have he : (4 : ℝ) ^ (2 * (k / 2)) = (16 : ℝ) ^ (k / 2) := by rw [pow_mul]; norm_num
    have hreal : 2 * ((k / 2 : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast hk.symm
    rw [← he] at h
    simpa only [Nat.centralBinom, ← hk, hreal] using h
  · have h := odd_middle_choose_sq_bound (k / 2)
    have hreal : 2 * ((k / 2 : ℕ) : ℝ) + 2 = (k : ℝ) + 1 := by
      have hh : (k : ℝ) = 2 * ((k / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hk
      linarith
    simpa only [← hk, hreal] using h

/-- The middle binomial coefficient saves a square root compared with
all subsets, at every count including zero. -/
theorem middle_choose_le (k : ℕ) :
    (k.choose (k / 2) : ℝ) ≤ (2 : ℝ) ^ k / Real.sqrt (k + 1) := by
  have hs : 0 < Real.sqrt ((k : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  apply (le_div_iff₀ hs).mpr
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (k : ℝ) + 1)]
  have he : ((2 : ℝ) ^ k) ^ 2 = (4 : ℝ) ^ k := by
    rw [pow_two, ← mul_pow]
    norm_num
  rw [he]
  exact middle_choose_sq_bound k

/-- Keeping the middle-layer square-root saving yields a count factor
of 2k times sqrt(k-1), uniformly over every admissible prime count. -/
theorem middle_layer_le_root_saving {k : ℕ} (hk : 2 ≤ k) :
    (2 : ℝ) * ((k - 2).choose ((k - 2) / 2) : ℝ) / k ≤
      (2 : ℝ) ^ k / (2 * k * Real.sqrt ((k - 1 : ℕ) : ℝ)) := by
  have hc := middle_choose_le (k - 2)
  have hcast : ((k - 2 : ℕ) : ℝ) + 1 = ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show (k - 2) + 1 = k - 1 by omega)
  rw [hcast] at hc
  have hp : (2 : ℝ) ^ k = 4 * (2 : ℝ) ^ (k - 2) := by
    calc
      _ = (2 : ℝ) ^ ((k - 2) + 2) := by rw [Nat.sub_add_cancel hk]
      _ = _ := by rw [pow_add]; norm_num; ring
  calc
    _ ≤ 2 * ((2 : ℝ) ^ (k - 2) / Real.sqrt ((k - 1 : ℕ) : ℝ)) / k := by gcongr
    _ = _ := by rw [hp]; ring

/-- The original central coefficient retains the full square-root
antichain gain. This is a height-independent bound for actual arithmetic
atoms, not a decay estimate for the sum across different integers. -/
theorem norm_actual_central_coefficient_le_root_saving {u : ℝ} {N n : ℕ}
    (huh : u < Real.exp (-(2 / 3 : ℝ)))
    (hn : n ∈ ZetaRieszCentralPrimeLayers.centralUnpairedBand u N) :
    ‖SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n‖ ≤
      Real.log n * ((2 : ℝ) ^ n.primeFactors.card /
        (2 * n.primeFactors.card * Real.sqrt ((n.primeFactors.card - 1 : ℕ) : ℝ))) := by
  by_cases hc : SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n = 0
  · rw [hc, norm_zero]
    have := Real.log_natCast_nonneg n
    positivity
  · have hs := ZetaRieszSperner.coefficient_ne_zero_support hc
    exact (ZetaRieszSperner.norm_actual_central_coefficient_le huh hn).trans
      (mul_le_mul_of_nonneg_left (middle_layer_le_root_saving hs.2) (Real.log_natCast_nonneg n))

end
end RiemannGaussian.ZetaRieszSpernerRate
