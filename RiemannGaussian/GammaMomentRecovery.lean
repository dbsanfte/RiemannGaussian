/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SignedLaplaceMoments
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Controlled recovery from signed factorial moments

The positive gamma kernel is exponentially small outside a fixed multiple
of its moment order, even after allowing exponential growth of the signal.
Consequently, diverging signed moments of a causal signal force positive
values in every sufficiently late interval `[n/16, 64*n]`. The tail estimate
uses only one actual weighted L1 integral. No pointwise growth estimate or
assumed recovery-time bound is needed.
-/

namespace RiemannGaussian
noncomputable section
open Filter MeasureTheory Set
open scoped Topology

/-- The literal nonnegative factorial kernel on positive time. -/
def factorialGammaKernel (n : ℕ) (t : ℝ) : ℝ :=
  t ^ n * Real.exp (-t) / (n.factorial : ℝ)

private def lowerRatio : ℝ := Real.exp (1 / 4) / 4
private def upperRatio : ℝ := 8 * Real.exp (-8)

private theorem lowerRatio_bounds : 0 ≤ lowerRatio ∧ lowerRatio < 1 := by
  constructor
  · exact (div_pos (Real.exp_pos _) (by norm_num)).le
  · unfold lowerRatio
    rw [div_lt_one (by norm_num)]
    have h := (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) / 4 ≤ 1)).trans_lt
      Real.exp_one_lt_three
    linarith

private theorem upperRatio_bounds : 0 ≤ upperRatio ∧ upperRatio < 1 := by
  constructor
  · unfold upperRatio
    positivity
  · unfold upperRatio
    rw [Real.exp_neg, mul_inv_lt_iff₀ (Real.exp_pos _)]
    linarith [Real.add_one_le_exp (8 : ℝ)]

private theorem lower_kernel_bound (n : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (htn : t ≤ (n : ℝ) / 16) :
    t ^ n * Real.exp (-t / 4) / (n.factorial : ℝ) ≤ lowerRatio ^ n := by
  have hn0 : 0 < (n.factorial : ℝ) := by positivity
  have h4 : 0 < (4 : ℝ) ^ n := by positivity
  have h := Real.pow_div_factorial_le_exp (4 * t) (show 0 ≤ 4 * t by positivity) n
  have hp : t ^ n / (n.factorial : ℝ) ≤ Real.exp (4 * t) / 4 ^ n := by
    rw [le_div_iff₀ h4]
    calc
      _ = (4 * t) ^ n / (n.factorial : ℝ) := by rw [mul_pow]; ring
      _ ≤ _ := h
  calc
    t ^ n * Real.exp (-t / 4) / (n.factorial : ℝ) ≤ t ^ n / (n.factorial : ℝ) := by
      apply div_le_div_of_nonneg_right _ hn0.le
      exact mul_le_of_le_one_right (pow_nonneg ht _) (Real.exp_le_one_iff.mpr (by linarith))
    _ ≤ Real.exp (4 * t) / 4 ^ n := hp
    _ ≤ Real.exp ((n : ℝ) * (1 / 4)) / 4 ^ n := by
      exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) h4.le
    _ = lowerRatio ^ n := by rw [Real.exp_nat_mul, lowerRatio, div_pow]

private theorem upper_kernel_bound (n : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (htn : 64 * (n : ℝ) ≤ t) :
    t ^ n * Real.exp (-t / 4) / (n.factorial : ℝ) ≤ upperRatio ^ n := by
  have h := Real.pow_div_factorial_le_exp (t / 8) (show 0 ≤ t / 8 by positivity) n
  have hp : t ^ n / (n.factorial : ℝ) ≤ 8 ^ n * Real.exp (t / 8) := by
    have h' := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ 8 ^ n by positivity)
    calc
      _ = 8 ^ n * ((t / 8) ^ n / (n.factorial : ℝ)) := by
        rw [div_pow]
        field_simp
      _ ≤ _ := h'
  calc
    t ^ n * Real.exp (-t / 4) / (n.factorial : ℝ) =
        (t ^ n / (n.factorial : ℝ)) * Real.exp (-t / 4) := by ring
    _ ≤ (8 ^ n * Real.exp (t / 8)) * Real.exp (-t / 4) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = 8 ^ n * Real.exp (-t / 8) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ 8 ^ n * Real.exp ((n : ℝ) * (-8)) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
    _ = upperRatio ^ n := by rw [Real.exp_nat_mul, upperRatio, mul_pow]

private theorem kernel_split (f : ℝ → ℝ) (n : ℕ) (t : ℝ) :
    f t * factorialGammaKernel n t =
      (f t * Real.exp (-(3 / 4 : ℝ) * t)) *
        (t ^ n * Real.exp (-t / 4) / (n.factorial : ℝ)) := by
  unfold factorialGammaKernel
  have he : Real.exp (-t) = Real.exp (-(3 / 4 : ℝ) * t) * Real.exp (-t / 4) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  ring

/-- Actual exponential integrability controls both discarded time tails
geometrically whenever the signal is nonpositive on the central interval. -/
theorem gammaMoment_le_geometric_tails_of_nonpositive_middle {f : ℝ → ℝ}
    (hf0 : ∀ t : ℝ, t ≤ 0 → f t = 0)
    (hi : Integrable (fun t : ℝ => f t * Real.exp (-(3 / 4 : ℝ) * t)))
    (n : ℕ) (hn : Integrable (fun t : ℝ => f t * factorialGammaKernel n t))
    (hmid : ∀ t ∈ Icc ((n : ℝ) / 16) (64 * (n : ℝ)), f t ≤ 0) :
    (∫ t : ℝ, f t * factorialGammaKernel n t) ≤
      ((Real.exp (1 / 4) / 4) ^ n + (8 * Real.exp (-8)) ^ n) *
        ∫ t : ℝ, ‖f t * Real.exp (-(3 / 4 : ℝ) * t)‖ := by
  have hq0 : 0 ≤ lowerRatio ^ n + upperRatio ^ n :=
    add_nonneg (pow_nonneg lowerRatio_bounds.1 _) (pow_nonneg upperRatio_bounds.1 _)
  have hb (t : ℝ) : f t * factorialGammaKernel n t ≤
      (lowerRatio ^ n + upperRatio ^ n) * ‖f t * Real.exp (-(3 / 4 : ℝ) * t)‖ := by
    by_cases ht : t ≤ 0
    · rw [hf0 t ht, zero_mul]
      positivity
    have ht0 : 0 ≤ t := (lt_of_not_ge ht).le
    by_cases hm : t ∈ Icc ((n : ℝ) / 16) (64 * (n : ℝ))
    · apply (mul_nonpos_of_nonpos_of_nonneg (hmid t hm) (by
        unfold factorialGammaKernel; positivity)).trans
      exact mul_nonneg hq0 (norm_nonneg _)
    have htail : t ^ n * Real.exp (-t / 4) / (n.factorial : ℝ) ≤
        lowerRatio ^ n + upperRatio ^ n := by
      rcases lt_or_ge t ((n : ℝ) / 16) with h | h
      · exact (lower_kernel_bound n ht0 h.le).trans (le_add_of_nonneg_right
          (pow_nonneg upperRatio_bounds.1 _))
      · have hu : 64 * (n : ℝ) ≤ t := (lt_of_not_ge (fun hh => hm ⟨h, hh⟩)).le
        exact (upper_kernel_bound n ht0 hu).trans (le_add_of_nonneg_left
          (pow_nonneg lowerRatio_bounds.1 _))
    rw [kernel_split]
    calc
      _ ≤ ‖f t * Real.exp (-(3 / 4 : ℝ) * t)‖ *
          (t ^ n * Real.exp (-t / 4) / (n.factorial : ℝ)) := by
        apply mul_le_mul_of_nonneg_right (Real.le_norm_self _) (by positivity)
      _ ≤ ‖f t * Real.exp (-(3 / 4 : ℝ) * t)‖ * (lowerRatio ^ n + upperRatio ^ n) :=
        mul_le_mul_of_nonneg_left htail (norm_nonneg _)
      _ = _ := mul_comm _ _
  have h := integral_mono hn (hi.norm.const_mul (lowerRatio ^ n + upperRatio ^ n)) hb
  rw [integral_const_mul] at h
  exact h

/-- Diverging signed factorial moments force a positive value at a
controlled time, for every sufficiently large moment order. -/
theorem eventually_exists_pos_in_gammaInterval {f : ℝ → ℝ}
    (hf0 : ∀ t : ℝ, t ≤ 0 → f t = 0)
    (hi : Integrable (fun t : ℝ => f t * Real.exp (-(3 / 4 : ℝ) * t)))
    (hn : ∀ n : ℕ, Integrable (fun t : ℝ => f t * factorialGammaKernel n t))
    (hm : Tendsto (fun n : ℕ => ∫ t : ℝ, f t * factorialGammaKernel n t) atTop atTop) :
    ∀ᶠ n : ℕ in atTop, ∃ t ∈ Icc ((n : ℝ) / 16) (64 * (n : ℝ)), 0 < f t := by
  have hq : Tendsto (fun n : ℕ =>
      (lowerRatio ^ n + upperRatio ^ n) *
        ∫ t : ℝ, ‖f t * Real.exp (-(3 / 4 : ℝ) * t)‖) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one lowerRatio_bounds.1 lowerRatio_bounds.2).add
      (tendsto_pow_atTop_nhds_zero_of_lt_one upperRatio_bounds.1 upperRatio_bounds.2)).mul_const
        (∫ t : ℝ, ‖f t * Real.exp (-(3 / 4 : ℝ) * t)‖)
  filter_upwards [hm.eventually (eventually_gt_atTop (1 : ℝ)),
    hq.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn1 hq1
  by_contra hnot
  push Not at hnot
  have hbound := gammaMoment_le_geometric_tails_of_nonpositive_middle hf0 hi n (hn n) hnot
  change _ ≤ (lowerRatio ^ n + upperRatio ^ n) * _ at hbound
  linarith

end
end RiemannGaussian
