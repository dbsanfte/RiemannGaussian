/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.EtaOddPowerQuadrature
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Exact Euler cells for ordinary zeta truncation

The first Euler--Maclaurin remainder keeps the original complex power
on every unit cell. Multiplying a cell by `1-s` gives an entire expression
in `s`, so the pole can be cleared before analytic continuation. This is
the initial bridge for the direct truncation argument in Yang, section 3.2
(https://arxiv.org/html/2301.03165v2), not his sharp remainder estimate.
-/

namespace RiemannGaussian.ZetaEulerCell
noncomputable section
open Complex Filter MeasureTheory Metric Set Topology
open scoped Interval

/-- The original ordinary Dirichlet partialSum, including every index up
to its integer cutoff. -/
def partialSum (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, (n + 1 : ℂ) ^ (-s)

/-- The exact complex difference between a power and its unit-cell
integral; neither its phase nor its sign is removed. -/
def cell (s : ℂ) (n : ℕ) : ℂ :=
  (n + 1 : ℂ) ^ (-s) - ∫ x : ℝ in (n + 1 : ℝ)..(n + 2 : ℝ), (x : ℂ) ^ (-s)

/-- Clearing the pole produces an entire cell expression, including
at the original pole coordinate. -/
def regularizedCell (s : ℂ) (n : ℕ) : ℂ :=
  (1 - s) * (n + 1 : ℂ) ^ (-s) -
    (n + 2 : ℂ) ^ (1 - s) + (n + 1 : ℂ) ^ (1 - s)

/-- The literal power is integrable on each positive unit cell. -/
theorem intervalIntegrable_power (s : ℂ) (n : ℕ) :
    IntervalIntegrable (fun x : ℝ ↦ (x : ℂ) ^ (-s)) volume (n + 1 : ℝ) (n + 2 : ℝ) := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.cpow_const continuous_ofReal.continuousOn
  intro x hx
  rw [uIcc_of_le (by linarith : (n + 1 : ℝ) ≤ n + 2)] at hx
  exact Complex.ofReal_mem_slitPlane.mpr (by linarith [Nat.cast_nonneg (α := ℝ) n, hx.1])

/-- The cell integral has its exact complex endpoint expression away
from the pole; the denominator is not bounded or replaced. -/
theorem integral_power {s : ℂ} (hs : s ≠ 1) (n : ℕ) :
    (∫ x : ℝ in (n + 1 : ℝ)..(n + 2 : ℝ), (x : ℂ) ^ (-s)) =
      ((n + 2 : ℂ) ^ (1 - s) - (n + 1 : ℂ) ^ (1 - s)) / (1 - s) := by
  have h := integral_cpow (a := (n + 1 : ℝ)) (b := (n + 2 : ℝ)) (r := -s)
    (Or.inr ⟨by simpa using hs, by
      rw [uIcc_of_le (by linarith : (n + 1 : ℝ) ≤ n + 2)]
      simp only [mem_Icc, not_and]
      intro h
      linarith [Nat.cast_nonneg (α := ℝ) n]⟩)
  simpa only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one,
    Complex.ofReal_ofNat, show -s + 1 = 1 - s by ring] using h

/-- The entire cell equals the pole factor times the original complex
quadrature cell, also at the pole itself. -/
theorem regularizedCell_eq (s : ℂ) (n : ℕ) :
    regularizedCell s n = (1 - s) * cell s n := by
  by_cases hs : s = 1
  · subst s
    simp [regularizedCell]
  · unfold regularizedCell cell
    rw [integral_power hs]
    field_simp
    ring

/-- Every regularized cell is entire in the zeta argument. -/
theorem differentiable_regularizedCell (n : ℕ) :
    Differentiable ℂ (fun s ↦ regularizedCell s n) := by
  unfold regularizedCell
  have h1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (show n + 1 ≠ 0 by omega)
  have h2 : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast (show n + 2 ≠ 0 by omega)
  have hlin : Differentiable ℂ (fun s : ℂ ↦ 1 - s) := by fun_prop
  exact ((hlin.mul (differentiable_neg.const_cpow (Or.inl h1))).sub
    (hlin.const_cpow (Or.inl h2))).add (hlin.const_cpow (Or.inl h1))

/-- The exact quadrature error has a summable derivative envelope
throughout the positive half-plane. -/
theorem norm_cell_le {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖cell s n‖ ≤ ‖s‖ * (n + 1 : ℝ) ^ (-s.re - 1) := by
  have hn : 0 < (n + 1 : ℝ) := by positivity
  have he : cell s n = ∫ x : ℝ in (n + 1 : ℝ)..(n + 2 : ℝ),
      ((n + 1 : ℂ) ^ (-s) - (x : ℂ) ^ (-s)) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const (intervalIntegrable_power s n),
      intervalIntegral.integral_const]
    simp only [show (n + 2 : ℝ) - (n + 1) = 1 by ring, one_smul]
    rfl
  rw [he]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (n + 1 : ℝ)) (b := (n + 2 : ℝ))
    (f := fun x ↦ (n + 1 : ℂ) ^ (-s) - (x : ℂ) ^ (-s))
    (C := ‖s‖ * (n + 1 : ℝ) ^ (-s.re - 1)) (by
      intro x hx
      rw [uIoc_of_le (by linarith : (n + 1 : ℝ) ≤ n + 2)] at hx
      have h := norm_cpow_sub_cpow_le_above (-s) hn
        (by simp only [neg_re]; linarith) hx.1.le (le_refl _)
      have hd : |(n + 1 : ℝ) - x| ≤ 1 := abs_le.mpr ⟨by linarith [hx.2], by linarith [hx.1]⟩
      simp only [norm_neg, neg_re, Complex.ofReal_add, Complex.ofReal_natCast,
        Complex.ofReal_one] at h
      exact h.trans (by nlinarith [mul_nonneg (norm_nonneg s) (Real.rpow_nonneg hn.le (-s.re - 1))]))
  simpa only [show (n + 2 : ℝ) - (n + 1) = 1 by ring, abs_one, mul_one] using hb

/-- The common power envelope is summable for every positive real
exponent, uniformly available to the analytic continuation argument. -/
theorem summable_envelope {p : ℝ} (hp : 0 < p) :
    Summable (fun n : ℕ ↦ (n + 1 : ℝ) ^ (-p - 1)) := by
  have h := (Real.summable_one_div_nat_add_rpow 1 (p + 1)).mpr (by linarith)
  apply h.congr
  intro n
  rw [abs_of_nonneg (by positivity), one_div, ← Real.rpow_neg (by positivity)]
  congr 1
  ring

/-- The original complex Euler cells converge absolutely throughout
the positive half-plane, before their phases are bounded. -/
theorem summable_cell {s : ℂ} (hs : 0 < s.re) : Summable (cell s) :=
  ((summable_envelope hs).mul_left ‖s‖).of_norm_bounded (norm_cell_le hs)

/-- The regularized entire cells form an absolutely convergent series
on the same full positive half-plane. -/
theorem summable_regularizedCell {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n ↦ regularizedCell s n) := by
  simpa only [regularizedCell_eq] using (summable_cell hs).mul_left (1 - s)

/-- Every finite regularized partialSum telescopes exactly, retaining
both the original Dirichlet sum and its complex upper endpoint. -/
theorem sum_regularizedCell (N : ℕ) (s : ℂ) :
    (∑ n ∈ Finset.range N, regularizedCell s n) =
      (1 - s) * partialSum N s - (N + 1 : ℂ) ^ (1 - s) + 1 := by
  induction N with
  | zero => simp [partialSum]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [partialSum, Finset.sum_range_succ, regularizedCell, Nat.cast_add, Nat.cast_one]
      have he : (N : ℂ) + 1 + 1 = N + 2 := by ring
      rw [he]
      ring

end
end RiemannGaussian.ZetaEulerCell
