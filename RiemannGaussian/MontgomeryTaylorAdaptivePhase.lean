/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.MontgomeryTaylorPhaseEnclosure

/-!
# Adaptive signed phase enclosures

The Taylor budget is computed from the actual angular interval. This works
for arbitrary interval widths and anchors, while retaining the common signed
linear term. Small anchor intervals automatically receive a smaller budget.
-/

namespace RiemannGaussian.MontgomeryTaylorAdaptivePhase
open LeanCert.Core LeanCert.Engine MontgomeryTaylorPhaseGrid
open MontgomeryTaylorPhaseEnclosure

/-- A rational upper bound for the absolute angular displacement. -/
def radius (n : ℕ) (X : IntervalDyadic) : ℚ :=
  max |(deltaInterval n X).lo.toRat| |(deltaInterval n X).hi.toRat|

/-- The explicit second-order and phase-data error budget. -/
def budget (n : ℕ) (X : IntervalDyadic) : ℚ :=
  radius n X ^ 2 / 2 + (1 / 10000000000000) * (1 + radius n X)

/-- The interval radius is nonnegative. -/
theorem radius_nonneg (n : ℕ) (X : IntervalDyadic) : 0 ≤ radius n X :=
  (abs_nonneg _).trans (le_max_left _ _)

/-- Every computed remainder budget is nonnegative. -/
theorem budget_nonneg (n : ℕ) (X : IntervalDyadic) : 0 ≤ budget n X := by
  unfold budget
  have hr := radius_nonneg n X
  positivity

/-- The outward-rounded interval for the signed remainder. -/
def remainderInterval (n : ℕ) (X : IntervalDyadic) : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat ⟨-budget n X, budget n X,
    by linarith [budget_nonneg n X]⟩ (-53)

/-- Any remainder within the mathematical budget belongs to its interval. -/
theorem remainder_mem {n : ℕ} {X : IntervalDyadic} {z : ℝ}
    (hz : |z| ≤ (budget n X : ℝ)) : z ∈ remainderInterval n X := by
  apply IntervalDyadic.mem_ofIntervalRat (prec := -53) (hprec := by norm_num)
  simpa only [IntervalRat.mem_def, Rat.cast_neg] using abs_le.mp hz

/-- The computed radius controls the actual angular displacement. -/
theorem abs_delta_le {n : ℕ} {x : ℝ} {X : IntervalDyadic} (hx : x ∈ X) :
    |Real.pi * (x - (n : ℝ) / 8000)| ≤ (radius n X : ℝ) := by
  have hd := delta_mem (n := n) hx
  have hl : -(radius n X : ℝ) ≤ ((deltaInterval n X).lo.toRat : ℝ) := by
    exact_mod_cast (abs_le.mp (le_max_left |(deltaInterval n X).lo.toRat|
      |(deltaInterval n X).hi.toRat|)).1
  have hu : ((deltaInterval n X).hi.toRat : ℝ) ≤ (radius n X : ℝ) := by
    exact_mod_cast (abs_le.mp (le_max_right |(deltaInterval n X).lo.toRat|
      |(deltaInterval n X).hi.toRat|)).2
  exact abs_le.mpr ⟨hl.trans hd.1, hd.2.trans hu⟩

/-- The error budget applies throughout any input interval, with no
fixed-width or sample-point assumption. -/
theorem phase_errors {n : ℕ} {c s x : ℝ} {X : IntervalDyadic}
    (hc : |c - Real.cos ((n : ℝ) * (Real.pi / 8000))| ≤ 1 / 10000000000000)
    (hs : |s - Real.sin ((n : ℝ) * (Real.pi / 8000))| ≤ 1 / 10000000000000)
    (hx : x ∈ X) :
    |Real.sin (Real.pi * x) - (s + c * (Real.pi * (x - (n : ℝ) / 8000)))| ≤
        (budget n X : ℝ) ∧
      |Real.cos (Real.pi * x) - (c - s * (Real.pi * (x - (n : ℝ) / 8000)))| ≤
        (budget n X : ℝ) := by
  have hd := abs_delta_le (n := n) hx
  have hr : (0 : ℝ) ≤ (radius n X : ℝ) := by exact_mod_cast radius_nonneg n X
  have hsq : (Real.pi * (x - (n : ℝ) / 8000)) ^ 2 ≤ (radius n X : ℝ) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (Real.pi * (x - (n : ℝ) / 8000))) hr).mpr hd
  have hb : (Real.pi * (x - (n : ℝ) / 8000)) ^ 2 / 2 +
      (1 / 10000000000000 : ℝ) * (1 + |Real.pi * (x - (n : ℝ) / 8000)|) ≤
        (budget n X : ℝ) := by
    simp only [budget, Rat.cast_add, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat,
      Rat.cast_mul, Rat.cast_one]
    linarith
  have heq : Real.pi * x - (n : ℝ) * (Real.pi / 8000) =
      Real.pi * (x - (n : ℝ) / 8000) := by ring
  have hsin := TrigonometricLinearEnclosure.sin_from_phase hc hs (Real.pi * x)
  have hcos := TrigonometricLinearEnclosure.cos_from_phase hc hs (Real.pi * x)
  rw [heq] at hsin hcos
  exact ⟨hsin.trans hb, hcos.trans hb⟩

/-- Sine enclosure using the interval's actual angular radius. -/
def sineInterval (n : ℕ) (c s : ℤ) (X : IntervalDyadic) : IntervalDyadic :=
  ((ratPoint ((s : ℚ) / scale)).add
    ((ratPoint ((c : ℚ) / scale)).mul (deltaInterval n X))).add (remainderInterval n X)

/-- Cosine enclosure with the opposite signed slope and the same budget. -/
def cosineInterval (n : ℕ) (c s : ℤ) (X : IntervalDyadic) : IntervalDyadic :=
  ((ratPoint ((c : ℚ) / scale)).sub
    ((ratPoint ((s : ℚ) / scale)).mul (deltaInterval n X))).add (remainderInterval n X)

/-- Both adaptive phase intervals contain the true trigonometric values
throughout the input interval. -/
theorem trig_mem {n : ℕ} {c s : ℤ} {x : ℝ} {X : IntervalDyadic}
    (hc : |(c : ℝ) / scale - Real.cos ((n : ℝ) * (Real.pi / 8000))| ≤ 1 / 10000000000000)
    (hs : |(s : ℝ) / scale - Real.sin ((n : ℝ) * (Real.pi / 8000))| ≤ 1 / 10000000000000)
    (hx : x ∈ X) :
    Real.sin (Real.pi * x) ∈ sineInterval n c s X ∧
      Real.cos (Real.pi * x) ∈ cosineInterval n c s X := by
  have he := phase_errors hc hs hx
  have hcn : (c : ℝ) / scale ∈ ratPoint ((c : ℚ) / scale) := by
    simpa only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using
      mem_ratPoint ((c : ℚ) / scale)
  have hsn : (s : ℝ) / scale ∈ ratPoint ((s : ℚ) / scale) := by
    simpa only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using
      mem_ratPoint ((s : ℚ) / scale)
  have hid (a b : ℝ) : a + (b - a) = b := by ring
  constructor
  · have hv := IntervalDyadic.mem_add
      (IntervalDyadic.mem_add hsn (IntervalDyadic.mem_mul hcn (delta_mem (n := n) hx)))
      (remainder_mem he.1)
    rw [hid] at hv
    exact hv
  · have hv := IntervalDyadic.mem_add
      (IntervalDyadic.mem_sub hcn (IntervalDyadic.mem_mul hsn (delta_mem (n := n) hx)))
      (remainder_mem he.2)
    rw [hid] at hv
    exact hv

end RiemannGaussian.MontgomeryTaylorAdaptivePhase
