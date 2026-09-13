/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.MontgomeryTaylorPhaseTable
import RiemannGaussian.TrigonometricLinearEnclosure
import RiemannGaussian.MontgomeryTaylorKernelEnclosure

/-!
# Continuous interval enclosures from the periodic phase table

A single phase controls its entire neighboring cell. These enclosures use
only rational arithmetic after the phase certificate, and so also apply to
arbitrary rational anchors chosen by an untrusted numerical optimizer.
-/

namespace RiemannGaussian.MontgomeryTaylorPhaseEnclosure
open LeanCert.Core LeanCert.Engine MontgomeryTaylorPhaseGrid

/-- Outward-rounded interval containing a rational point. -/
def ratPoint (q : ℚ) : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat (IntervalRat.singleton q) (-53)

/-- Exact containment of the rational input despite outward rounding. -/
theorem mem_ratPoint (q : ℚ) : (q : ℝ) ∈ ratPoint q :=
  IntervalDyadic.mem_ofIntervalRat (IntervalRat.mem_singleton q) (-53) (by norm_num)

/-- A fixed enclosure for pi; its correctness is proved in Mathlib. -/
def piInterval : IntervalDyadic := IntervalDyadic.ofIntervalRat
  ⟨31415926535897932 / 10000000000000000, 31415926535897933 / 10000000000000000,
    by norm_num⟩ (-53)

/-- The true pi belongs to the fixed interval. -/
theorem pi_mem : Real.pi ∈ piInterval := by
  apply IntervalDyadic.mem_ofIntervalRat (prec := -53) (hprec := by norm_num)
  change ((31415926535897932 / 10000000000000000 : ℚ) : ℝ) ≤ Real.pi ∧
    Real.pi ≤ ((31415926535897933 / 10000000000000000 : ℚ) : ℝ)
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  constructor <;> linarith [Real.pi_gt_d20, Real.pi_lt_d20]

/-- The common Taylor and phase-data error budget. -/
def errorInterval : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat ⟨-1 / 10000000, 1 / 10000000, by norm_num⟩ (-53)

/-- Absolute error bounds embed in the error interval. -/
theorem mem_errorInterval {x : ℝ} (hx : |x| ≤ 1 / 10000000) : x ∈ errorInterval := by
  apply IntervalDyadic.mem_ofIntervalRat (prec := -53) (hprec := by norm_num)
  simpa only [IntervalRat.mem_def, Rat.cast_div, Rat.cast_neg, Rat.cast_one,
    Rat.cast_ofNat, neg_div] using abs_le.mp hx

/-- Uniform signed Taylor enclosures on a complete grid cell. -/
theorem nearby_error {n : ℕ} {c s x : ℝ}
    (hc : |c - Real.cos ((n : ℝ) * (Real.pi / 8000))| ≤ 1 / 10000000000000)
    (hs : |s - Real.sin ((n : ℝ) * (Real.pi / 8000))| ≤ 1 / 10000000000000)
    (hx : |x - (n : ℝ) / 8000| ≤ 1 / 8000) :
    |Real.sin (Real.pi * x) - (s + c * (Real.pi * (x - (n : ℝ) / 8000)))| ≤
        1 / 10000000 ∧
      |Real.cos (Real.pi * x) - (c - s * (Real.pi * (x - (n : ℝ) / 8000)))| ≤
        1 / 10000000 := by
  have hd : |Real.pi * (x - (n : ℝ) / 8000)| ≤ (1 : ℝ) / 2500 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    calc
      _ ≤ (16 / 5 : ℝ) * (1 / 8000) :=
        mul_le_mul (by linarith [Real.pi_lt_d20]) hx (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hsq : (Real.pi * (x - (n : ℝ) / 8000)) ^ 2 ≤ ((1 : ℝ) / 2500) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (Real.pi * (x - (n : ℝ) / 8000))) (by norm_num)).mpr hd
  have hb : (Real.pi * (x - (n : ℝ) / 8000)) ^ 2 / 2 +
      (1 / 10000000000000 : ℝ) * (1 + |Real.pi * (x - (n : ℝ) / 8000)|) ≤
        1 / 10000000 := by linarith
  have heq : Real.pi * x - (n : ℝ) * (Real.pi / 8000) =
      Real.pi * (x - (n : ℝ) / 8000) := by ring
  have hsin := TrigonometricLinearEnclosure.sin_from_phase hc hs (Real.pi * x)
  have hcos := TrigonometricLinearEnclosure.cos_from_phase hc hs (Real.pi * x)
  rw [heq] at hsin hcos
  exact ⟨hsin.trans hb, hcos.trans hb⟩

/-- Enclosure of the signed angular displacement from the chosen phase. -/
def deltaInterval (n : ℕ) (X : IntervalDyadic) : IntervalDyadic :=
  (piInterval.mul (X.sub (ratPoint ((n : ℚ) / 8000)))).roundOut (-53)

/-- Certified sine interval, retaining the cosine as the signed slope. -/
def sineInterval (n : ℕ) (c s : ℤ) (X : IntervalDyadic) : IntervalDyadic :=
  ((ratPoint ((s : ℚ) / scale)).add
    ((ratPoint ((c : ℚ) / scale)).mul (deltaInterval n X))).add errorInterval

/-- Certified cosine interval, retaining the negative sine slope. -/
def cosineInterval (n : ℕ) (c s : ℤ) (X : IntervalDyadic) : IntervalDyadic :=
  ((ratPoint ((c : ℚ) / scale)).sub
    ((ratPoint ((s : ℚ) / scale)).mul (deltaInterval n X))).add errorInterval

/-- The computed angular interval encloses the actual displacement. -/
theorem delta_mem {n : ℕ} {x : ℝ} {X : IntervalDyadic} (hx : x ∈ X) :
    Real.pi * (x - (n : ℝ) / 8000) ∈ deltaInterval n X := by
  have hn : (n : ℝ) / 8000 ∈ ratPoint ((n : ℚ) / 8000) := by
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      mem_ratPoint ((n : ℚ) / 8000)
  exact IntervalDyadic.roundOut_contains
    (IntervalDyadic.mem_mul pi_mem (IntervalDyadic.mem_sub hx hn)) (-53)

/-- The continuous sine and cosine belong to the computed intervals at
every point of the cell, including its endpoints. -/
theorem trig_mem {n : ℕ} {c s : ℤ} {x : ℝ} {X : IntervalDyadic}
    (hc : |(c : ℝ) / scale - Real.cos ((n : ℝ) * (Real.pi / 8000))| ≤ 1 / 10000000000000)
    (hs : |(s : ℝ) / scale - Real.sin ((n : ℝ) * (Real.pi / 8000))| ≤ 1 / 10000000000000)
    (hx : |x - (n : ℝ) / 8000| ≤ 1 / 8000) (hX : x ∈ X) :
    Real.sin (Real.pi * x) ∈ sineInterval n c s X ∧
      Real.cos (Real.pi * x) ∈ cosineInterval n c s X := by
  have he := nearby_error hc hs hx
  have hcn : (c : ℝ) / scale ∈ ratPoint ((c : ℚ) / scale) := by
    simpa only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using
      mem_ratPoint ((c : ℚ) / scale)
  have hsn : (s : ℝ) / scale ∈ ratPoint ((s : ℚ) / scale) := by
    simpa only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using
      mem_ratPoint ((s : ℚ) / scale)
  have hid (a b : ℝ) : a + (b - a) = b := by ring
  constructor
  · have hv := IntervalDyadic.mem_add
      (IntervalDyadic.mem_add hsn (IntervalDyadic.mem_mul hcn (delta_mem (n := n) hX)))
      (mem_errorInterval he.1)
    rw [hid] at hv
    exact hv
  · have hv := IntervalDyadic.mem_add
      (IntervalDyadic.mem_sub hcn (IntervalDyadic.mem_mul hsn (delta_mem (n := n) hX)))
      (mem_errorInterval he.2)
    rw [hid] at hv
    exact hv

end RiemannGaussian.MontgomeryTaylorPhaseEnclosure
