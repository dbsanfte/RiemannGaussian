/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.MontgomeryTaylorPhaseEnclosure

/-!
# An executable checker for continuous kernel cells

The two rational outputs bound the squared correlation and its second
derivative on the complete input cell. A successful check supplies genuine
continuous inequalities; it is not a sample-point test.
-/

namespace RiemannGaussian.MontgomeryTaylorNumericalCell
open LeanCert.Core LeanCert.Engine
open CertifiedIntervalProgram MontgomeryTaylorPhaseGrid
open MontgomeryTaylorPhaseEnclosure MontgomeryTaylorNumericalKernel

/-- Fixed precision for the rational-only arithmetic program. -/
def config : DyadicConfig := { precision := -53, taylorDepth := 0 }

/-- The outward-rounded cell between two consecutive multiples of `1/4000`. -/
def gridInterval (i : ℕ) : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat ⟨(i : ℚ) / 4000, ((i : ℚ) + 1) / 4000,
    by apply div_le_div_of_nonneg_right _ (by norm_num); linarith⟩ (-53)

/-- The actual closed grid cell lies in its computed dyadic enclosure. -/
theorem grid_mem {i : ℕ} {x : ℝ}
    (hx : x ∈ Set.Icc ((i : ℝ) / 4000) (((i : ℝ) + 1) / 4000)) :
    x ∈ gridInterval i := by
  apply IntervalDyadic.mem_ofIntervalRat (prec := -53) (hprec := by norm_num)
  simpa only [IntervalRat.mem_def, Set.mem_Icc, Rat.cast_div, Rat.cast_natCast,
    Rat.cast_ofNat, Rat.cast_add, Rat.cast_one] using hx

/-- The odd phase index is exactly the center of the complete grid cell. -/
theorem grid_near_phase {i : ℕ} {x : ℝ}
    (hx : x ∈ Set.Icc ((i : ℝ) / 4000) (((i : ℝ) + 1) / 4000)) :
    |x - ((2 * i + 1 : ℕ) : ℝ) / 8000| ≤ 1 / 8000 := by
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- Inputs assembled from the phase certificate and a continuous cell. -/
def cellInputs (n : ℕ) (c s : ℤ) (X : IntervalDyadic) : List IntervalDyadic :=
  [X, piInterval, sineInterval n c s X, cosineInterval n c s X, ratPoint etaRat]

/-- Checked evaluation, including the nonzero denominator obligation. -/
def evaluate (n : ℕ) (c s : ℤ) (X : IntervalDyadic) :
    EvalResult (List IntervalDyadic) :=
  run config MontgomeryTaylorKernelEnclosure.program (cellInputs n c s X)

/-- Lower-bound comparisons for a checked evaluator result. -/
def checkBounds (result : EvalResult (List IntervalDyadic)) (v d : ℚ) : Bool :=
  match result with
  | .error _ => false
  | .ok zs =>
    decide (v ≤ max 0 (intervalEnv zs 2).lo.toRat) &&
      decide (d ≤ (intervalEnv zs 0).lo.toRat)

/-- Proposed lower bounds are checked against the computed intervals.
The squared kernel also has its exact algebraic lower bound zero. -/
def checkLower (n : ℕ) (c s : ℤ) (X : IntervalDyadic) (v d : ℚ) : Bool :=
  checkBounds (evaluate n c s X) v d

/-- Successful comparisons turn correct result intervals into real lower bounds. -/
theorem checkBounds_sound {result : EvalResult (List IntervalDyadic)}
    {v d : ℚ} {w dd : ℝ} (hw0 : 0 ≤ w)
    (hsound : ∀ zs, result = .ok zs →
      dd ∈ intervalEnv zs 0 ∧ w ∈ intervalEnv zs 2)
    (h : checkBounds result v d = true) : (v : ℝ) ≤ w ∧ (d : ℝ) ≤ dd := by
  cases result with
  | error err => simp [checkBounds] at h
  | ok zs =>
    simp only [checkBounds, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hdd, hw⟩ := hsound zs rfl
    have hv : (v : ℝ) ≤ max 0 ((intervalEnv zs 2).lo.toRat : ℝ) := by
      exact_mod_cast h.1
    have hd : (d : ℝ) ≤ ((intervalEnv zs 0).lo.toRat : ℝ) := by exact_mod_cast h.2
    exact ⟨hv.trans (max_le hw0 hw.1), hd.trans hdd.1⟩

/-- Continuous soundness of the complete rational kernel evaluation. -/
theorem evaluate_sound {n : ℕ} {c s : ℤ} {x : ℝ} {X : IntervalDyadic}
    (hc : |(c : ℝ) / scale - Real.cos ((n : ℝ) * (Real.pi / 8000))| ≤ 1 / 10000000000000)
    (hs : |(s : ℝ) / scale - Real.sin ((n : ℝ) * (Real.pi / 8000))| ≤ 1 / 10000000000000)
    (hx : |x - (n : ℝ) / 8000| ≤ 1 / 8000) (hX : x ∈ X)
    {zs : List IntervalDyadic} (h : evaluate n c s X = .ok zs) :
    squaredDD x ∈ intervalEnv zs 0 ∧ squaredD x ∈ intervalEnv zs 1 ∧
      kernel x ^ 2 ∈ intervalEnv zs 2 := by
  have ht := trig_mem hc hs hx hX
  have hi : List.Forall₂ (fun v I => v ∈ I)
      (MontgomeryTaylorKernelEnclosure.inputs x) (cellInputs n c s X) :=
    .cons hX (.cons pi_mem (.cons ht.1 (.cons ht.2 (.cons (mem_ratPoint etaRat) .nil))))
  exact MontgomeryTaylorKernelEnclosure.enclosures (by decide : config.precision ≤ 0) hi h

/-- A successful Boolean check supplies actual lower bounds throughout
the real cell, with all reciprocal and interpolation conditions retained. -/
theorem lower_of_check {n : ℕ} {c s : ℤ} {x : ℝ} {X : IntervalDyadic} {v d : ℚ}
    (hc : |(c : ℝ) / scale - Real.cos ((n : ℝ) * (Real.pi / 8000))| ≤ 1 / 10000000000000)
    (hs : |(s : ℝ) / scale - Real.sin ((n : ℝ) * (Real.pi / 8000))| ≤ 1 / 10000000000000)
    (hx : |x - (n : ℝ) / 8000| ≤ 1 / 8000) (hX : x ∈ X)
    (h : checkLower n c s X v d = true) :
    (v : ℝ) ≤ kernel x ^ 2 ∧ (d : ℝ) ≤ squaredDD x := by
  apply checkBounds_sound (sq_nonneg (kernel x)) ?_ h
  intro zs he
  have hi := evaluate_sound hc hs hx hX he
  exact ⟨hi.1, hi.2.2⟩

end RiemannGaussian.MontgomeryTaylorNumericalCell
