/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.MontgomeryTaylorAdaptivePhase
import RiemannGaussian.MontgomeryTaylorNumericalCell

/-!
# Continuous kernel cells with adaptive phase error

The checker supports arbitrary rational intervals and arbitrary chosen
phases. Successful evaluation proves real bounds on the complete interval;
the phase may be selected solely to make the computed enclosure tighter.
-/

namespace RiemannGaussian.MontgomeryTaylorAdaptiveCell
open LeanCert.Core LeanCert.Engine
open CertifiedIntervalProgram MontgomeryTaylorPhaseGrid
open MontgomeryTaylorPhaseEnclosure MontgomeryTaylorNumericalKernel

/-- A rational cell at any positive grid resolution. The construction also
has a defined degenerate value at resolution zero. -/
def gridInterval (G i : ℕ) : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat ⟨(i : ℚ) / G, ((i : ℚ) + 1) / G,
    by apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg G); linarith⟩ (-53)

/-- Every point of the rational grid cell belongs to its dyadic enclosure. -/
theorem grid_mem {G i : ℕ} {x : ℝ}
    (hx : x ∈ Set.Icc ((i : ℝ) / G) (((i : ℝ) + 1) / G)) :
    x ∈ gridInterval G i := by
  apply IntervalDyadic.mem_ofIntervalRat (prec := -53) (hprec := by norm_num)
  simpa only [IntervalRat.mem_def, Set.mem_Icc, Rat.cast_div, Rat.cast_natCast,
    Rat.cast_add, Rat.cast_one] using hx

/-- Adaptive trigonometric inputs followed by rational kernel evaluation. -/
def evaluate (n : ℕ) (c s : ℤ) (X : IntervalDyadic) :
    EvalResult (List IntervalDyadic) :=
  run MontgomeryTaylorNumericalCell.config MontgomeryTaylorKernelEnclosure.program
    [X, piInterval, MontgomeryTaylorAdaptivePhase.sineInterval n c s X,
      MontgomeryTaylorAdaptivePhase.cosineInterval n c s X, ratPoint etaRat]

/-- Compare proposed rational lower bounds with the adaptive result. -/
def checkLower (n : ℕ) (c s : ℤ) (X : IntervalDyadic) (v d : ℚ) : Bool :=
  MontgomeryTaylorNumericalCell.checkBounds (evaluate n c s X) v d

/-- Soundness retains the complete value, slope, and curvature intervals. -/
theorem evaluate_sound {n : ℕ} {c s : ℤ} {x : ℝ} {X : IntervalDyadic}
    (hc : |(c : ℝ) / scale - Real.cos ((n : ℝ) * (Real.pi / 8000))| ≤ 1 / 10000000000000)
    (hs : |(s : ℝ) / scale - Real.sin ((n : ℝ) * (Real.pi / 8000))| ≤ 1 / 10000000000000)
    (hx : x ∈ X) {zs : List IntervalDyadic} (h : evaluate n c s X = .ok zs) :
    squaredDD x ∈ intervalEnv zs 0 ∧ squaredD x ∈ intervalEnv zs 1 ∧
      kernel x ^ 2 ∈ intervalEnv zs 2 := by
  have ht := MontgomeryTaylorAdaptivePhase.trig_mem hc hs hx
  exact MontgomeryTaylorKernelEnclosure.enclosures
    (by decide : MontgomeryTaylorNumericalCell.config.precision ≤ 0)
    (.cons hx (.cons pi_mem (.cons ht.1 (.cons ht.2 (.cons (mem_ratPoint etaRat) .nil))))) h

/-- Successful adaptive checks imply real lower bounds at every point of
the interval. No proximity-to-phase hypothesis remains. -/
theorem lower_of_check {n : ℕ} {c s : ℤ} {x : ℝ} {X : IntervalDyadic} {v d : ℚ}
    (hc : |(c : ℝ) / scale - Real.cos ((n : ℝ) * (Real.pi / 8000))| ≤ 1 / 10000000000000)
    (hs : |(s : ℝ) / scale - Real.sin ((n : ℝ) * (Real.pi / 8000))| ≤ 1 / 10000000000000)
    (hx : x ∈ X) (h : checkLower n c s X v d = true) :
    (v : ℝ) ≤ kernel x ^ 2 ∧ (d : ℝ) ≤ squaredDD x := by
  apply MontgomeryTaylorNumericalCell.checkBounds_sound (sq_nonneg (kernel x)) ?_ h
  intro zs he
  have hi := evaluate_sound hc hs hx he
  exact ⟨hi.1, hi.2.2⟩

end RiemannGaussian.MontgomeryTaylorAdaptiveCell
