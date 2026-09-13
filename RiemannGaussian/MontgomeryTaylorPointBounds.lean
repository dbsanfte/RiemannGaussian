/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.MontgomeryTaylorRangeTable

/-!
# Checked values and slopes at reusable rational anchors

Each check supplies a lower bound for the squared kernel and an enclosing
interval for its signed derivative. The exact phase-cycle proof is reused;
the point is enclosed by outward dyadic rounding before evaluation.
-/

namespace RiemannGaussian.MontgomeryTaylorPointBounds
open LeanCert.Core LeanCert.Engine CertifiedIntervalProgram
open MontgomeryTaylorNumericalKernel MontgomeryTaylorRangeTable

/-- Fixed-point data proposed for one squared-kernel value and slope. -/
structure Bounds where
  /-- Integer lower bound for the squared-kernel value. -/
  value : ℤ
  /-- Integer lower bound for its signed derivative. -/
  derivativeLo : ℤ
  /-- Integer upper bound for its signed derivative. -/
  derivativeHi : ℤ

/-- The exact rational squared-value lower bound. -/
def Bounds.valueRat (b : Bounds) : ℚ := (b.value : ℚ) / boundScale

/-- The exact rational lower endpoint of the slope enclosure. -/
def Bounds.lowerRat (b : Bounds) : ℚ := (b.derivativeLo : ℚ) / boundScale

/-- The exact rational upper endpoint of the slope enclosure. -/
def Bounds.upperRat (b : Bounds) : ℚ := (b.derivativeHi : ℚ) / boundScale

/-- Check a proposed point enclosure against a successful program result. -/
def checkOutput (result : EvalResult (List IntervalDyadic)) (b : Bounds) : Bool :=
  match result with
  | .error _ => false
  | .ok zs => decide (b.valueRat ≤ max 0 (intervalEnv zs 2).lo.toRat) &&
      decide (b.lowerRat ≤ (intervalEnv zs 1).lo.toRat) &&
      decide ((intervalEnv zs 1).hi.toRat ≤ b.upperRat)

/-- The point data's real analytic interpretation. -/
def Valid (q : ℚ) (b : Bounds) : Prop :=
  (b.valueRat : ℝ) ≤ kernel q ^ 2 ∧
    squaredD q ∈ Set.Icc (b.lowerRat : ℝ) b.upperRat

/-- Abstract output comparisons preserve both the value and signed slope. -/
theorem checkOutput_sound {result : EvalResult (List IntervalDyadic)} {b : Bounds} {q : ℚ}
    (hsound : ∀ zs, result = .ok zs →
      squaredD q ∈ intervalEnv zs 1 ∧ kernel q ^ 2 ∈ intervalEnv zs 2)
    (h : checkOutput result b = true) : Valid q b := by
  cases result with
  | error e => simp [checkOutput] at h
  | ok zs =>
    simp only [checkOutput, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hd, hv⟩ := hsound zs rfl
    have hv' : (b.valueRat : ℝ) ≤ max 0 ((intervalEnv zs 2).lo.toRat : ℝ) := by
      exact_mod_cast h.1.1
    have hl : (b.lowerRat : ℝ) ≤ ((intervalEnv zs 1).lo.toRat : ℝ) := by
      exact_mod_cast h.1.2
    have hu : ((intervalEnv zs 1).hi.toRat : ℝ) ≤ b.upperRat := by exact_mod_cast h.2
    exact ⟨hv'.trans (max_le (sq_nonneg _) hv.1), hl.trans hd.1, hd.2.trans hu⟩

/-- Check a point enclosure using a chosen certified phase. -/
def check (q : ℚ) (n : ℕ) (b : Bounds) : Bool :=
  let cs := MontgomeryTaylorPhaseGrid.CertificateData.lookup n
  checkOutput (MontgomeryTaylorAdaptiveCell.evaluate n cs.1 cs.2
    (MontgomeryTaylorPhaseEnclosure.ratPoint q)) b

/-- A successful Boolean point check supplies the complete real enclosure. -/
theorem check_sound {q : ℚ} {n : ℕ} {b : Bounds} (h : check q n b = true) :
    Valid q b := by
  dsimp only [check] at h
  apply checkOutput_sound (q := q) (b := b) (result := MontgomeryTaylorAdaptiveCell.evaluate n
    (MontgomeryTaylorPhaseGrid.CertificateData.lookup n).1
    (MontgomeryTaylorPhaseGrid.CertificateData.lookup n).2
    (MontgomeryTaylorPhaseEnclosure.ratPoint q)) ?_ h
  intro zs he
  have hp := MontgomeryTaylorPhaseGrid.CertificateData.lookup_error n
  have hv := MontgomeryTaylorAdaptiveCell.evaluate_sound hp.1 hp.2
    (MontgomeryTaylorPhaseEnclosure.mem_ratPoint q) he
  exact hv.2

end RiemannGaussian.MontgomeryTaylorPointBounds
