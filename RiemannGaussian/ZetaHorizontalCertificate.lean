/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaEulerMaclaurinCertificate

/-!
# Signed zeta rectangle checks for complete zero counting

The literal Euler--Maclaurin evaluator and its analytic error certify
positive real or imaginary parts on entire closed rectangles. These are
numerical inputs for the horizontal counting path and its endpoint.
-/

namespace RiemannGaussian.ZetaHorizontalCertificate
open LeanCert.Core LeanCert.Engine CertifiedComplexInterval
open ZetaEulerMaclaurinEnclosure ZetaEulerMaclaurinCertificate

/-- Check strict positivity of a selected signed coordinate after paying
the full analytic error. The selector is false for real and true for imaginary. -/
def positiveCheck (cfg : DyadicConfig) (N : ℕ) (A : Box) (imaginary : Bool) : Bool :=
  admissible cfg N A && match evaluate cfg N 18 A with
  | .error _ => false
  | .ok B => decide (errorAllowance ≤ (if imaginary then B.im else B.re).lo.toRat)

/-- Successful signed-coordinate checking gives a strict bound for
actual zeta throughout the input rectangle, including every boundary point. -/
theorem positive_of_check {cfg : DyadicConfig} {N : ℕ} {A : Box} {imaginary : Bool}
    (hc : positiveCheck cfg N A imaginary = true) {s : ℂ} (hs : Mem s A) :
    0 < (if imaginary then (riemannZeta s).im else (riemannZeta s).re) := by
  unfold positiveCheck at hc
  obtain ⟨ha, he⟩ := Bool.and_eq_true_iff.mp hc
  cases hB : evaluate cfg N 18 A with
  | error err => simp only [hB, Bool.false_eq_true] at he
  | ok B =>
    simp only [hB, decide_eq_true_eq] at he
    obtain ⟨hlr, _, hli, _⟩ := coordinate_bounds ha hB hs
    cases imaginary with
    | false =>
      have hh : (errorAllowance : ℝ) ≤ B.re.lo.toRat := by exact_mod_cast he
      change 0 < (riemannZeta s).re
      linarith
    | true =>
      have hh : (errorAllowance : ℝ) ≤ B.im.lo.toRat := by exact_mod_cast he
      change 0 < (riemannZeta s).im
      linarith

/-- The exact rational input interval at a fixed rational height. -/
def input (cfg : DyadicConfig) (a b T : ℚ) (h : a ≤ b) : Box :=
  ⟨IntervalDyadic.ofIntervalRat ⟨a, b, h⟩ cfg.precision,
    IntervalDyadic.ofIntervalRat (IntervalRat.singleton T) cfg.precision⟩

/-- Every real abscissa in the stated rational interval lies in the
outward-rounded complex input rectangle. -/
theorem mem_input {cfg : DyadicConfig} (hp : cfg.precision ≤ 0)
    {a b T : ℚ} (h : a ≤ b) {x : ℝ} (hx : (a : ℝ) ≤ x) (hx' : x ≤ (b : ℝ)) :
    Mem ((x : ℂ) + (T : ℂ) * Complex.I) (input cfg a b T h) := by
  constructor
  · apply IntervalDyadic.mem_ofIntervalRat (prec := cfg.precision) (hprec := hp)
    simpa only [IntervalRat.mem_def, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_self, add_zero] using And.intro hx hx'
  · apply IntervalDyadic.mem_ofIntervalRat (prec := cfg.precision) (hprec := hp)
    simpa using IntervalRat.mem_singleton T

end RiemannGaussian.ZetaHorizontalCertificate
