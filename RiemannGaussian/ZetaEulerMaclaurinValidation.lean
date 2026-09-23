/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaEulerMaclaurinCertificate

/-!
# Kernel-checked validation of the finite zeta evaluator

One literal rectangle near height fourteen is certified from the full
Dirichlet prefix and all Bernoulli corrections. This checks the numerical
and analytic interfaces together. It is not a low-zero list, a completeness
proof, or a reproduction of a published zero-free benchmark.
-/

namespace RiemannGaussian.ZetaEulerMaclaurinValidation
open LeanCert.Core LeanCert.Engine CertifiedComplexInterval ZetaEulerMaclaurinCertificate

/-- Modest precision is sufficient for the first integration certificate. -/
def config : DyadicConfig := {precision := -40, taylorDepth := 12}

/-- Exact source interval for the real coordinate. -/
def realInput : IntervalRat := ⟨1 / 2, 50001 / 100000, by norm_num⟩

/-- Exact source interval for the imaginary coordinate. -/
def imaginaryInput : IntervalRat := ⟨14, 1400001 / 100000, by norm_num⟩

/-- Outward-rounded input rectangle. -/
def inputBox : Box :=
  ⟨IntervalDyadic.ofIntervalRat realInput config.precision,
    IntervalDyadic.ofIntervalRat imaginaryInput config.precision⟩

/-- This complete computation is reduced by the Lean kernel, not trusted
native code or a supplied table of numerical zeta values. -/
theorem checked_rectangle : check config 34 inputBox = true := by
  decide +kernel

/-- Actual zeta is nonzero on every point of the specified rectangle. -/
theorem height_fourteen_rectangle {s : ℂ}
    (hr : (1 / 2 : ℝ) ≤ s.re) (hr' : s.re ≤ (50001 / 100000 : ℝ))
    (hi : (14 : ℝ) ≤ s.im) (hi' : s.im ≤ (1400001 / 100000 : ℝ)) :
    riemannZeta s ≠ 0 := by
  apply nonzero_of_check checked_rectangle
  constructor
  · apply IntervalDyadic.mem_ofIntervalRat (prec := config.precision) (hprec := by decide)
    simpa only [realInput, IntervalRat.mem_def, Rat.cast_div, Rat.cast_one,
      Rat.cast_ofNat] using And.intro hr hr'
  · apply IntervalDyadic.mem_ofIntervalRat (prec := config.precision) (hprec := by decide)
    simpa only [imaginaryInput, IntervalRat.mem_def, Rat.cast_div, Rat.cast_ofNat]
      using And.intro hi hi'

end RiemannGaussian.ZetaEulerMaclaurinValidation
