/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaHeightFiftyFour.Cell0
import RiemannGaussian.ZetaHeightFiftyFour.Cell1
import RiemannGaussian.ZetaHeightFiftyFour.Cell2
import RiemannGaussian.ZetaHeightFiftyFour.Cell3
import RiemannGaussian.ZetaHeightFiftyFour.Cell4

/-!
# Complete checked horizontal counting path at height fifty-four

Four independently checked closed cells cover the whole segment from one
half to three halves. The fifth check fixes the endpoint's imaginary sign.
Every cell retains the full analytic and rounding allowances; separating
its kernel computation bounds the memory needed for a clean build.
-/

namespace RiemannGaussian.ZetaHeightFiftyFour

/-- Actual zeta has positive real part on the entire closed counting segment. -/
theorem horizontal_positive (x : ℝ) (hx : x ∈ Set.Icc (1 / 2 : ℝ) (3 / 2)) :
    0 < (riemannZeta ((x : ℂ) + 54 * Complex.I)).re := by
  by_cases h0 : x ≤ 5 / 8
  · exact Cell0.positive ⟨hx.1, h0⟩
  by_cases h1 : x ≤ 3 / 4
  · exact Cell1.positive ⟨by linarith, h1⟩
  by_cases h2 : x ≤ 1
  · exact Cell2.positive ⟨by linarith, h2⟩
  exact Cell3.positive ⟨by linarith, hx.2⟩

/-- The counting endpoint has strictly positive imaginary part. -/
theorem endpoint_imaginary_positive :
    0 < (riemannZeta ((1 / 2 : ℂ) + 54 * Complex.I)).im := Cell4.positive

end RiemannGaussian.ZetaHeightFiftyFour
