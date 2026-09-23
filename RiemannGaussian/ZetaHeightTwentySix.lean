/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaHorizontalCertificate

/-!
# The complete checked horizontal counting path at height twenty-six

Eight adjacent closed rectangles cover every abscissa from one half to
three halves. Every rectangle is checked with the complete finite zeta
expression and its analytic error. No point-sample interpolation is used.
-/

namespace RiemannGaussian.ZetaHeightTwentySix
open LeanCert.Core LeanCert.Engine CertifiedComplexInterval ZetaHorizontalCertificate

private def cfg : DyadicConfig := {precision := -32, taylorDepth := 12}

private theorem checked_00 : positiveCheck cfg 48
    (input cfg (1 / 2) (17 / 32) 26 (by norm_num)) false = true := by
  decide +kernel

private theorem checked_01 : positiveCheck cfg 48
    (input cfg (17 / 32) (9 / 16) 26 (by norm_num)) false = true := by
  decide +kernel

private theorem checked_02 : positiveCheck cfg 48
    (input cfg (9 / 16) (5 / 8) 26 (by norm_num)) false = true := by
  decide +kernel

private theorem checked_03 : positiveCheck cfg 48
    (input cfg (5 / 8) (11 / 16) 26 (by norm_num)) false = true := by
  decide +kernel

private theorem checked_04 : positiveCheck cfg 48
    (input cfg (11 / 16) (3 / 4) 26 (by norm_num)) false = true := by
  decide +kernel

private theorem checked_05 : positiveCheck cfg 48
    (input cfg (3 / 4) (7 / 8) 26 (by norm_num)) false = true := by
  decide +kernel

private theorem checked_06 : positiveCheck cfg 48
    (input cfg (7 / 8) (1) 26 (by norm_num)) false = true := by
  decide +kernel

private theorem checked_07 : positiveCheck cfg 48
    (input cfg (1) (3 / 2) 26 (by norm_num)) false = true := by
  decide +kernel

private theorem checked_imaginary : positiveCheck cfg 48
    (input cfg (1 / 2) (1 / 2) 26 (by norm_num)) true = true := by
  decide +kernel

private theorem cell_positive {a b : ℚ} (hab : a ≤ b)
    (hc : positiveCheck cfg 48 (input cfg a b 26 hab) false = true)
    {x : ℝ} (ha : (a : ℝ) ≤ x) (hb : x ≤ (b : ℝ)) :
    0 < (riemannZeta ((x : ℂ) + 26 * Complex.I)).re := by
  simpa using positive_of_check hc (mem_input (by decide) hab ha hb)

/-- Actual zeta has positive real part on the entire closed horizontal
counting path at height twenty-six, with no gaps between verified cells. -/
theorem horizontal_positive (x : ℝ) (hx : x ∈ Set.Icc (1 / 2 : ℝ) (3 / 2)) :
    0 < (riemannZeta ((x : ℂ) + 26 * Complex.I)).re := by
  by_cases h0 : x ≤ (17 / 32)
  · apply cell_positive (by norm_num) checked_00
    · norm_num
      linarith [hx.1]
    · simpa using h0
  by_cases h1 : x ≤ (9 / 16)
  · apply cell_positive (by norm_num) checked_01
    · norm_num
      linarith [hx.1]
    · simpa using h1
  by_cases h2 : x ≤ (5 / 8)
  · apply cell_positive (by norm_num) checked_02
    · norm_num
      linarith [hx.1]
    · simpa using h2
  by_cases h3 : x ≤ (11 / 16)
  · apply cell_positive (by norm_num) checked_03
    · norm_num
      linarith [hx.1]
    · simpa using h3
  by_cases h4 : x ≤ (3 / 4)
  · apply cell_positive (by norm_num) checked_04
    · norm_num
      linarith [hx.1]
    · simpa using h4
  by_cases h5 : x ≤ (7 / 8)
  · apply cell_positive (by norm_num) checked_05
    · norm_num
      linarith [hx.1]
    · simpa using h5
  by_cases h6 : x ≤ (1)
  · apply cell_positive (by norm_num) checked_06
    · norm_num
      linarith [hx.1]
    · simpa using h6
  apply cell_positive (by norm_num) checked_07
  · norm_num
    linarith
  · simpa using hx.2

/-- The endpoint has strictly positive imaginary part, including all
rounding, finite-evaluation and analytic-truncation errors. -/
theorem endpoint_imaginary_positive :
    0 < (riemannZeta ((1 / 2 : ℂ) + 26 * Complex.I)).im := by
  simpa using positive_of_check checked_imaginary
    (mem_input (by decide) (by norm_num : (1 / 2 : ℚ) ≤ 1 / 2)
      (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num))

end RiemannGaussian.ZetaHeightTwentySix
