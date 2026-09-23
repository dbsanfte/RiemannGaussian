/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaHorizontalCertificate

/-!
# A checked complete horizontal counting path at height fifteen

Fourteen adjacent closed rectangles cover every abscissa from one half to
three halves. Their complete Euler--Maclaurin checks prove positive real
part throughout the path. A separate endpoint check proves positive
imaginary part. No sampled-point interpolation or assumed values are used.
-/

namespace RiemannGaussian.ZetaHeightFifteen
open LeanCert.Core LeanCert.Engine CertifiedComplexInterval ZetaHorizontalCertificate

private def cfg : DyadicConfig := {precision := -32, taylorDepth := 12}

private theorem checked_00 : positiveCheck cfg 36
    (input cfg (1 / 2) (33 / 64) 15 (by norm_num)) false = true := by
  decide +kernel

private theorem checked_01 : positiveCheck cfg 36
    (input cfg (33 / 64) (17 / 32) 15 (by norm_num)) false = true := by
  decide +kernel

private theorem checked_02 : positiveCheck cfg 36
    (input cfg (17 / 32) (35 / 64) 15 (by norm_num)) false = true := by
  decide +kernel

private theorem checked_03 : positiveCheck cfg 36
    (input cfg (35 / 64) (9 / 16) 15 (by norm_num)) false = true := by
  decide +kernel

private theorem checked_04 : positiveCheck cfg 36
    (input cfg (9 / 16) (19 / 32) 15 (by norm_num)) false = true := by
  decide +kernel

private theorem checked_05 : positiveCheck cfg 36
    (input cfg (19 / 32) (5 / 8) 15 (by norm_num)) false = true := by
  decide +kernel

private theorem checked_06 : positiveCheck cfg 36
    (input cfg (5 / 8) (21 / 32) 15 (by norm_num)) false = true := by
  decide +kernel

private theorem checked_07 : positiveCheck cfg 36
    (input cfg (21 / 32) (11 / 16) 15 (by norm_num)) false = true := by
  decide +kernel

private theorem checked_08 : positiveCheck cfg 36
    (input cfg (11 / 16) (3 / 4) 15 (by norm_num)) false = true := by
  decide +kernel

private theorem checked_09 : positiveCheck cfg 36
    (input cfg (3 / 4) (13 / 16) 15 (by norm_num)) false = true := by
  decide +kernel

private theorem checked_10 : positiveCheck cfg 36
    (input cfg (13 / 16) (7 / 8) 15 (by norm_num)) false = true := by
  decide +kernel

private theorem checked_11 : positiveCheck cfg 36
    (input cfg (7 / 8) 1 15 (by norm_num)) false = true := by
  decide +kernel

private theorem checked_12 : positiveCheck cfg 36
    (input cfg 1 (5 / 4) 15 (by norm_num)) false = true := by
  decide +kernel

private theorem checked_13 : positiveCheck cfg 36
    (input cfg (5 / 4) (3 / 2) 15 (by norm_num)) false = true := by
  decide +kernel

private theorem checked_imaginary : positiveCheck cfg 36
    (input cfg (1 / 2) (1 / 2) 15 (by norm_num)) true = true := by
  decide +kernel

private theorem cell_positive {a b : ℚ} (hab : a ≤ b)
    (hc : positiveCheck cfg 36 (input cfg a b 15 hab) false = true)
    {x : ℝ} (ha : (a : ℝ) ≤ x) (hb : x ≤ (b : ℝ)) :
    0 < (riemannZeta ((x : ℂ) + 15 * Complex.I)).re := by
  simpa using positive_of_check hc (mem_input (by decide) hab ha hb)

/-- Actual zeta has positive real part on the complete horizontal counting
segment at height fifteen, including every junction between checked cells. -/
theorem horizontal_positive (x : ℝ) (hx : x ∈ Set.Icc (1 / 2 : ℝ) (3 / 2)) :
    0 < (riemannZeta ((x : ℂ) + 15 * Complex.I)).re := by
  by_cases h0 : x ≤ (33 / 64)
  · apply cell_positive (by norm_num) checked_00
    · norm_num
      linarith [hx.1]
    · simpa using h0
  by_cases h1 : x ≤ (17 / 32)
  · apply cell_positive (by norm_num) checked_01
    · norm_num
      linarith [hx.1]
    · simpa using h1
  by_cases h2 : x ≤ (35 / 64)
  · apply cell_positive (by norm_num) checked_02
    · norm_num
      linarith [hx.1]
    · simpa using h2
  by_cases h3 : x ≤ (9 / 16)
  · apply cell_positive (by norm_num) checked_03
    · norm_num
      linarith [hx.1]
    · simpa using h3
  by_cases h4 : x ≤ (19 / 32)
  · apply cell_positive (by norm_num) checked_04
    · norm_num
      linarith [hx.1]
    · simpa using h4
  by_cases h5 : x ≤ (5 / 8)
  · apply cell_positive (by norm_num) checked_05
    · norm_num
      linarith [hx.1]
    · simpa using h5
  by_cases h6 : x ≤ (21 / 32)
  · apply cell_positive (by norm_num) checked_06
    · norm_num
      linarith [hx.1]
    · simpa using h6
  by_cases h7 : x ≤ (11 / 16)
  · apply cell_positive (by norm_num) checked_07
    · norm_num
      linarith [hx.1]
    · simpa using h7
  by_cases h8 : x ≤ (3 / 4)
  · apply cell_positive (by norm_num) checked_08
    · norm_num
      linarith [hx.1]
    · simpa using h8
  by_cases h9 : x ≤ (13 / 16)
  · apply cell_positive (by norm_num) checked_09
    · norm_num
      linarith [hx.1]
    · simpa using h9
  by_cases h10 : x ≤ (7 / 8)
  · apply cell_positive (by norm_num) checked_10
    · norm_num
      linarith [hx.1]
    · simpa using h10
  by_cases h11 : x ≤ 1
  · apply cell_positive (by norm_num) checked_11
    · norm_num
      linarith [hx.1]
    · simpa using h11
  by_cases h12 : x ≤ (5 / 4)
  · apply cell_positive (by norm_num) checked_12
    · norm_num
      linarith [hx.1]
    · simpa using h12
  apply cell_positive (by norm_num) checked_13
  · norm_num
    linarith
  · simpa using hx.2

/-- The critical-line endpoint at height fifteen has positive imaginary
part, with both numerical and analytic errors included. -/
theorem endpoint_imaginary_positive :
    0 < (riemannZeta ((1 / 2 : ℂ) + 15 * Complex.I)).im := by
  simpa using positive_of_check checked_imaginary
    (mem_input (by decide) (by norm_num : (1 / 2 : ℚ) ≤ 1 / 2)
      (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num))

end RiemannGaussian.ZetaHeightFifteen
