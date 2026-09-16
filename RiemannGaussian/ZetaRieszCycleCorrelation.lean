/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCycleCore
import RiemannGaussian.ZetaRieszPairMidpoint

/-!
# The arithmetic cross-correlations controlling cycle orientation

Exact zero cycles remove supported portions of original amplitudes and
retain every remainder. Nearby opposite phases have quadratic extra mass
cost, but sufficient aggregate arithmetic capacity at source scale remains
unproved. This is not a new zero-free region or an RH proof.
-/

namespace RiemannGaussian.ZetaRieszCycleCorrelation
noncomputable section
open scoped BigOperators Classical
open ZetaArithmeticBandCorrelation
open ZetaRieszCycleCore
open ZetaRieszPairMidpoint

/-- Signed area is the imaginary part of the retained cross-correlation. -/
theorem area_eq_im_conj_mul (z w : ℂ) :
    area z w = ((starRingEnd ℂ z) * w).im := by
  simp only [area, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- A common complex factor multiplies every area by its squared norm. -/
theorem area_mul_common (z w c : ℂ) :
    area (z * c) (w * c) = Complex.normSq c * area z w := by
  simp only [area, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

/-- The exact relative sine carries the orientation of two unit phases. -/
theorem area_unitPhase (x y : ℝ) :
    area (unitPhase x) (unitPhase y) = Real.sin (y - x) := by
  rw [unitPhase_eq_cos_sin, unitPhase_eq_cos_sin]
  simp only [area, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, one_mul, sub_zero, zero_add, add_zero, Real.sin_sub]
  ring

/-- Real arithmetic signs multiply the exact oriented phase difference. -/
theorem area_real_phases (a b x y : ℝ) :
    area ((a : ℂ) * unitPhase x) ((b : ℂ) * unitPhase y) =
      a * b * Real.sin (y - x) := by
  have h : area ((a : ℂ) * unitPhase x) ((b : ℂ) * unitPhase y) =
      a * b * area (unitPhase x) (unitPhase y) := by
    simp only [area, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, add_zero]
    ring
  rw [h, area_unitPhase]

/-- Full unfiltered original amplitudes expose their arithmetic signs
and exact logarithmic relative sine in every three-cycle test. -/
theorem area_actual_one (L : ℝ) (N : ℕ) (t : ℝ) (i j : ℕ) :
    area (ZetaRieszConditionedEnergy.bandWeight L 1 N t i)
      (ZetaRieszConditionedEnergy.bandWeight L 1 N t j) =
      ZetaRieszTransportPhase.realBandOne L N i *
        ZetaRieszTransportPhase.realBandOne L N j *
          Real.sin (t * (Real.log i - Real.log j)) := by
  rw [ZetaRieszTransportPhase.bandWeight_one_eq_signed_phase,
    ZetaRieszTransportPhase.bandWeight_one_eq_signed_phase, area_real_phases]
  congr 2
  ring

/-- Full complex coefficients contribute both sine and cosine channels
to the exact cycle orientation; no polynomial phase is discarded. -/
theorem area_complex_phases (z w : ℂ) (x y : ℝ) :
    area (z * unitPhase x) (w * unitPhase y) =
      ((starRingEnd ℂ z) * w).re * Real.sin (y - x) +
      ((starRingEnd ℂ z) * w).im * Real.cos (y - x) := by
  rw [area_eq_im_conj_mul, map_mul]
  have he : (starRingEnd ℂ z * starRingEnd ℂ (unitPhase x)) * (w * unitPhase y) =
      (starRingEnd ℂ z * w) * unitPhase (y - x) := by
    rw [unitPhase_sub]
    ring
  rw [he, unitPhase_eq_cos_sin]
  simp only [Complex.mul_im, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, one_mul, sub_zero, zero_add, add_zero]

/-- Every actual full-polynomial pair keeps its zero-height complex
cross-correlation as well as the exact prime-product logarithmic phase. -/
theorem area_actual_full (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) (i j : ℕ) :
    area (ZetaRieszConditionedEnergy.bandWeight L P N t i)
      (ZetaRieszConditionedEnergy.bandWeight L P N t j) =
      ((starRingEnd ℂ (ZetaRieszConditionedEnergy.bandWeight L P N 0 i)) *
        ZetaRieszConditionedEnergy.bandWeight L P N 0 j).re *
          Real.sin (t * (Real.log i - Real.log j)) +
      ((starRingEnd ℂ (ZetaRieszConditionedEnergy.bandWeight L P N 0 i)) *
        ZetaRieszConditionedEnergy.bandWeight L P N 0 j).im *
          Real.cos (t * (Real.log i - Real.log j)) := by
  rw [bandWeight_phase L P N t i, bandWeight_phase L P N t j, area_complex_phases]
  have he : -t * Real.log j - -t * Real.log i = t * (Real.log i - Real.log j) := by ring
  rw [he]
end
end RiemannGaussian.ZetaRieszCycleCorrelation
