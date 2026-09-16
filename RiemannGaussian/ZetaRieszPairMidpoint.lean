/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszTransportSource

/-!
# Keep the common midpoint phase of each transported pair

Exact zero cycles remove supported portions of original amplitudes and
retain every remainder. Nearby opposite phases have quadratic extra mass
cost, but sufficient aggregate arithmetic capacity at source scale remains
unproved. This is not a new zero-free region or an RH proof.
-/

namespace RiemannGaussian.ZetaRieszPairMidpoint
noncomputable section
open scoped BigOperators Classical
open ZetaRieszMassTransport
open ZetaRieszTransportPhase
open ZetaArithmeticBandCorrelation

/-- The exact complex phase keeps both trigonometric coordinates. -/
theorem unitPhase_eq_cos_sin (x : ℝ) :
    unitPhase x = (Real.cos x : ℂ) + Complex.I * (Real.sin x : ℂ) := by
  apply Complex.ext <;>
    simp only [unitPhase, Complex.exp_re, Complex.exp_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, mul_zero, one_mul, sub_zero,
      zero_add, add_zero, Real.exp_zero]

/-- Addition of angles preserves exact complex multiplication. -/
theorem unitPhase_add (x y : ℝ) : unitPhase (x + y) = unitPhase x * unitPhase y := by
  simp only [unitPhase, Complex.ofReal_add, mul_add, Complex.exp_add]

/-- The two complex coefficient channels remain coupled to one midpoint
phase. Neither the trigonometric sign nor the full polynomial phase is lost. -/
theorem weighted_pair_eq_midpoint (z w : ℂ) (x y : ℝ) :
    z * unitPhase x + w * unitPhase y =
      ((z + w) * (Real.cos ((x - y) / 2) : ℂ) +
        Complex.I * (z - w) * (Real.sin ((x - y) / 2) : ℂ)) *
      unitPhase ((x + y) / 2) := by
  have hx : unitPhase x = unitPhase ((x + y) / 2) *
      ((Real.cos ((x - y) / 2) : ℂ) + Complex.I * (Real.sin ((x - y) / 2) : ℂ)) := by
    rw [← unitPhase_eq_cos_sin, ← unitPhase_add]
    congr 1
    ring
  have hy : unitPhase y = unitPhase ((x + y) / 2) *
      ((Real.cos ((x - y) / 2) : ℂ) - Complex.I * (Real.sin ((x - y) / 2) : ℂ)) := by
    have he : unitPhase (-((x - y) / 2)) =
        (Real.cos ((x - y) / 2) : ℂ) - Complex.I * (Real.sin ((x - y) / 2) : ℂ) := by
      rw [unitPhase_eq_cos_sin, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
      ring
    rw [← he, ← unitPhase_add]
    congr 1
    ring
  rw [hx, hy]
  ring

/-- The original full-polynomial sent pair has its precise multiplicative
midpoint phase and both signed coefficient channels. -/
theorem sent_pair_bandWeight_eq_midpoint (L : ℝ) (P : Polynomial ℂ) (N : ℕ)
    (t : ℝ) (i j : ℕ) :
    pairMass (ZetaRieszConditionedEnergy.bandWeight L P N t i)
      (ZetaRieszConditionedEnergy.bandWeight L P N t j) •
      (ray (ZetaRieszConditionedEnergy.bandWeight L P N t i) +
        ray (ZetaRieszConditionedEnergy.bandWeight L P N t j)) =
      (pairMass (ZetaRieszConditionedEnergy.bandWeight L P N 0 i)
        (ZetaRieszConditionedEnergy.bandWeight L P N 0 j) : ℂ) *
      ((ray (ZetaRieszConditionedEnergy.bandWeight L P N 0 i) +
          ray (ZetaRieszConditionedEnergy.bandWeight L P N 0 j)) *
        (Real.cos (-t * (Real.log i - Real.log j) / 2) : ℂ) +
      Complex.I * (ray (ZetaRieszConditionedEnergy.bandWeight L P N 0 i) -
          ray (ZetaRieszConditionedEnergy.bandWeight L P N 0 j)) *
        (Real.sin (-t * (Real.log i - Real.log j) / 2) : ℂ)) *
      unitPhase (-t * (Real.log i + Real.log j) / 2) := by
  have hm (n : ℕ) : ‖ZetaRieszConditionedEnergy.bandWeight L P N t n‖ =
      ‖ZetaRieszConditionedEnergy.bandWeight L P N 0 n‖ := by
    rw [bandWeight_phase, norm_mul, norm_unitPhase, mul_one]
  have hmass : pairMass (ZetaRieszConditionedEnergy.bandWeight L P N t i)
      (ZetaRieszConditionedEnergy.bandWeight L P N t j) =
      pairMass (ZetaRieszConditionedEnergy.bandWeight L P N 0 i)
        (ZetaRieszConditionedEnergy.bandWeight L P N 0 j) := by
    unfold pairMass
    rw [hm i, hm j]
  rw [hmass, ray_bandWeight L P N t i, ray_bandWeight L P N t j,
    weighted_pair_eq_midpoint, Complex.real_smul]
  have hd : (-t * Real.log i - -t * Real.log j) / 2 = -t * (Real.log i - Real.log j) / 2 := by ring
  have hs : (-t * Real.log i + -t * Real.log j) / 2 = -t * (Real.log i + Real.log j) / 2 := by ring
  rw [hd, hs]
  ring
end
end RiemannGaussian.ZetaRieszPairMidpoint
