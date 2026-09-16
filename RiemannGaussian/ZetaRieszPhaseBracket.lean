/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCycleCorrelation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Quadratic partner-mass overhead for opposite phase brackets

Exact zero cycles remove supported portions of original amplitudes and
retain every remainder. Nearby opposite phases have quadratic extra mass
cost, but sufficient aggregate arithmetic capacity at source scale remains
unproved. This is not a new zero-free region or an RH proof.
-/

namespace RiemannGaussian.ZetaRieszPhaseBracket
noncomputable section
open scoped BigOperators Classical
open ZetaArithmeticBandCorrelation
open ZetaRieszCycleCore
open ZetaRieszPairMidpoint
open ZetaRieszCycleCorrelation

/-- Two flanking directions around the opposite ray have an exact
positive trigonometric dependence, before any norm estimate. -/
theorem bracket_identity (theta a b : ℝ) :
    (Real.sin (a + b) : ℂ) * unitPhase theta +
      (Real.sin b : ℂ) * unitPhase (theta + Real.pi - a) +
      (Real.sin a : ℂ) * unitPhase (theta + Real.pi + b) = 0 := by
  have ha : unitPhase (theta + Real.pi - a) =
      unitPhase theta * unitPhase (Real.pi - a) := by
    rw [← unitPhase_add]
    congr 1
    ring
  have hb : unitPhase (theta + Real.pi + b) =
      unitPhase theta * unitPhase (Real.pi + b) := by
    rw [← unitPhase_add]
    congr 1
    ring
  rw [ha, hb]
  have hid : (Real.sin (a + b) : ℂ) +
      (Real.sin b : ℂ) * unitPhase (Real.pi - a) +
      (Real.sin a : ℂ) * unitPhase (Real.pi + b) = 0 := by
    have hva : unitPhase (Real.pi - a) =
        -(Real.cos a : ℂ) + Complex.I * (Real.sin a : ℂ) := by
      rw [unitPhase_eq_cos_sin, Real.cos_pi_sub, Real.sin_pi_sub, Complex.ofReal_neg]
    have hvb : unitPhase (Real.pi + b) =
        -(Real.cos b : ℂ) - Complex.I * (Real.sin b : ℂ) := by
      rw [add_comm Real.pi b, unitPhase_eq_cos_sin, Real.cos_add_pi, Real.sin_add_pi,
        Complex.ofReal_neg, Complex.ofReal_neg]
      ring
    rw [hva, hvb, Real.sin_add]
    simp only [Complex.ofReal_add, Complex.ofReal_mul]
    ring
  linear_combination unitPhase theta * hid

/-- The exact partner coefficients are positive when both flanks are
strict and the enclosing angle is less than a half turn. -/
theorem bracket_coefficients_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b < Real.pi) :
    0 < Real.sin (a + b) ∧ 0 < Real.sin b ∧ 0 < Real.sin a := by
  exact ⟨Real.sin_pos_of_pos_of_lt_pi (add_pos ha hb) hab,
    Real.sin_pos_of_pos_of_lt_pi hb (by linarith),
    Real.sin_pos_of_pos_of_lt_pi ha (by linarith)⟩

/-- The total opposite mass required to cancel one unit central mass. -/
def bracketOverhead (a b : ℝ) : ℝ :=
  (Real.sin a + Real.sin b) / Real.sin (a + b)

/-- The partner mass is at least the central mass: exact cancellation
never manufactures amplitude. -/
theorem one_le_bracketOverhead {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b < Real.pi) : 1 ≤ bracketOverhead a b := by
  obtain ⟨hs, hb', ha'⟩ := bracket_coefficients_pos ha hb hab
  rw [bracketOverhead, le_div_iff₀ hs, one_mul, Real.sin_add]
  nlinarith [mul_nonneg ha'.le (sub_nonneg.mpr (Real.cos_le_one b)),
    mul_nonneg hb'.le (sub_nonneg.mpr (Real.cos_le_one a))]

/-- Nearby opposite flanks pay only quadratic angular overhead. The
actual availability of this partner mass is a separate arithmetic task. -/
theorem bracketOverhead_le_quadratic {a b delta : ℝ}
    (ha : 0 < a) (hb : 0 < b) (had : a ≤ delta) (hbd : b ≤ delta)
    (hd : delta ≤ 1) :
    bracketOverhead a b ≤ 1 / (1 - delta ^ 2 / 2) := by
  have hd0 : 0 < delta := ha.trans_le had
  have hd2 : delta ^ 2 ≤ 1 := by nlinarith
  have hc : 0 < 1 - delta ^ 2 / 2 := by linarith
  have hab : a + b < Real.pi := by linarith [Real.pi_gt_three]
  obtain ⟨hs, hsb, hsa⟩ := bracket_coefficients_pos ha hb hab
  have hca : 1 - delta ^ 2 / 2 ≤ Real.cos a := by
    have hsq : a ^ 2 ≤ delta ^ 2 := by nlinarith
    linarith [Real.one_sub_sq_div_two_le_cos (x := a)]
  have hcb : 1 - delta ^ 2 / 2 ≤ Real.cos b := by
    have hsq : b ^ 2 ≤ delta ^ 2 := by nlinarith
    linarith [Real.one_sub_sq_div_two_le_cos (x := b)]
  rw [bracketOverhead, div_le_div_iff₀ hs hc, one_mul, Real.sin_add]
  nlinarith [mul_nonneg hsa.le (sub_nonneg.mpr hcb),
    mul_nonneg hsb.le (sub_nonneg.mpr hca)]


/-- On a one-radian bracket, the excess partner mass is at most the
square of the phase error, without a linear angular loss. -/
theorem bracketOverhead_sub_one_le_sq {a b delta : ℝ}
    (ha : 0 < a) (hb : 0 < b) (had : a ≤ delta) (hbd : b ≤ delta)
    (hd : delta ≤ 1) : bracketOverhead a b - 1 ≤ delta ^ 2 := by
  have hd0 : 0 < delta := ha.trans_le had
  have hd2 : delta ^ 2 ≤ 1 := by nlinarith
  have hc : 0 < 1 - delta ^ 2 / 2 := by linarith
  have he : 1 / (1 - delta ^ 2 / 2) ≤ 1 + delta ^ 2 := by
    rw [div_le_iff₀ hc]
    nlinarith [sq_nonneg delta, mul_nonneg (sq_nonneg delta) (sub_nonneg.mpr hd2)]
  linarith [(bracketOverhead_le_quadratic ha hb had hbd hd).trans he]

/-- The exact trigonometric weights cancel an arbitrary prescribed
central mass. This identity keeps its complete common phase. -/
theorem bracket_removal_identity (theta A a b : ℝ) (hs : Real.sin (a + b) ≠ 0) :
    (A : ℂ) * unitPhase theta +
      (A * Real.sin b / Real.sin (a + b) : ℝ) * unitPhase (theta + Real.pi - a) +
      (A * Real.sin a / Real.sin (a + b) : ℝ) * unitPhase (theta + Real.pi + b) = 0 := by
  have hcast : (Real.sin (a + b) : ℂ) ≠ 0 := by exact_mod_cast hs
  have hid := bracket_identity theta a b
  have he : (A : ℂ) * unitPhase theta +
      (A * Real.sin b / Real.sin (a + b) : ℝ) * unitPhase (theta + Real.pi - a) +
      (A * Real.sin a / Real.sin (a + b) : ℝ) * unitPhase (theta + Real.pi + b) =
      ((A : ℂ) / (Real.sin (a + b) : ℂ)) *
      ((Real.sin (a + b) : ℂ) * unitPhase theta +
        (Real.sin b : ℂ) * unitPhase (theta + Real.pi - a) +
        (Real.sin a : ℂ) * unitPhase (theta + Real.pi + b)) := by
    simp only [Complex.ofReal_div, Complex.ofReal_mul]
    field_simp [hcast]
  rw [he, hid, mul_zero]

/-- If the actual flanking amplitudes supply the sine-weighted portions,
the central amplitude disappears with zero chord cost. All excess partner
mass remains in this quantitative bound. -/
theorem norm_bracket_le_remaining (theta A B C a b : ℝ)
    (hs : Real.sin (a + b) ≠ 0)
    (hB : A * Real.sin b / Real.sin (a + b) ≤ B)
    (hC : A * Real.sin a / Real.sin (a + b) ≤ C) :
    ‖(A : ℂ) * unitPhase theta + (B : ℂ) * unitPhase (theta + Real.pi - a) +
      (C : ℂ) * unitPhase (theta + Real.pi + b)‖ ≤
      B + C - A * bracketOverhead a b := by
  have hid := bracket_removal_identity theta A a b hs
  have he : (A : ℂ) * unitPhase theta + (B : ℂ) * unitPhase (theta + Real.pi - a) +
      (C : ℂ) * unitPhase (theta + Real.pi + b) =
      ((B - A * Real.sin b / Real.sin (a + b) : ℝ) : ℂ) * unitPhase (theta + Real.pi - a) +
      ((C - A * Real.sin a / Real.sin (a + b) : ℝ) : ℂ) * unitPhase (theta + Real.pi + b) := by
    simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_mul] at hid ⊢
    linear_combination hid
  rw [he]
  apply (norm_add_le _ _).trans_eq
  rw [norm_mul, norm_mul, norm_unitPhase, norm_unitPhase, mul_one, mul_one,
    Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr hB),
    Real.norm_of_nonneg (sub_nonneg.mpr hC)]
  unfold bracketOverhead
  ring

/-- The exact cancellation removes at least twice the central mass
whenever both required partner portions are actually available. -/
theorem norm_bracket_le_sub_twice (theta A B C a b : ℝ)
    (hA : 0 ≤ A) (ha : 0 < a) (hb : 0 < b) (hab : a + b < Real.pi)
    (hB : A * Real.sin b / Real.sin (a + b) ≤ B)
    (hC : A * Real.sin a / Real.sin (a + b) ≤ C) :
    ‖(A : ℂ) * unitPhase theta + (B : ℂ) * unitPhase (theta + Real.pi - a) +
      (C : ℂ) * unitPhase (theta + Real.pi + b)‖ ≤ A + B + C - 2 * A := by
  have he := norm_bracket_le_remaining theta A B C a b
    (bracket_coefficients_pos ha hb hab).1.ne' hB hC
  have ho := mul_le_mul_of_nonneg_left (one_le_bracketOverhead ha hb hab) hA
  linarith


/-- The actually available central mass is fixed by all three capacities,
not chosen independently of the original amplitudes. -/
def bracketCapacity (A B C a b : ℝ) : ℝ :=
  min A (min (B * Real.sin (a + b) / Real.sin b)
    (C * Real.sin (a + b) / Real.sin a))

/-- The deterministic bracket capacity automatically respects every
original amplitude, including a shortage on either side. -/
theorem bracketCapacity_bounds {A B C a b : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b < Real.pi) :
    0 ≤ bracketCapacity A B C a b ∧ bracketCapacity A B C a b ≤ A ∧
    bracketCapacity A B C a b * Real.sin b / Real.sin (a + b) ≤ B ∧
    bracketCapacity A B C a b * Real.sin a / Real.sin (a + b) ≤ C := by
  obtain ⟨hs, hsb, hsa⟩ := bracket_coefficients_pos ha hb hab
  have hmB : bracketCapacity A B C a b ≤ B * Real.sin (a + b) / Real.sin b :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hmC : bracketCapacity A B C a b ≤ C * Real.sin (a + b) / Real.sin a :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨le_min hA (le_min (div_nonneg (mul_nonneg hB hs.le) hsb.le)
    (div_nonneg (mul_nonneg hC hs.le) hsa.le)), min_le_left _ _, ?_, ?_⟩
  · rw [div_le_iff₀ hs]
    exact (le_div_iff₀ hsb).mp hmB
  · rw [div_le_iff₀ hs]
    exact (le_div_iff₀ hsa).mp hmC

/-- A complete three-amplitude bound pays the actual deterministic
capacity. Every shortage and remaining amplitude is included; no phase
approximation error is charged to the removed exact zero cycle. -/
theorem norm_bracket_le_capacity (theta A B C a b : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b < Real.pi) :
    ‖(A : ℂ) * unitPhase theta + (B : ℂ) * unitPhase (theta + Real.pi - a) +
      (C : ℂ) * unitPhase (theta + Real.pi + b)‖ ≤
      A + B + C - bracketCapacity A B C a b * (1 + bracketOverhead a b) := by
  let m := bracketCapacity A B C a b
  obtain ⟨_, hmA, hmB, hmC⟩ := bracketCapacity_bounds hA hB hC ha hb hab
  have hr := norm_bracket_le_remaining theta m B C a b
    (bracket_coefficients_pos ha hb hab).1.ne' hmB hmC
  have he : (A : ℂ) * unitPhase theta + (B : ℂ) * unitPhase (theta + Real.pi - a) +
      (C : ℂ) * unitPhase (theta + Real.pi + b) =
      ((A - m : ℝ) : ℂ) * unitPhase theta +
        ((m : ℂ) * unitPhase theta + (B : ℂ) * unitPhase (theta + Real.pi - a) +
        (C : ℂ) * unitPhase (theta + Real.pi + b)) := by
    rw [Complex.ofReal_sub]
    ring
  rw [he]
  have hn := norm_add_le (((A - m : ℝ) : ℂ) * unitPhase theta)
    ((m : ℂ) * unitPhase theta + (B : ℂ) * unitPhase (theta + Real.pi - a) +
      (C : ℂ) * unitPhase (theta + Real.pi + b))
  rw [norm_mul, norm_unitPhase, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (sub_nonneg.mpr hmA)] at hn
  change _ ≤ A + B + C - m * (1 + bracketOverhead a b)
  linarith


/-- The literal bracket has a positive zero cycle for any three positive
available amplitudes, even when those amplitudes differ. -/
theorem positiveCycle_bracket {theta A B C a b : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b < Real.pi) :
    positiveCycle ((A : ℂ) * unitPhase theta)
      ((B : ℂ) * unitPhase (theta + Real.pi - a))
      ((C : ℂ) * unitPhase (theta + Real.pi + b)) := by
  obtain ⟨hs, hsb, hsa⟩ := bracket_coefficients_pos ha hb hab
  unfold positiveCycle
  simp only [area_real_phases]
  have h1 : theta + Real.pi + b - (theta + Real.pi - a) = a + b := by ring
  have h2 : theta - (theta + Real.pi + b) = -(b + Real.pi) := by ring
  have h3 : theta + Real.pi - a - theta = Real.pi - a := by ring
  rw [h1, h2, h3, Real.sin_neg, Real.sin_add_pi, neg_neg, Real.sin_pi_sub]
  exact ⟨mul_pos (mul_pos hB hC) hs, mul_pos (mul_pos hC hA) hsb,
    mul_pos (mul_pos hA hB) hsa⟩

end
end RiemannGaussian.ZetaRieszPhaseBracket
