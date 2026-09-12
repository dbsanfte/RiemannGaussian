/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.AnalyticStripGrowth
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# The two vertical boundaries in the original disc coordinate

The hyperbolic parametrizations retain the full complex boundary point and
its orientation. The actual strip map sends them to the two vertical lines
with the exact height scale. Its principal logarithm is continuous at every
finite parameter; the two infinite ends are never treated as finite points.
-/

namespace RiemannGaussian.AnalyticStripBoundary
noncomputable section
open Complex Filter Set
open AnalyticStripMap
open scoped Topology

/-- The positive-real semicircle, parametrized by vertical strip height. -/
def right (u : ℝ) : ℂ := ((1 / Real.cosh u : ℝ) : ℂ) + (Real.tanh u : ℂ) * I

/-- The negative-real semicircle, retaining the same upward height orientation. -/
def left (u : ℝ) : ℂ := -((1 / Real.cosh u : ℝ) : ℂ) + (Real.tanh u : ℂ) * I

/-- The positive arc has its exact signed real projection. -/
theorem right_re (u : ℝ) : (right u).re = 1 / Real.cosh u := by
  simp only [right, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, zero_mul, sub_zero, add_zero]

/-- The negative arc has the opposite real projection. -/
theorem left_re (u : ℝ) : (left u).re = -(1 / Real.cosh u) := by
  simp only [left, add_re, neg_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, zero_mul, sub_zero, add_zero]

/-- The Cayley coordinate on the positive arc is a positive multiple of `I`. -/
theorem cayley_right (u : ℝ) : cayley (right u) = (Real.exp (-u) : ℂ) * I := by
  have hc : Real.cosh u ≠ 0 := (Real.cosh_pos u).ne'
  have he : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have hd : 1 - right u * I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [sub_im, one_im, mul_im, right_re, I_im, I_re, mul_one,
      mul_zero, add_zero, zero_sub, zero_im, neg_eq_zero] at hi
    exact (one_div_ne_zero hc) hi
  rw [cayley, div_eq_iff hd]
  apply Complex.ext <;>
    simp only [right, add_re, add_im, sub_re, sub_im, mul_re, mul_im,
      ofReal_re, ofReal_im, one_re, one_im, I_re, I_im, mul_zero, zero_mul,
      mul_one, add_zero, zero_add, sub_zero, zero_sub]
  all_goals rw [Real.tanh_eq_sinh_div_cosh]
  all_goals field_simp
  all_goals rw [Real.cosh_eq, Real.sinh_eq]
  all_goals nlinarith

/-- The Cayley coordinate on the negative arc retains the opposite argument. -/
theorem cayley_left (u : ℝ) : cayley (left u) = (Real.exp (-u) : ℂ) * (-I) := by
  have hc : Real.cosh u ≠ 0 := (Real.cosh_pos u).ne'
  have he : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have hd : 1 - left u * I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [sub_im, one_im, mul_im, left_re, I_im, I_re, mul_one,
      mul_zero, add_zero, zero_sub, zero_im, neg_neg] at hi
    exact (one_div_ne_zero hc) hi
  rw [cayley, div_eq_iff hd]
  apply Complex.ext <;>
    simp only [left, add_re, add_im, sub_re, sub_im, mul_re, mul_im,
      neg_re, neg_im, ofReal_re, ofReal_im, one_re, one_im, I_re, I_im,
      mul_zero, zero_mul, mul_one, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  all_goals rw [Real.tanh_eq_sinh_div_cosh]
  all_goals field_simp
  all_goals rw [Real.cosh_eq, Real.sinh_eq]
  all_goals nlinarith

/-- The full arctangent on the positive semicircle has its exact branch and height. -/
theorem arctan_right (u : ℝ) :
    Complex.arctan (right u) = (Real.pi : ℂ) / 4 + (u : ℂ) / 2 * I := by
  change -I / 2 * Complex.log (cayley (right u)) = _
  rw [cayley_right, Complex.log_ofReal_mul (Real.exp_pos _) I_ne_zero,
    Real.log_exp, Complex.log_I]
  push_cast
  ring_nf
  simp only [I_sq]
  ring

/-- The negative semicircle has the opposite real branch and the same height. -/
theorem arctan_left (u : ℝ) :
    Complex.arctan (left u) = -(Real.pi : ℂ) / 4 + (u : ℂ) / 2 * I := by
  change -I / 2 * Complex.log (cayley (left u)) = _
  rw [cayley_left, Complex.log_ofReal_mul (Real.exp_pos _) (neg_ne_zero.mpr I_ne_zero),
    Real.log_exp, Complex.log_neg_I]
  push_cast
  ring_nf
  simp only [I_sq]
  ring

/-- The original map sends the positive semicircle to the full right vertical line. -/
theorem map_right (c : ℂ) (η u : ℝ) :
    AnalyticStripMap.map c η (right u) = c + η + ((2 * η / Real.pi * u : ℝ) : ℂ) * I := by
  rw [AnalyticStripMap.map, arctan_right]
  push_cast
  field_simp
  ring

/-- The negative semicircle maps to the full left vertical line, with the same height scale. -/
theorem map_left (c : ℂ) (η u : ℝ) :
    AnalyticStripMap.map c η (left u) = c - η + ((2 * η / Real.pi * u : ℝ) : ℂ) * I := by
  rw [AnalyticStripMap.map, arctan_left]
  push_cast
  field_simp
  ring

/-- The positive semicircle's angle, increasing with the vertical parameter. -/
def angle (u : ℝ) : ℝ := Real.arctan (Real.sinh u)

/-- The angular cosine is the hyperbolic secant, with no absolute-value ambiguity. -/
theorem cos_angle (u : ℝ) : Real.cos (angle u) = 1 / Real.cosh u := by
  rw [angle, Real.cos_arctan, ← Real.cosh_sq', Real.sqrt_sq (Real.cosh_pos u).le]

/-- The angular sine keeps the signed hyperbolic height coordinate. -/
theorem sin_angle (u : ℝ) : Real.sin (angle u) = Real.tanh u := by
  rw [angle, Real.sin_arctan, ← Real.cosh_sq', Real.sqrt_sq (Real.cosh_pos u).le,
    Real.tanh_eq_sinh_div_cosh]

/-- The positive arc is the literal complex circle map at its height angle. -/
theorem circleMap_angle (r u : ℝ) : circleMap 0 r (angle u) = (r : ℂ) * right u := by
  simp only [circleMap, zero_add, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, cos_angle, sin_angle, right]

/-- The negative arc has the reversed angular orientation. -/
theorem circleMap_pi_sub_angle (r u : ℝ) :
    circleMap 0 r (Real.pi - angle u) = (r : ℂ) * left u := by
  simp only [circleMap, zero_add, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_pi_sub, Real.sin_pi_sub, cos_angle, sin_angle,
    Complex.ofReal_neg, left]

/-- Every finite positive-arc parameter lies on the original unit circle. -/
theorem norm_right (u : ℝ) : ‖right u‖ = 1 := by
  have h := norm_circleMap_zero (1 : ℝ) (angle u)
  simpa [circleMap_angle] using h

/-- Every finite negative-arc parameter lies on the original unit circle. -/
theorem norm_left (u : ℝ) : ‖left u‖ = 1 := by
  have h := norm_circleMap_zero (1 : ℝ) (Real.pi - angle u)
  simpa [circleMap_pi_sub_angle] using h

/-- The exact angular Jacobian is positive and decays at both infinite ends. -/
theorem hasDerivAt_angle (u : ℝ) : HasDerivAt angle (1 / Real.cosh u) u := by
  have h := (Real.hasDerivAt_arctan (Real.sinh u)).comp u (Real.hasDerivAt_sinh u)
  convert! h using 1
  rw [← Real.cosh_sq']
  field_simp

/-- The right angular parametrization is strictly increasing. -/
theorem angle_strictMono : StrictMono angle :=
  Real.arctan_strictMono.comp Real.sinh_strictMono

/-- The positive semicircle is covered completely, without either infinite endpoint. -/
theorem range_angle : range angle = Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  change range (Real.arctan ∘ Real.sinh) = _
  rw [range_comp, Real.sinh_surjective.range_eq, image_univ, Real.range_arctan]

/-- The map is continuous at each finite boundary coordinate whose real part is nonzero. -/
theorem continuousAt_map_boundary (c : ℂ) (η : ℝ) {w : ℂ}
    (hre : w.re ≠ 0) : ContinuousAt (AnalyticStripMap.map c η) w := by
  have hd : 1 - w * I ≠ 0 := by
    intro h
    have h := congrArg Complex.im h
    simp at h
    exact hre h
  have hc : ContinuousAt cayley w := by
    unfold cayley
    fun_prop
  have him : (cayley w).im ≠ 0 := by
    rw [cayley_im]
    exact div_ne_zero (mul_ne_zero (by norm_num) hre) (normSq_pos.mpr hd).ne'
  have hs : cayley w ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inr him)
  have hl := hc.clog hs
  unfold AnalyticStripMap.map Complex.arctan
  exact continuousAt_const.add (continuousAt_const.mul (continuousAt_const.mul hl))

end
end RiemannGaussian.AnalyticStripBoundary
