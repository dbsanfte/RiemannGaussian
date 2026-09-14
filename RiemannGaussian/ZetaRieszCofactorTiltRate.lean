/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszGrowingCofactor

/-!
# Exact scalar cofactor tilt-rate audit

The geometric rate suggested by a general positive factorial tilt has a
unique explicit minimizer. This scalar audit matches the two already proved
unit and three-halves arithmetic estimates. A general-tilt spatial estimate
is still needed before the other scalar rates yield arithmetic bounds.
The exceptional scalar contact is not a zero-location conclusion.
-/

namespace RiemannGaussian.ZetaRieszCofactorTiltRate
noncomputable section

/-- The geometric base suggested by a full positive tilt, before
cofactor growth and fixed multiplicative constants are charged. This is
an exponent audit, not a bound for an arithmetic sum. -/
def tiltRate (u q : ℝ) : ℝ := Real.exp ((2 - 2 * q) * Real.log u) / q

/-- The exact stationary positive tilt at a source scale in (0,1). -/
def optimalTilt (u : ℝ) : ℝ := 1 / (-2 * Real.log u)

/-- The exact minimum of the scalar tilt-rate expression. -/
def minimumRate (u : ℝ) : ℝ := (-2 * Real.log u) * Real.exp (1 + 2 * Real.log u)

/-- The elementary exponential tangent inequality identifies the
minimum for every positive tilt, without searching a parameter grid. -/
theorem rate_minimum (h : ℝ) {q : ℝ} (hq : 0 < q) :
    h * Real.exp (1 - h) ≤ Real.exp (h * (q - 1)) / q := by
  apply (le_div_iff₀ hq).mpr
  have ht := Real.add_one_le_exp (h * q - 1)
  have hm := mul_le_mul_of_nonneg_right ht (Real.exp_pos (1 - h)).le
  have he : Real.exp (h * q - 1) * Real.exp (1 - h) = Real.exp (h * (q - 1)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hm
  nlinarith

/-- The stationary tilt attains that exact minimum. -/
theorem rate_at_optimum {h : ℝ} (hh : 0 < h) :
    Real.exp (h * (1 / h - 1)) / (1 / h) = h * Real.exp (1 - h) := by
  have he : h * (1 / h - 1) = 1 - h := by field_simp
  rw [he]
  field_simp

/-- The optimal scalar rate never exceeds one. -/
theorem minimum_rate_le_one (h : ℝ) :
    h * Real.exp (1 - h) ≤ 1 := by
  have ht := Real.add_one_le_exp (h - 1)
  have hm := mul_le_mul_of_nonneg_right ht (Real.exp_pos (1 - h)).le
  have he : Real.exp (h - 1) * Real.exp (1 - h) = 1 := by rw [← Real.exp_add]; simp
  rw [he] at hm
  nlinarith

/-- On the actual source-scale interval the ideal positive tilt exists. -/
theorem optimalTilt_pos {u : ℝ} (hu : 0 < u) (hu1 : u < 1) : 0 < optimalTilt u := by
  have hl := Real.log_neg hu hu1
  exact one_div_pos.mpr (by linarith)

/-- The mathematically defined tilt is optimal over every positive
candidate, including candidates not in any finite numerical family. -/
theorem minimumRate_le_tiltRate (u : ℝ) {q : ℝ} (hq : 0 < q) :
    minimumRate u ≤ tiltRate u q := by
  have h := rate_minimum (-2 * Real.log u) hq
  unfold minimumRate tiltRate
  convert h using 1 <;> congr 2 <;> ring

/-- The scalar optimum is attained at the exact analytic tilt. -/
theorem tiltRate_optimal {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    tiltRate u (optimalTilt u) = minimumRate u := by
  have hl := Real.log_neg hu hu1
  have h := rate_at_optimum (show 0 < -2 * Real.log u by linarith)
  unfold tiltRate optimalTilt minimumRate
  convert h using 1 <;> congr 2 <;> ring

/-- The optimal scalar rate is strictly below one away from its
single tangent contact. -/
theorem minimum_rate_lt_one {h : ℝ} (hne : h ≠ 1) :
    h * Real.exp (1 - h) < 1 := by
  have ht := Real.add_one_lt_exp (show h - 1 ≠ 0 by exact sub_ne_zero.mpr hne)
  have hm := mul_lt_mul_of_pos_right ht (Real.exp_pos (1 - h))
  have he : Real.exp (h - 1) * Real.exp (1 - h) = 1 := by rw [← Real.exp_add]; simp
  rw [he] at hm
  nlinarith

/-- At the exact transition source scale every positive tilt has a
scalar rate at least one. Parameter searching cannot beat this envelope. -/
theorem critical_scale_rate {q : ℝ} (hq : 0 < q) :
    1 ≤ tiltRate (Real.exp (-(1 / 2 : ℝ))) q := by
  have h := minimumRate_le_tiltRate (Real.exp (-(1 / 2 : ℝ))) hq
  norm_num [minimumRate, Real.log_exp] at h
  exact h

/-- At every other source scale in (0,1), the exact optimum improves
the scalar geometric base. This does not discharge an arithmetic bound. -/
theorem minimumRate_lt_one {u : ℝ} (hu : 0 < u)
    (hcrit : u ≠ Real.exp (-(1 / 2 : ℝ))) : minimumRate u < 1 := by
  have hn : -2 * Real.log u ≠ 1 := by
    intro he
    have hl : Real.log u = -(1 / 2 : ℝ) := by linarith
    exact hcrit (by rw [← hl, Real.exp_log hu])
  have h := minimum_rate_lt_one hn
  unfold minimumRate
  convert h using 1; congr 2; ring

/-- An exact analytical test for all positive tilts: a strict scalar
geometric saving exists precisely away from the single transition scale. -/
theorem exists_improving_tilt_iff {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    (∃ q : ℝ, 0 < q ∧ tiltRate u q < 1) ↔ u ≠ Real.exp (-(1 / 2 : ℝ)) := by
  constructor
  · rintro ⟨q, hq, hlt⟩ he
    subst u
    exact (not_lt_of_ge (critical_scale_rate hq)) hlt
  · intro hcrit
    exact ⟨optimalTilt u, optimalTilt_pos hu hu1,
      (tiltRate_optimal hu hu1).trans_lt (minimumRate_lt_one hu hcrit)⟩

/-- Equality in the exponential tangent inequality characterizes the
unique minimizing tilt, rather than only exhibiting one minimizer. -/
theorem rate_minimum_eq_iff {h q : ℝ} (hh : 0 < h) (hq : 0 < q) :
    h * Real.exp (1 - h) = Real.exp (h * (q - 1)) / q ↔ q = 1 / h := by
  constructor
  · intro heq
    by_contra hne
    have hn : h * q - 1 ≠ 0 := by
      intro hzero
      apply hne
      apply (eq_div_iff hh.ne').mpr
      nlinarith
    have ht := Real.add_one_lt_exp hn
    have hm := mul_lt_mul_of_pos_right ht (Real.exp_pos (1 - h))
    have he : Real.exp (h * q - 1) * Real.exp (1 - h) = Real.exp (h * (q - 1)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he] at hm
    have hlt : h * Real.exp (1 - h) < Real.exp (h * (q - 1)) / q := by
      apply (lt_div_iff₀ hq).mpr
      nlinarith
    exact (ne_of_lt hlt) heq
  · intro he
    subst q
    exact (rate_at_optimum hh).symm

/-- The positive minimizer is unique at each actual source scale. -/
theorem minimumRate_eq_tiltRate_iff {u q : ℝ} (hu : 0 < u) (hu1 : u < 1) (hq : 0 < q) :
    minimumRate u = tiltRate u q ↔ q = optimalTilt u := by
  have hl := Real.log_neg hu hu1
  have h := rate_minimum_eq_iff (show 0 < -2 * Real.log u by linarith) hq
  unfold minimumRate tiltRate optimalTilt
  rw [show 1 + 2 * Real.log u = 1 - (-2 * Real.log u) by ring,
    show (2 - 2 * q) * Real.log u = (-2 * Real.log u) * (q - 1) by ring]
  exact h

/-- The older unit tilt has geometric base exactly one at every
source scale; its decay comes only from the polynomial damping. -/
theorem tiltRate_one (u : ℝ) : tiltRate u 1 = 1 := by norm_num [tiltRate]

/-- The three-halves scalar rate is exactly the base in the independently
proved exponential-budget cofactor estimate. -/
theorem tiltRate_three_halves {u : ℝ} (hu : 0 < u) :
    tiltRate u (3 / 2) = (2 / 3) / u := by
  unfold tiltRate
  rw [show (2 - 2 * (3 / 2 : ℝ)) * Real.log u = -Real.log u by ring,
    Real.exp_neg, Real.exp_log hu]
  ring

/-- At every actual right-half-zero source scale the ideal tilt lies
above one half, the boundary for the power-prefix growth calculation. -/
theorem optimalTilt_gt_half {u : ℝ} (hu : 1 / 2 < u) (hu1 : u < 1) :
    1 / 2 < optimalTilt u := by
  have hu0 : 0 < u := by linarith
  have hl := Real.log_lt_log (by norm_num : (0 : ℝ) < 1 / 2) hu
  norm_num [Real.log_div] at hl
  have h2 := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
  have hn := Real.log_neg hu0 hu1
  unfold optimalTilt
  apply (lt_div_iff₀ (by linarith : 0 < -2 * Real.log u)).mpr
  nlinarith

end
end RiemannGaussian.ZetaRieszCofactorTiltRate
