/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianLocalizer
import RiemannGaussian.ZetaLogarithmicShiftAllowance

/-!
# Propagating a near-one zeta bound across a complete vertical strip

The Gaussian pays for every vertical displacement on both boundary
lines. Its boundedness throughout the strip supplies the independent
growth hypothesis for Phragmen--Lindelof. The resulting bound keeps
the original order-dependent logarithmic profile without adding a
power of the central height.
-/

namespace RiemannGaussian.ZetaGaussianStrip
noncomputable section
open Complex Filter Set ZetaGaussianLocalizer ZetaNearOneLogProfile
open ZetaLogarithmicShiftAllowance DirichletPowerParameters DerivativeOrderComparison
open scoped Topology

/-- The actual zeta norm is bounded by the exponential of the exact
all-height profile on every balanced near-one line. -/
theorem norm_zeta_le_exp_profile (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hs : s.re = line k) :
    ‖riemannZeta s‖ ≤ Real.exp (profile k s.im) := by
  rw [profile_eq_log, Real.exp_log (by linarith [one_le_majorant k s.im])]
  exact all_height_bound k hk hs

/-- At unit vertical scale the logarithmic shift price is at most two,
uniformly in height and derivative order. -/
theorem shiftCost_one_le_two (k : ℕ) (t : ℝ) : shiftCost k t 1 ≤ 2 := by
  have h := shiftCost_le k t 1
  norm_num only [abs_one, mul_one] at h
  apply h.trans
  apply (div_le_iff₀ (by linarith [two_le_height t] : 0 < height t)).mpr
  linarith [two_le_height t]

/-- Gaussian damping absorbs the complete affine logarithmic shift
on the left boundary with a constant additive allowance. -/
theorem left_boundary (k : ℕ) (hk : 1 ≤ k) (t : ℝ) {s : ℂ} (hs : s.re = line k) :
    ‖carrier t s‖ ≤ Real.exp (profile k t + 2) := by
  have hlo : 0 ≤ s.re := by rw [hs]; linarith [half_le_line k hk]
  have hhi : s.re < 1 := by rw [hs]; exact line_lt_one k
  have hs1 : s ≠ 1 := by intro h; simp [h] at hhi
  have hshift := profile_shift_le k t 1 (s.im - t)
  simp only [one_mul, add_sub_cancel] at hshift
  have hnorm := (norm_regularized_le_zeta hlo hs1).trans (norm_zeta_le_exp_profile k hk hs)
  rw [norm_carrier]
  have hm := mul_le_mul_of_nonneg_right
    (hnorm.trans (Real.exp_le_exp.mpr hshift)) (Real.exp_pos (s.re ^ 2 - (s.im - t) ^ 2)).le
  apply hm.trans
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hcost := mul_le_mul_of_nonneg_right (shiftCost_one_le_two k t) (abs_nonneg (s.im - t))
  have hsquare : |s.im - t| ^ 2 = (s.im - t) ^ 2 := sq_abs _
  nlinarith [sq_nonneg (|s.im - t| - 1)]

/-- The right boundary is controlled by the actual absolutely convergent
zeta series; its bound has no central-height dependence. -/
theorem right_boundary (t : ℝ) {s : ℂ} (hs : s.re = 3 / 2) :
    ‖carrier t s‖ ≤ 8 * Real.exp 3 := by
  have hs0 : 0 ≤ s.re := by rw [hs]; norm_num
  have hs1 : s ≠ 1 := by intro h; norm_num [h] at hs
  have hnorm := (norm_regularized_le_zeta hs0 hs1).trans
    ((norm_riemannZeta_safeLine_le_mass hs).trans staticContourSafeZetaDirichletMass_le_eight)
  rw [norm_carrier]
  apply mul_le_mul hnorm _ (Real.exp_pos _).le (by norm_num)
  apply Real.exp_le_exp.mpr
  rw [hs]
  nlinarith [sq_nonneg (s.im - t)]

/-- The actual Gaussian carrier is differentiable inside the complete
vertical strip and continuous on its closure, including over the removed pole. -/
theorem diffContOnCl_carrier (k : ℕ) (hk : 1 ≤ k) (t : ℝ) :
    DiffContOnCl ℂ (carrier t) (Complex.re ⁻¹' Ioo (line k) (3 / 2)) := by
  apply DifferentiableOn.diffContOnCl
  have hsub : closure (Complex.re ⁻¹' Ioo (line k) (3 / 2)) ⊆
      Complex.re ⁻¹' Ici (line k) :=
    closure_minimal (fun _ hw => hw.1.le) (isClosed_Ici.preimage Complex.continuous_re)
  intro s hs
  apply (differentiableAt_carrier t (add_one_ne_zero ?_)).differentiableWithinAt
  have h := hsub hs
  change line k ≤ s.re at h
  linarith [half_le_line k hk]

/-- The growth hypothesis of the strip maximum principle is discharged
by the independent coarse polynomial zeta bound and full Gaussian damping. -/
theorem carrier_growth (k : ℕ) (hk : 1 ≤ k) (t : ℝ) :
    ∃ c < Real.pi / (3 / 2 - line k), ∃ B : ℝ,
      carrier t =O[comap (abs ∘ Complex.im) atTop ⊓
        𝓟 (Complex.re ⁻¹' Ioo (line k) (3 / 2))]
        (fun s : ℂ => Real.exp (B * Real.exp (c * |s.im|))) := by
  refine ⟨0, div_pos Real.pi_pos (by linarith [line_lt_one k]), 0, ?_⟩
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨16 * Real.exp 3 * (1 + (|t| + 22) ^ 2), ?_⟩
  apply Filter.Eventually.filter_mono inf_le_right
  rw [Filter.eventually_principal]
  intro s hs
  simp only [zero_mul, Real.exp_zero, norm_one, mul_one]
  exact carrier_bounded t ((half_le_line k hk).trans hs.1.le) hs.2.le

/-- Both boundary estimates propagate across the entire closed strip.
The cost is additive in the logarithm, uniform in order and height. -/
theorem carrier_bound (k : ℕ) (hk : 1 ≤ k) (t : ℝ) {s : ℂ}
    (hlo : line k ≤ s.re) (hhi : s.re ≤ 3 / 2) :
    ‖carrier t s‖ ≤ Real.exp (profile k t + 10) := by
  apply PhragmenLindelof.vertical_strip (diffContOnCl_carrier k hk t)
    (carrier_growth k hk t) _ _ hlo hhi
  · intro w hw
    exact (left_boundary k hk t hw).trans (Real.exp_le_exp.mpr (by linarith))
  · intro w hw
    apply (right_boundary t hw).trans
    have h8 : (8 : ℝ) ≤ Real.exp 7 := by linarith [Real.add_one_le_exp (7 : ℝ)]
    calc
      8 * Real.exp 3 ≤ Real.exp 7 * Real.exp 3 :=
        mul_le_mul_of_nonneg_right h8 (Real.exp_pos _).le
      _ = Real.exp 10 := by rw [← Real.exp_add]; norm_num
      _ ≤ Real.exp (profile k t + 10) :=
        Real.exp_le_exp.mpr (by linarith [profile_nonneg k t])

end
end RiemannGaussian.ZetaGaussianStrip
