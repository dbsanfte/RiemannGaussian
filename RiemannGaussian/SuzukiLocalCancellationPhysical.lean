/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiLocalCancellationKernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # The local Suzuki kernel in the physical arithmetic variable

The exact density cancellation is transported through a genuine change of
variables. This supplies the zero-mean input for integer-lattice estimates.
-/

namespace RiemannGaussian
noncomputable section
open MeasureTheory Set

/-- The unchanged physical signed weight, totalized to zero on nonpositive input
by its square-root denominator. Its arithmetic uses always have positive base. -/
def suzukiLocalPhysicalKernel (X y : ℝ) : ℝ :=
  suzukiLocalSignedKernel (Real.log (y / X)) / Real.sqrt y

/-- The physical kernel is continuous at every positive physical argument. -/
theorem continuousAt_suzukiLocalPhysicalKernel {X y : ℝ} (hX : 0 < X) (hy : 0 < y) :
    ContinuousAt (suzukiLocalPhysicalKernel X) y := by
  unfold suzukiLocalPhysicalKernel suzukiLocalSignedKernel suzukiLocalTriangle
  fun_prop (disch := positivity)

/-- The lower exterior and the left endpoint make zero contribution. -/
theorem suzukiLocalPhysicalKernel_eq_zero_of_le {X y : ℝ} (hX : 0 < X) (hy : y ≤ X) :
    suzukiLocalPhysicalKernel X y = 0 := by
  by_cases hy0 : 0 < y
  · unfold suzukiLocalPhysicalKernel
    rw [suzukiLocalSignedKernel_eq_zero_of_nonpos
      (Real.log_nonpos (div_nonneg hy0.le hX.le) ((div_le_one hX).mpr hy)), zero_div]
  · simp [suzukiLocalPhysicalKernel, Real.sqrt_eq_zero_of_nonpos (le_of_not_gt hy0)]

/-- The upper exterior and the right endpoint make zero contribution. -/
theorem suzukiLocalPhysicalKernel_eq_zero_of_eight_mul_le {X y : ℝ}
    (hX : 0 < X) (hy : 8 * X ≤ y) : suzukiLocalPhysicalKernel X y = 0 := by
  have hq : (8 : ℝ) ≤ y / X := (le_div_iff₀ hX).mpr (by linarith)
  have hl : 3 * Real.log 2 ≤ Real.log (y / X) := by
    have he : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [← he]
    exact Real.log_le_log (by norm_num) hq
  rw [suzukiLocalPhysicalKernel, suzukiLocalSignedKernel_eq_zero_of_three_mul_le hl, zero_div]

/-- The exponential Jacobian retains exactly the density normalization. -/
theorem suzukiLocalPhysicalKernel_exp_jacobian {X : ℝ} (hX : 0 < X) (v : ℝ) :
    suzukiLocalPhysicalKernel X (X * Real.exp v) * (X * Real.exp v) =
      Real.sqrt X * (Real.exp (v / 2) * suzukiLocalSignedKernel v) := by
  have hs : Real.sqrt (X * Real.exp v) ≠ 0 := by positivity
  have he : X * Real.exp v / X = Real.exp v := mul_div_cancel_left₀ _ hX.ne'
  rw [suzukiLocalPhysicalKernel, he, Real.log_exp]
  calc
    _ = suzukiLocalSignedKernel v * Real.sqrt (X * Real.exp v) := by
      field_simp
      rw [Real.sq_sqrt (show 0 ≤ X * Real.exp v by positivity)]
      ring
    _ = _ := by
      rw [Real.sqrt_mul hX.le, ← Real.exp_half]
      ring

/-- The signed kernel has zero real density integral in logarithmic coordinates. -/
theorem suzukiLocalSignedKernel_real_density_integral :
    (∫ v in (0 : ℝ)..3 * Real.log 2,
      Real.exp (v / 2) * suzukiLocalSignedKernel v) = 0 := by
  have he := suzukiLocalSignedKernel_transform_half
  rw [suzukiLocalSignedKernel_integral_eq_interval] at he
  have hc : (fun v : ℝ => Complex.exp ((1 / 2 : ℂ) * (v : ℂ)) *
      (suzukiLocalSignedKernel v : ℂ)) =
      fun v => ((Real.exp (v / 2) * suzukiLocalSignedKernel v : ℝ) : ℂ) := by
    funext v
    rw [show (1 / 2 : ℂ) * (v : ℂ) = ((v / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp, Complex.ofReal_mul]
  rw [hc, intervalIntegral.integral_ofReal] at he
  exact_mod_cast he

/-- The complete physical kernel has zero mean on its exact arithmetic support. -/
theorem suzukiLocalPhysicalKernel_integral_eq_zero {X : ℝ} (hX : 0 < X) :
    (∫ y in X..8 * X, suzukiLocalPhysicalKernel X y) = 0 := by
  have hc : ContinuousOn (suzukiLocalPhysicalKernel X)
      ((fun v : ℝ => X * Real.exp v) '' uIcc 0 (3 * Real.log 2)) := by
    rintro y ⟨v, _, rfl⟩
    exact (continuousAt_suzukiLocalPhysicalKernel hX (by positivity)).continuousWithinAt
  have he := intervalIntegral.integral_comp_mul_deriv'
    (a := 0) (b := 3 * Real.log 2)
    (f := fun v : ℝ => X * Real.exp v) (f' := fun v => X * Real.exp v)
    (g := suzukiLocalPhysicalKernel X)
    (fun v _ => (Real.hasDerivAt_exp v).const_mul X)
    (by fun_prop) hc
  have hexp : Real.exp (3 * Real.log 2) = (8 : ℝ) := by
    rw [show 3 * Real.log 2 = Real.log 2 + Real.log 2 + Real.log 2 by ring]
    norm_num [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  simp only [Real.exp_zero, mul_one, hexp] at he
  rw [show X * 8 = 8 * X by ring] at he
  rw [← he]
  simp only [Function.comp_def]
  simp_rw [suzukiLocalPhysicalKernel_exp_jacobian hX]
  rw [intervalIntegral.integral_const_mul, suzukiLocalSignedKernel_real_density_integral, mul_zero]

/-- The first physical branch retains its literal logarithmic coefficient. -/
theorem suzukiLocalPhysicalKernel_eq_first {X y : ℝ} (hX : 0 < X)
    (hlo : X ≤ y) (hhi : y ≤ 2 * X) :
    suzukiLocalPhysicalKernel X y = Real.sqrt 2 * Real.log (y / X) / Real.sqrt y := by
  have hq : 0 < y / X := div_pos (hX.trans_le hlo) hX
  have hl : 0 ≤ Real.log (y / X) := Real.log_nonneg ((one_le_div hX).mpr hlo)
  have hu : Real.log (y / X) ≤ Real.log 2 :=
    Real.log_le_log hq ((div_le_iff₀ hX).mpr hhi)
  rw [suzukiLocalPhysicalKernel, suzukiLocalSignedKernel_eq_first hl hu]

/-- The middle physical branch retains both coefficients before estimation. -/
theorem suzukiLocalPhysicalKernel_eq_middle {X y : ℝ} (hX : 0 < X)
    (hlo : 2 * X ≤ y) (hhi : y ≤ 4 * X) :
    suzukiLocalPhysicalKernel X y =
      ((2 * Real.sqrt 2 + 1) * Real.log 2 -
        (Real.sqrt 2 + 1) * Real.log (y / X)) / Real.sqrt y := by
  have hq : 0 < y / X := div_pos (by linarith) hX
  have hl : Real.log 2 ≤ Real.log (y / X) :=
    Real.log_le_log (by norm_num) ((le_div_iff₀ hX).mpr hlo)
  have hu : Real.log (y / X) ≤ 2 * Real.log 2 := by
    have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [← he]
    exact Real.log_le_log hq ((div_le_iff₀ hX).mpr hhi)
  rw [suzukiLocalPhysicalKernel, suzukiLocalSignedKernel_eq_middle hl hu]

/-- The last physical branch vanishes at the full eightfold cutoff. -/
theorem suzukiLocalPhysicalKernel_eq_last {X y : ℝ} (hX : 0 < X)
    (hlo : 4 * X ≤ y) (hhi : y ≤ 8 * X) :
    suzukiLocalPhysicalKernel X y =
      (Real.log (y / X) - 3 * Real.log 2) / Real.sqrt y := by
  have hq : 0 < y / X := div_pos (by linarith) hX
  have he4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have he8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hl : 2 * Real.log 2 ≤ Real.log (y / X) := by
    rw [← he4]
    exact Real.log_le_log (by norm_num) ((le_div_iff₀ hX).mpr hlo)
  have hu : Real.log (y / X) ≤ 3 * Real.log 2 := by
    rw [← he8]
    exact Real.log_le_log hq ((div_le_iff₀ hX).mpr hhi)
  rw [suzukiLocalPhysicalKernel, suzukiLocalSignedKernel_eq_last hl hu]

end
end RiemannGaussian
