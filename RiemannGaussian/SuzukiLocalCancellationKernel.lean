/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiLocalCancellation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The fixed local Suzuki kernel and its mode multiplier

Piecewise evaluation and mode retention for the exact signed prime-band
kernel. These identities do not bound the signed arithmetic fluctuation.
-/

namespace RiemannGaussian
noncomputable section

/-- On its ascending half, the triangular kernel equals its argument. -/
theorem suzukiLocalTriangle_eq_self {h v : ℝ} (hv : 0 ≤ v) (hvh : v ≤ h) :
    suzukiLocalTriangle h v = v := by
  unfold suzukiLocalTriangle
  rw [abs_of_nonpos (by linarith), max_eq_right (by linarith)]
  ring

/-- On its descending half, the triangular kernel equals `2*h-v`. -/
theorem suzukiLocalTriangle_eq_two_mul_sub {h v : ℝ} (hhv : h ≤ v) (hv : v ≤ 2 * h) :
    suzukiLocalTriangle h v = 2 * h - v := by
  unfold suzukiLocalTriangle
  rw [abs_of_nonneg (by linarith), max_eq_right (by linarith)]
  ring

/-- The signed kernel vanishes before the first packet starts. -/
theorem suzukiLocalSignedKernel_eq_zero_of_nonpos {v : ℝ} (hv : v ≤ 0) :
    suzukiLocalSignedKernel v = 0 := by
  have hh : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [suzukiLocalSignedKernel, suzukiLocalTriangle_eq_zero_of_nonpos hh hv,
    suzukiLocalTriangle_eq_zero_of_nonpos hh (by linarith)]
  ring

/-- The signed kernel vanishes after the second packet ends. -/
theorem suzukiLocalSignedKernel_eq_zero_of_three_mul_le {v : ℝ}
    (hv : 3 * Real.log 2 ≤ v) : suzukiLocalSignedKernel v = 0 := by
  have hh : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [suzukiLocalSignedKernel,
    suzukiLocalTriangle_eq_zero_of_two_mul_le hh (by linarith),
    suzukiLocalTriangle_eq_zero_of_two_mul_le hh (by linarith)]
  ring

/-- The first band of the fixed signed kernel. -/
theorem suzukiLocalSignedKernel_eq_first {v : ℝ} (hv : 0 ≤ v) (hvh : v ≤ Real.log 2) :
    suzukiLocalSignedKernel v = Real.sqrt 2 * v := by
  rw [suzukiLocalSignedKernel, suzukiLocalTriangle_eq_self hv hvh,
    suzukiLocalTriangle_eq_zero_of_nonpos (Real.log_nonneg (by norm_num)) (by linarith)]
  ring

/-- The overlap band of the fixed signed kernel, with both source coefficients. -/
theorem suzukiLocalSignedKernel_eq_middle {v : ℝ} (hl : Real.log 2 ≤ v)
    (hu : v ≤ 2 * Real.log 2) :
    suzukiLocalSignedKernel v =
      (2 * Real.sqrt 2 + 1) * Real.log 2 - (Real.sqrt 2 + 1) * v := by
  rw [suzukiLocalSignedKernel, suzukiLocalTriangle_eq_two_mul_sub hl hu,
    suzukiLocalTriangle_eq_self (by linarith) (by linarith)]
  ring

/-- The final band of the fixed signed kernel. -/
theorem suzukiLocalSignedKernel_eq_last {v : ℝ} (hl : 2 * Real.log 2 ≤ v)
    (hu : v ≤ 3 * Real.log 2) :
    suzukiLocalSignedKernel v = v - 3 * Real.log 2 := by
  rw [suzukiLocalSignedKernel,
    suzukiLocalTriangle_eq_zero_of_two_mul_le (Real.log_nonneg (by norm_num)) hl,
    suzukiLocalTriangle_eq_two_mul_sub (by linarith) (by linarith)]
  ring

/-- The exact exponential-mode multiplier of the four-shift signal filter. -/
def suzukiLocalModeMultiplier (lambda : ℂ) : ℂ :=
  (Complex.exp (lambda * (Real.log 2 : ℂ)) - (Real.sqrt 2 : ℂ)) *
    (Complex.exp (lambda * (Real.log 2 : ℂ)) - 1) ^ 2

private theorem local_complex_exp_shift (lambda : ℂ) (t : ℝ) (n : ℕ) :
    Complex.exp (lambda * ((t + n * Real.log 2 : ℝ) : ℂ)) =
      Complex.exp (lambda * (t : ℂ)) * Complex.exp (lambda * (Real.log 2 : ℂ)) ^ n := by
  push_cast
  rw [show lambda * ((t : ℂ) + n * (Real.log 2 : ℂ)) =
    lambda * (t : ℂ) + n * (lambda * (Real.log 2 : ℂ)) by ring,
    Complex.exp_add, Complex.exp_nat_mul]

/-- The filter acts on a complex exponential by the stated polynomial,
without using or interchanging any expansion over zeta zeros. -/
theorem suzukiLocalModeMultiplier_eq_four_shifts (lambda : ℂ) (t : ℝ) :
    -(Real.sqrt 2 : ℂ) * Complex.exp (lambda * (t : ℂ)) +
      (1 + 2 * (Real.sqrt 2 : ℂ)) *
        Complex.exp (lambda * ((t + Real.log 2 : ℝ) : ℂ)) -
      (2 + (Real.sqrt 2 : ℂ)) *
        Complex.exp (lambda * ((t + 2 * Real.log 2 : ℝ) : ℂ)) +
      Complex.exp (lambda * ((t + 3 * Real.log 2 : ℝ) : ℂ)) =
        suzukiLocalModeMultiplier lambda * Complex.exp (lambda * (t : ℂ)) := by
  have h1 := local_complex_exp_shift lambda t 1
  have h2 := local_complex_exp_shift lambda t 2
  have h3 := local_complex_exp_shift lambda t 3
  norm_num only [Nat.cast_one, Nat.cast_ofNat, one_mul, pow_one] at h1 h2 h3
  rw [h1, h2, h3, suzukiLocalModeMultiplier]
  ring

/-- Every mode in the open right-half zero range has shift modulus strictly
between `1` and `sqrt 2`; neither cancellation factor vanishes there. -/
theorem suzukiLocalMode_shift_norm_bounds {lambda : ℂ} (hlo : 0 < lambda.re)
    (hhi : lambda.re < 1 / 2) :
    1 < ‖Complex.exp (lambda * (Real.log 2 : ℂ))‖ ∧
      ‖Complex.exp (lambda * (Real.log 2 : ℂ))‖ < Real.sqrt 2 := by
  have hh : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn : ‖Complex.exp (lambda * (Real.log 2 : ℂ))‖ =
      Real.exp (lambda.re * Real.log 2) := by
    simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
  rw [hn]
  constructor
  · exact Real.one_lt_exp_iff.mpr (mul_pos hlo hh)
  · have h := Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_right hhi hh)
    have he : Real.exp ((1 / 2 : ℝ) * Real.log 2) = Real.sqrt 2 := by
      rw [show (1 / 2 : ℝ) * Real.log 2 = Real.log 2 / 2 by ring,
        Real.exp_half, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    rwa [he] at h

/-- The density/history filter retains every exponential mode in the open
right-half zero range. This is mode retention, not a prime-fluctuation bound. -/
theorem suzukiLocalModeMultiplier_ne_zero {lambda : ℂ} (hlo : 0 < lambda.re)
    (hhi : lambda.re < 1 / 2) : suzukiLocalModeMultiplier lambda ≠ 0 := by
  obtain ⟨hl, hu⟩ := suzukiLocalMode_shift_norm_bounds hlo hhi
  apply mul_ne_zero
  · apply sub_ne_zero.mpr
    intro he
    have hn := congrArg norm he
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2)] at hn
    linarith
  · apply pow_ne_zero
    apply sub_ne_zero.mpr
    intro he
    have hn := congrArg norm he
    simp only [norm_one] at hn
    linarith

private theorem local_integral_affine_exp (lambda A B : ℂ) (hlambda : lambda ≠ 0)
    (a b : ℝ) :
    (∫ x in a..b, Complex.exp (lambda * (x : ℂ)) * (A * (x : ℂ) + B)) =
      Complex.exp (lambda * (b : ℂ)) *
          ((A * lambda) * (b : ℂ) + (B * lambda - A)) / lambda ^ 2 -
        Complex.exp (lambda * (a : ℂ)) *
          ((A * lambda) * (a : ℂ) + (B * lambda - A)) / lambda ^ 2 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x _
    have he := (Complex.hasDerivAt_exp (lambda * (x : ℂ))).comp x
      (((hasDerivAt_id (x : ℂ)).const_mul lambda).comp_ofReal)
    have ha := (((hasDerivAt_id (x : ℂ)).const_mul (A * lambda)).add_const
      (B * lambda - A)).comp_ofReal
    convert (he.mul ha).div_const (lambda ^ 2) using 1
    · rfl
    · dsimp
      field_simp [hlambda]
      ring
  · exact (by fun_prop : Continuous (fun x : ℝ =>
      Complex.exp (lambda * (x : ℂ)) * (A * (x : ℂ) + B))).intervalIntegrable _ _

/-- The exact transform of the compact signed kernel on its full support.
The parameter zero is excluded here; its removable value is separate. -/
theorem suzukiLocalSignedKernel_interval_transform {lambda : ℂ} (hlambda : lambda ≠ 0) :
    (∫ v in (0 : ℝ)..(3 * Real.log 2),
      Complex.exp (lambda * (v : ℂ)) * (suzukiLocalSignedKernel v : ℂ)) =
      ((Real.sqrt 2 : ℂ) - Complex.exp (lambda * (Real.log 2 : ℂ))) *
        (Complex.exp (lambda * (Real.log 2 : ℂ)) - 1) ^ 2 / lambda ^ 2 := by
  let f : ℝ → ℂ := fun v =>
    Complex.exp (lambda * (v : ℂ)) * (suzukiLocalSignedKernel v : ℂ)
  have hc : Continuous f := by
    dsimp [f, suzukiLocalSignedKernel, suzukiLocalTriangle]
    fun_prop
  have hh : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h1 : (∫ v in (0 : ℝ)..Real.log 2, f v) =
      ∫ v in (0 : ℝ)..Real.log 2,
        Complex.exp (lambda * (v : ℂ)) * ((Real.sqrt 2 : ℂ) * v + 0) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le hh] at hv
    dsimp [f]
    rw [suzukiLocalSignedKernel_eq_first hv.1 hv.2]
    push_cast
    ring
  have h2 : (∫ v in Real.log 2..2 * Real.log 2, f v) =
      ∫ v in Real.log 2..2 * Real.log 2,
        Complex.exp (lambda * (v : ℂ)) *
          (-((Real.sqrt 2 : ℂ) + 1) * v +
            (2 * (Real.sqrt 2 : ℂ) + 1) * (Real.log 2 : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le (by linarith : Real.log 2 ≤ 2 * Real.log 2)] at hv
    dsimp [f]
    rw [suzukiLocalSignedKernel_eq_middle hv.1 hv.2]
    push_cast
    ring
  have h3 : (∫ v in 2 * Real.log 2..3 * Real.log 2, f v) =
      ∫ v in 2 * Real.log 2..3 * Real.log 2,
        Complex.exp (lambda * (v : ℂ)) * (1 * v + -3 * (Real.log 2 : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le (by linarith : 2 * Real.log 2 ≤ 3 * Real.log 2)] at hv
    dsimp [f]
    rw [suzukiLocalSignedKernel_eq_last hv.1 hv.2]
    push_cast
    ring
  have hsplit : (∫ v in (0 : ℝ)..(3 * Real.log 2), f v) =
      (∫ v in (0 : ℝ)..Real.log 2, f v) +
        (∫ v in Real.log 2..2 * Real.log 2, f v) +
        (∫ v in 2 * Real.log 2..3 * Real.log 2, f v) := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals
        (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  change (∫ v in (0 : ℝ)..(3 * Real.log 2), f v) = _
  rw [hsplit, h1, h2, h3, local_integral_affine_exp _ _ _ hlambda,
    local_integral_affine_exp _ _ _ hlambda, local_integral_affine_exp _ _ _ hlambda]
  have he2 := local_complex_exp_shift lambda 0 2
  have he3 := local_complex_exp_shift lambda 0 3
  norm_num only [zero_add, zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    one_mul, Nat.cast_ofNat] at he2 he3
  rw [he2, he3]
  push_cast
  simp only [mul_zero, Complex.exp_zero, zero_mul]
  field_simp
  ring

/-- The real-line kernel integral is exactly its finite support integral,
including the zero parameter. -/
theorem suzukiLocalSignedKernel_integral_eq_interval (lambda : ℂ) :
    (∫ v : ℝ, Complex.exp (lambda * (v : ℂ)) * (suzukiLocalSignedKernel v : ℂ)) =
      ∫ v in (0 : ℝ)..(3 * Real.log 2),
        Complex.exp (lambda * (v : ℂ)) * (suzukiLocalSignedKernel v : ℂ) := by
  have hs : ∀ v : ℝ, v ∉ Set.Ioc 0 (3 * Real.log 2) →
      Complex.exp (lambda * (v : ℂ)) * (suzukiLocalSignedKernel v : ℂ) = 0 := by
    intro v hv
    by_cases h0 : v ≤ 0
    · rw [suzukiLocalSignedKernel_eq_zero_of_nonpos h0, Complex.ofReal_zero, mul_zero]
    · have h3 : 3 * Real.log 2 ≤ v := by
        by_contra h
        exact hv ⟨lt_of_not_ge h0, (lt_of_not_ge h).le⟩
      rw [suzukiLocalSignedKernel_eq_zero_of_three_mul_le h3, Complex.ofReal_zero, mul_zero]
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hs,
    ← intervalIntegral.integral_of_le (show 0 ≤ 3 * Real.log 2 by positivity)]

/-- The full real-line kernel transform equals its compact-support formula. -/
theorem suzukiLocalSignedKernel_transform {lambda : ℂ} (hlambda : lambda ≠ 0) :
    (∫ v : ℝ, Complex.exp (lambda * (v : ℂ)) * (suzukiLocalSignedKernel v : ℂ)) =
      ((Real.sqrt 2 : ℂ) - Complex.exp (lambda * (Real.log 2 : ℂ))) *
        (Complex.exp (lambda * (Real.log 2 : ℂ)) - 1) ^ 2 / lambda ^ 2 := by
  rw [suzukiLocalSignedKernel_integral_eq_interval]
  exact suzukiLocalSignedKernel_interval_transform hlambda

/-- The quotient in the transform has removable value `(sqrt 2-1)*(log 2)^2`
at zero, rather than its field-totalized value at a zero denominator. -/
theorem suzukiLocalSignedKernel_transform_removable :
    Filter.Tendsto (fun lambda : ℂ =>
      ((Real.sqrt 2 : ℂ) - Complex.exp (lambda * (Real.log 2 : ℂ))) *
        (Complex.exp (lambda * (Real.log 2 : ℂ)) - 1) ^ 2 / lambda ^ 2)
      (nhdsWithin 0 ({0}ᶜ))
      (nhds (((Real.sqrt 2 : ℂ) - 1) * (Real.log 2 : ℂ) ^ 2)) := by
  have hd : HasDerivAt (fun z : ℂ => Complex.exp (z * (Real.log 2 : ℂ)))
      (Real.log 2 : ℂ) 0 := by
    convert (Complex.hasDerivAt_exp (0 * (Real.log 2 : ℂ))).comp 0
      ((hasDerivAt_id (0 : ℂ)).mul_const (Real.log 2 : ℂ)) using 1
    · rfl
    · simp only [zero_mul, Complex.exp_zero, one_mul]
  have hq : Filter.Tendsto (fun z : ℂ =>
      (Complex.exp (z * (Real.log 2 : ℂ)) - 1) / z)
      (nhdsWithin 0 ({0}ᶜ)) (nhds (Real.log 2 : ℂ)) := by
    convert hd.tendsto_slope using 1
    ext z
    rw [slope_def_field]
    simp only [zero_mul, Complex.exp_zero, sub_zero]
  have he : Filter.Tendsto (fun z : ℂ => Complex.exp (z * (Real.log 2 : ℂ)))
      (nhdsWithin 0 ({0}ᶜ)) (nhds (Complex.exp (0 * (Real.log 2 : ℂ)))) :=
    hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hc : Filter.Tendsto (fun _ : ℂ => (Real.sqrt 2 : ℂ))
      (nhdsWithin 0 ({0}ᶜ)) (nhds (Real.sqrt 2 : ℂ)) := tendsto_const_nhds
  have hp := (hc.sub he).mul (hq.pow 2)
  simp only [zero_mul, Complex.exp_zero] at hp
  convert hp using 1
  ext z
  ring

/-- The actual zero-parameter integral equals the removable transform value. -/
theorem suzukiLocalSignedKernel_interval_transform_zero :
    (∫ v in (0 : ℝ)..(3 * Real.log 2), (suzukiLocalSignedKernel v : ℂ)) =
      ((Real.sqrt 2 : ℂ) - 1) * (Real.log 2 : ℂ) ^ 2 := by
  let f : ℂ → ℝ → ℂ := fun z v =>
    Complex.exp (z * (v : ℂ)) * (suzukiLocalSignedKernel v : ℂ)
  have hc : Continuous f.uncurry := by
    dsimp [f, Function.uncurry, suzukiLocalSignedKernel, suzukiLocalTriangle]
    fun_prop
  have hi := continuous_parametric_integral_of_continuous
    (μ := MeasureTheory.volume) hc (s := Set.Icc 0 (3 * Real.log 2)) isCompact_Icc
  have heq (z : ℂ) : (∫ v in Set.Icc 0 (3 * Real.log 2), f z v) =
      ∫ v in (0 : ℝ)..(3 * Real.log 2), f z v := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (show 0 ≤ 3 * Real.log 2 by positivity)]
  have heq0 : (∫ v in Set.Icc 0 (3 * Real.log 2), (suzukiLocalSignedKernel v : ℂ)) =
      ∫ v in (0 : ℝ)..(3 * Real.log 2), (suzukiLocalSignedKernel v : ℂ) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (show 0 ≤ 3 * Real.log 2 by positivity)]
  have hlim0 : Filter.Tendsto
      (fun z : ℂ => ∫ v in (0 : ℝ)..(3 * Real.log 2), f z v)
      (nhdsWithin 0 ({0}ᶜ))
      (nhds (∫ v in (0 : ℝ)..(3 * Real.log 2), (suzukiLocalSignedKernel v : ℂ))) := by
    simpa only [heq, f, zero_mul, Complex.exp_zero, one_mul, heq0] using
      ((hi.continuousAt (x := (0 : ℂ))).tendsto.mono_left
        (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ))))
  have hlim := suzukiLocalSignedKernel_transform_removable
  have hlim' : Filter.Tendsto
      (fun z : ℂ => ∫ v in (0 : ℝ)..(3 * Real.log 2), f z v)
      (nhdsWithin 0 ({0}ᶜ))
      (nhds (((Real.sqrt 2 : ℂ) - 1) * (Real.log 2 : ℂ) ^ 2)) := by
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : z ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hz
    exact (suzukiLocalSignedKernel_interval_transform hz0).symm
  exact tendsto_nhds_unique hlim0 hlim'

/-- The full real-line zero-parameter integral has the removable value. -/
theorem suzukiLocalSignedKernel_transform_zero :
    (∫ v : ℝ, (suzukiLocalSignedKernel v : ℂ)) =
      ((Real.sqrt 2 : ℂ) - 1) * (Real.log 2 : ℂ) ^ 2 := by
  have h := suzukiLocalSignedKernel_integral_eq_interval 0
  simp only [zero_mul, Complex.exp_zero, one_mul] at h
  rw [h]
  exact suzukiLocalSignedKernel_interval_transform_zero

/-- The density exponent `1/2` is canceled by the full real-line kernel. -/
theorem suzukiLocalSignedKernel_transform_half :
    (∫ v : ℝ, Complex.exp ((1 / 2 : ℂ) * (v : ℂ)) *
      (suzukiLocalSignedKernel v : ℂ)) = 0 := by
  rw [suzukiLocalSignedKernel_transform (by norm_num : (1 / 2 : ℂ) ≠ 0)]
  have he : Complex.exp ((1 / 2 : ℂ) * (Real.log 2 : ℂ)) = (Real.sqrt 2 : ℂ) := by
    have hr : Real.exp ((1 / 2 : ℝ) * Real.log 2) = Real.sqrt 2 := by
      rw [show (1 / 2 : ℝ) * Real.log 2 = Real.log 2 / 2 by ring,
        Real.exp_half, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    rw [show (1 / 2 : ℂ) * (Real.log 2 : ℂ) =
      (((1 / 2 : ℝ) * Real.log 2 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_exp, hr]
  rw [he, sub_self, zero_mul, zero_div]

end
end RiemannGaussian
