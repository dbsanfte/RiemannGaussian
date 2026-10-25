/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiLocalCancellationPhysical

/-!
# The surviving first logarithmic density moment

The fixed local kernel cancels the density but retains its first logarithmic
moment. Both values are exact physical-variable integrals; no prime estimate
is inferred from them.
-/

set_option warningAsError true

namespace RiemannGaussian
noncomputable section
open MeasureTheory Set

private theorem integral_quadratic_exp_half (A B a b : ℝ) :
    (∫ v in a..b, Real.exp (v / 2) * (A * v ^ 2 + B * v)) =
      Real.exp (b / 2) * (2 * A * b ^ 2 + (2 * B - 8 * A) * b + 16 * A - 4 * B) -
        Real.exp (a / 2) * (2 * A * a ^ 2 + (2 * B - 8 * A) * a + 16 * A - 4 * B) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun v => Real.exp (v / 2) *
      (2 * A * v ^ 2 + (2 * B - 8 * A) * v + 16 * A - 4 * B))
  · intro v _
    have he := (Real.hasDerivAt_exp (v / 2)).comp v ((hasDerivAt_id v).div_const 2)
    have hp := ((((hasDerivAt_id v).pow 2).const_mul (2 * A)).add
      ((hasDerivAt_id v).const_mul (2 * B - 8 * A))).add_const (16 * A - 4 * B)
    convert he.mul hp using 1
    · funext x
      dsimp
      ring
    · dsimp
      ring
  · exact (by fun_prop : Continuous (fun v : ℝ =>
      Real.exp (v / 2) * (A * v ^ 2 + B * v))).intervalIntegrable _ _

/-- The first logarithmic moment is nonzero even though the density integral
vanishes. Its negative coefficient is retained exactly. -/
theorem suzukiLocalSignedKernel_real_first_moment :
    (∫ v in (0 : ℝ)..3 * Real.log 2,
      Real.exp (v / 2) * suzukiLocalSignedKernel v * v) =
      -4 * Real.log 2 * Real.sqrt 2 * (Real.sqrt 2 - 1) ^ 2 := by
  let f : ℝ → ℝ := fun v => Real.exp (v / 2) * suzukiLocalSignedKernel v * v
  have hc : Continuous f := by
    dsimp [f, suzukiLocalSignedKernel, suzukiLocalTriangle]
    fun_prop
  have hh : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h1 : (∫ v in (0 : ℝ)..Real.log 2, f v) =
      ∫ v in (0 : ℝ)..Real.log 2,
        Real.exp (v / 2) * (Real.sqrt 2 * v ^ 2 + 0 * v) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hh] at hv
    dsimp [f]
    rw [suzukiLocalSignedKernel_eq_first hv.1 hv.2]
    ring
  have h2 : (∫ v in Real.log 2..2 * Real.log 2, f v) =
      ∫ v in Real.log 2..2 * Real.log 2,
        Real.exp (v / 2) * (-(Real.sqrt 2 + 1) * v ^ 2 +
          ((2 * Real.sqrt 2 + 1) * Real.log 2) * v) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le (by linarith : Real.log 2 ≤ 2 * Real.log 2)] at hv
    dsimp [f]
    rw [suzukiLocalSignedKernel_eq_middle hv.1 hv.2]
    ring
  have h3 : (∫ v in 2 * Real.log 2..3 * Real.log 2, f v) =
      ∫ v in 2 * Real.log 2..3 * Real.log 2,
        Real.exp (v / 2) * (1 * v ^ 2 + (-3 * Real.log 2) * v) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le (by linarith : 2 * Real.log 2 ≤ 3 * Real.log 2)] at hv
    dsimp [f]
    rw [suzukiLocalSignedKernel_eq_last hv.1 hv.2]
    ring
  have hsplit : (∫ v in (0 : ℝ)..3 * Real.log 2, f v) =
      (∫ v in (0 : ℝ)..Real.log 2, f v) +
        (∫ v in Real.log 2..2 * Real.log 2, f v) +
        (∫ v in 2 * Real.log 2..3 * Real.log 2, f v) := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals
        (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  change (∫ v in (0 : ℝ)..3 * Real.log 2, f v) = _
  rw [hsplit, h1, h2, h3, integral_quadratic_exp_half,
    integral_quadratic_exp_half, integral_quadratic_exp_half]
  have he1 : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
    rw [Real.exp_half, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have he2 : Real.exp (2 * Real.log 2 / 2) = (2 : ℝ) := by
    rw [show 2 * Real.log 2 / 2 = Real.log 2 by ring,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have he3 : Real.exp (3 * Real.log 2 / 2) = 2 * Real.sqrt 2 := by
    rw [show 3 * Real.log 2 / 2 = Real.log 2 + Real.log 2 / 2 by ring,
      Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2), he1]
  rw [he1, he2, he3]
  norm_num only [zero_div, Real.exp_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    mul_zero, add_zero, zero_add, one_mul]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith [congrArg (fun z : ℝ => z * Real.log 2) hs,
    congrArg (fun z : ℝ => z * (Real.log 2) ^ 2) hs]

/-- The first physical logarithmic density moment is independent of the
positive reference divisor because the zeroth density moment is zero. -/
theorem suzukiLocalPhysicalKernel_log_integral {X d : ℝ} (hX : 0 < X) (hd : 0 < d) :
    (∫ y in X..8 * X, suzukiLocalPhysicalKernel X y * Real.log (y / d)) =
      (-4 * Real.log 2 * Real.sqrt 2 * (Real.sqrt 2 - 1) ^ 2) * Real.sqrt X := by
  have hc : ContinuousOn (fun y => suzukiLocalPhysicalKernel X y * Real.log (y / d))
      ((fun v : ℝ => X * Real.exp v) '' uIcc 0 (3 * Real.log 2)) := by
    rintro y ⟨v, _, rfl⟩
    have hy : 0 < X * Real.exp v := by positivity
    exact ((continuousAt_suzukiLocalPhysicalKernel hX hy).mul
      ((Real.continuousAt_log (by positivity)).comp
        (continuousAt_id.div_const d))).continuousWithinAt
  have he := intervalIntegral.integral_comp_mul_deriv'
    (a := 0) (b := 3 * Real.log 2)
    (f := fun v : ℝ => X * Real.exp v) (f' := fun v => X * Real.exp v)
    (g := fun y => suzukiLocalPhysicalKernel X y * Real.log (y / d))
    (fun v _ => (Real.hasDerivAt_exp v).const_mul X) (by fun_prop) hc
  have hexp : Real.exp (3 * Real.log 2) = (8 : ℝ) := by
    rw [show 3 * Real.log 2 = Real.log 2 + Real.log 2 + Real.log 2 by ring]
    norm_num [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  simp only [Real.exp_zero, mul_one, hexp] at he
  rw [show X * 8 = 8 * X by ring] at he
  rw [← he]
  have heq : (fun v : ℝ =>
      (suzukiLocalPhysicalKernel X (X * Real.exp v) * Real.log (X * Real.exp v / d)) *
        (X * Real.exp v)) = fun v =>
      Real.sqrt X * ((Real.exp (v / 2) * suzukiLocalSignedKernel v) * Real.log (X / d) +
        Real.exp (v / 2) * suzukiLocalSignedKernel v * v) := by
    funext v
    have hl : Real.log (X * Real.exp v / d) = Real.log (X / d) + v := by
      rw [show X * Real.exp v / d = X / d * Real.exp v by ring,
        Real.log_mul (div_pos hX hd).ne' (Real.exp_ne_zero _), Real.log_exp]
    rw [hl, mul_right_comm, suzukiLocalPhysicalKernel_exp_jacobian hX]
    ring
  simp only [Function.comp_def]
  rw [heq, intervalIntegral.integral_const_mul]
  have hi : Continuous (fun v : ℝ => Real.exp (v / 2) * suzukiLocalSignedKernel v) := by
    unfold suzukiLocalSignedKernel suzukiLocalTriangle
    fun_prop
  have hi1 : IntervalIntegrable (fun v =>
      Real.exp (v / 2) * suzukiLocalSignedKernel v * Real.log (X / d))
      volume 0 (3 * Real.log 2) := (hi.mul continuous_const).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun v =>
      Real.exp (v / 2) * suzukiLocalSignedKernel v * v)
      volume 0 (3 * Real.log 2) := (hi.mul continuous_id).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_mul_const,
    suzukiLocalSignedKernel_real_density_integral, zero_mul, zero_add,
    suzukiLocalSignedKernel_real_first_moment]
  ring

/-- Scaling the physical first moment gives the exact continuous main term
for the logarithmically weighted integer lattice with positive divisor `d`. -/
theorem suzukiLocalPhysicalKernel_scaled_log_integral {X d : ℝ}
    (hX : 0 < X) (hd : 0 < d) :
    (∫ m in (X / d)..(8 * X / d),
      suzukiLocalPhysicalKernel X (d * m) * Real.log m) =
      ((-4 * Real.log 2 * Real.sqrt 2 * (Real.sqrt 2 - 1) ^ 2) * Real.sqrt X) / d := by
  have hab : X / d ≤ 8 * X / d := (div_le_div_iff_of_pos_right hd).mpr (by linarith)
  have hc : ContinuousOn (fun y => suzukiLocalPhysicalKernel X y * Real.log (y / d))
      ((fun m : ℝ => d * m) '' uIcc (X / d) (8 * X / d)) := by
    rintro y ⟨m, hm, rfl⟩
    rw [uIcc_of_le hab] at hm
    have hmpos : 0 < m := (div_pos hX hd).trans_le hm.1
    have hy : 0 < d * m := mul_pos hd hmpos
    exact ((continuousAt_suzukiLocalPhysicalKernel hX hy).mul
      ((Real.continuousAt_log (by positivity)).comp
        (continuousAt_id.div_const d))).continuousWithinAt
  have he := intervalIntegral.integral_comp_mul_deriv'
    (a := X / d) (b := 8 * X / d)
    (f := fun m : ℝ => d * m) (f' := fun _ => d)
    (g := fun y => suzukiLocalPhysicalKernel X y * Real.log (y / d))
    (fun m _ => by simpa using (hasDerivAt_id m).const_mul d) (by fun_prop) hc
  have hlo : d * (X / d) = X := by field_simp
  have hhi : d * (8 * X / d) = 8 * X := by field_simp
  rw [hlo, hhi, suzukiLocalPhysicalKernel_log_integral hX hd] at he
  simp only [Function.comp_def, mul_div_cancel_left₀ _ hd.ne'] at he
  rw [intervalIntegral.integral_mul_const] at he
  exact (eq_div_iff hd.ne').mpr he

end
end RiemannGaussian
