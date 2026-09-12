/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SechVerticalKernel

/-!
# Exact moments of the vertical detector

The original hyperbolic-secant density has mass one and absolute first
moment `log 2`. Its logistic survival function retains every finite tail.
The Laplace envelope is used only to establish integrability; integration
uses the actual density, removing the earlier factor-two allowance.
-/

namespace RiemannGaussian.SechVerticalMoments
noncomputable section
open MeasureTheory Set Filter Real SechVerticalKernel
open scoped Topology

/-- The exact positive-tail survival function of the detector density. -/
def survival (u : ℝ) : ℝ := Real.exp (-2 * u) / (1 + Real.exp (-2 * u))

/-- The hyperbolic density is exactly the derivative of a logistic profile. -/
theorem density_eq_logistic (u : ℝ) :
    density u = 2 * Real.exp (-2 * u) / (1 + Real.exp (-2 * u)) ^ 2 := by
  have he : Real.exp (-2 * u) = (Real.exp u)⁻¹ ^ 2 := by
    rw [show -2 * u = -(u + u) by ring, Real.exp_neg, Real.exp_add]
    simp only [mul_inv_rev, pow_two]
  rw [density, Real.cosh_eq, Real.exp_neg, he]
  field_simp

/-- The survival derivative is the negative of the original density. -/
theorem hasDerivAt_survival (u : ℝ) : HasDerivAt survival (-density u) u := by
  have he : HasDerivAt (fun v : ℝ => Real.exp (-2 * v))
      (-2 * Real.exp (-2 * u)) u := by
    simpa only [id_eq, mul_one, one_mul, mul_comm] using ((hasDerivAt_id u).const_mul (-2)).exp
  have h := he.div (he.const_add 1) (by positivity : 1 + Real.exp (-2 * u) ≠ 0)
  convert! h using 1
  · rw [density_eq_logistic]
    ring

/-- The exact survival function vanishes at positive infinity. -/
theorem survival_tendsto : Tendsto survival atTop (𝓝 0) := by
  have he : Tendsto (fun u : ℝ => Real.exp (-2 * u)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num))
  convert! he.div (he.const_add 1) (by norm_num : (1 : ℝ) + 0 ≠ 0) using 1
  norm_num

/-- The actual density is integrable on the complete real line. -/
theorem integrable_density : Integrable density := by
  apply integrable_exp_abs.mono' continuous_density.aestronglyMeasurable
  filter_upwards [] with u
  rw [Real.norm_eq_abs, abs_of_nonneg (density_nonneg u)]
  exact density_le_exp u

/-- Every half-line tail has an exact finite value, with no omitted endpoint. -/
theorem integral_density_Ioi (R : ℝ) : (∫ u in Ioi R, density u) = survival R := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := fun u : ℝ => -survival u) (f' := density)
    (fun u (_ : u ∈ Ici R) => by simpa only [neg_neg, Pi.neg_def] using (hasDerivAt_survival u).neg)
    integrable_density.integrableOn survival_tendsto.neg
  simpa only [neg_neg, neg_zero, zero_sub] using h

/-- Reflection preserves the original detector density exactly. -/
theorem density_abs (u : ℝ) : density |u| = density u := by
  unfold density
  by_cases hu : 0 ≤ u
  · rw [abs_of_nonneg hu]
  · rw [abs_of_neg (lt_of_not_ge hu), Real.cosh_neg]

/-- The actual complete detector has mass one, rather than the mass two
of the auxiliary Laplace envelope. -/
theorem integral_density : (∫ u : ℝ, density u) = 1 := by
  have h := integral_comp_abs (f := density)
  simp_rw [density_abs] at h
  rw [h, integral_density_Ioi]
  norm_num [survival]

/-- The two exterior tails retain an exact value at every nonnegative
cutoff. -/
theorem integral_tail {R : ℝ} (hR : 0 ≤ R) :
    (∫ u : ℝ, if R < |u| then density u else 0) = 2 * survival R := by
  have h := integral_comp_abs (f := fun u : ℝ => if R < u then density u else 0)
  simp_rw [density_abs] at h
  rw [h]
  congr 1
  change (∫ u in Ioi (0 : ℝ), (Ioi R).indicator density u) = survival R
  rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right hR,
    integral_density_Ioi]

/-- The exact two-sided tail has exponential decay at the original
kernel's rate, without extending a weaker Laplace envelope. -/
theorem integral_tail_le {R : ℝ} (hR : 0 ≤ R) :
    (∫ u : ℝ, if R < |u| then density u else 0) ≤ 2 * Real.exp (-2 * R) := by
  rw [integral_tail hR]
  exact mul_le_mul_of_nonneg_left
    (div_le_self (Real.exp_pos _).le (by linarith [Real.exp_pos (-2 * R)]))
    (by norm_num)

/-- The actual absolute first moment is genuinely integrable. -/
theorem integrable_abs_mul_density : Integrable (fun u : ℝ => |u| * density u) := by
  apply integrable_abs_mul_exp.mono'
    (continuous_abs.mul continuous_density).aestronglyMeasurable
  filter_upwards [] with u
  change ‖|u| * density u‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (density_nonneg _))]
  exact mul_le_mul_of_nonneg_left (density_le_exp u) (abs_nonneg u)

private def firstPrimitive (u : ℝ) : ℝ :=
  -u * survival u - Real.log (1 + Real.exp (-2 * u)) / 2

private theorem hasDerivAt_firstPrimitive (u : ℝ) :
    HasDerivAt firstPrimitive (u * density u) u := by
  have he : HasDerivAt (fun v : ℝ => Real.exp (-2 * v))
      (-2 * Real.exp (-2 * u)) u := by
    simpa only [id_eq, mul_one, one_mul, mul_comm] using ((hasDerivAt_id u).const_mul (-2)).exp
  have hl := ((he.const_add 1).log (by positivity : 1 + Real.exp (-2 * u) ≠ 0)).div_const 2
  have h := ((hasDerivAt_id u).neg.mul (hasDerivAt_survival u)).sub hl
  convert! h using 1
  · simp only [survival, Pi.neg_apply, id_eq]
    ring

private theorem firstPrimitive_tendsto : Tendsto firstPrimitive atTop (𝓝 0) := by
  have he : Tendsto (fun u : ℝ => Real.exp (-2 * u)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num))
  have hmul : Tendsto (fun u : ℝ => u * Real.exp (-2 * u)) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    convert! h.div_const 2 using 1
    · ext u
      simp only [Function.comp_apply, pow_one, id_eq, neg_mul]
      ring
    · norm_num
  have hs := hmul.div (he.const_add 1) (by norm_num : (1 : ℝ) + 0 ≠ 0)
  have hl := ((he.const_add 1).log (by norm_num : (1 : ℝ) + 0 ≠ 0)).div_const 2
  convert! hs.neg.sub hl using 1
  · ext u
    simp only [firstPrimitive, survival, Pi.div_apply]
    ring
  · norm_num

/-- The exact first absolute moment is `log 2`; no coefficient search or
numerical integration enters its proof. -/
theorem integral_abs_mul_density : (∫ u : ℝ, |u| * density u) = Real.log 2 := by
  have hi : IntegrableOn (fun u : ℝ => u * density u) (Ioi 0) := by
    apply integrable_abs_mul_density.integrableOn.congr_fun _ measurableSet_Ioi
    intro u hu
    simp [abs_of_pos (show 0 < u from hu)]
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun u (_ : u ∈ Ici (0 : ℝ)) => hasDerivAt_firstPrimitive u) hi firstPrimitive_tendsto
  norm_num [firstPrimitive, survival] at h
  have he := integral_comp_abs (f := fun u : ℝ => u * density u)
  simp_rw [density_abs] at he
  rw [he, h]
  ring

/-- Every affine absolute-value allowance is integrable against the
actual density. -/
theorem integrable_affine_density (A B : ℝ) :
    Integrable (fun u : ℝ => density u * (A + B * |u|)) := by
  have h := (integrable_density.const_mul A).add (integrable_abs_mul_density.const_mul B)
  convert! h using 1
  ext u
  simp only [Pi.add_apply]
  ring

/-- Exact integration of an affine allowance preserves the true mass
and first moment, replacing `2*A+2*B` by `A+log(2)*B`. -/
theorem integral_affine_density (A B : ℝ) :
    (∫ u : ℝ, density u * (A + B * |u|)) = A + Real.log 2 * B := by
  rw [show (fun u : ℝ => density u * (A + B * |u|)) =
      (fun u => A * density u + B * (|u| * density u)) by funext u; ring,
    integral_add (integrable_density.const_mul A) (integrable_abs_mul_density.const_mul B),
    integral_const_mul, integral_const_mul, integral_density, integral_abs_mul_density]
  ring

end
end RiemannGaussian.SechVerticalMoments
