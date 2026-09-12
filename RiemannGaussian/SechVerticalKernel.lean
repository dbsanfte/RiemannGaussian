/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Complete exponential domination of the vertical detector kernel

The original hyperbolic-secant density remains explicit. A downstream
Laplace envelope pays for its whole real domain. Exact zeroth and first
moments of that envelope control all affine logarithmic allowances.
-/

namespace RiemannGaussian.SechVerticalKernel
noncomputable section
open MeasureTheory Set Real

/-- The hyperbolic-secant density with the detector's factor one half. -/
def density (u : ℝ) : ℝ := 1 / (2 * Real.cosh u ^ 2)

/-- The actual detector density is nonnegative at every real point. -/
theorem density_nonneg (u : ℝ) : 0 ≤ density u := by unfold density; positivity

/-- The actual detector density is continuous on the whole real line. -/
theorem continuous_density : Continuous density := by
  unfold density
  exact continuous_const.div₀ (continuous_const.mul (Real.continuous_cosh.pow 2))
    (fun u => by positivity)

/-- The complete detector density is bounded by an elementary Laplace
envelope, with no cutoff or discarded tail. -/
theorem density_le_exp (u : ℝ) : density u ≤ Real.exp (-|u|) := by
  have hc := Real.one_le_cosh u
  have habs : Real.cosh |u| = Real.cosh u := by
    by_cases h : 0 ≤ u
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h), Real.cosh_neg]
  have he : Real.exp |u| ≤ 2 * Real.cosh u := by
    rw [← habs, Real.cosh_eq]
    linarith [Real.exp_pos (-|u|)]
  have hd : Real.exp |u| ≤ 2 * Real.cosh u ^ 2 := by nlinarith
  have h := one_div_le_one_div_of_le (Real.exp_pos |u|) hd
  simpa only [density, one_div, Real.exp_neg] using h

/-- Absolute-value reflection turns any integrable positive-half-line
function into a genuinely integrable function on the whole real line. -/
theorem integrable_abs_extension {f : ℝ → ℝ} (h : IntegrableOn f (Ioi 0)) :
    Integrable (fun u : ℝ => f |u|) := by
  have hi : IntegrableOn (fun u : ℝ => f |u|) (Ioi 0) := by
    apply h.congr_fun _ measurableSet_Ioi
    intro u hu
    simp only [mem_Ioi] at hu
    simp only [abs_of_pos hu]
  have hl : IntegrableOn (fun u : ℝ => f |u|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding (fun x : ℝ => -x) := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hi
  have hu := hl.union hi
  simpa only [Iic_union_Ioi, integrableOn_univ] using hu

/-- The full Laplace envelope is integrable. -/
theorem integrable_exp_abs : Integrable (fun u : ℝ => Real.exp (-|u|)) :=
  integrable_abs_extension (integrableOn_exp_neg_Ioi 0)

/-- The absolute first moment of the full Laplace envelope is integrable. -/
theorem integrable_abs_mul_exp : Integrable (fun u : ℝ => |u| * Real.exp (-|u|)) := by
  apply integrable_abs_extension (f := fun u : ℝ => u * Real.exp (-u))
  have h := Real.GammaIntegral_convergent (s := 2) (by norm_num)
  simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, mul_comm]
    using h

/-- The full Laplace envelope has exact mass two. -/
theorem integral_exp_abs : (∫ u : ℝ, Real.exp (-|u|)) = 2 := by
  rw [integral_comp_abs (f := fun u : ℝ => Real.exp (-u)), integral_exp_neg_Ioi_zero, mul_one]

/-- The absolute first moment of the full Laplace envelope is exactly two. -/
theorem integral_abs_mul_exp : (∫ u : ℝ, |u| * Real.exp (-|u|)) = 2 := by
  rw [integral_comp_abs (f := fun u : ℝ => u * Real.exp (-u))]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := 2) (r := 1) (by norm_num) (by norm_num)
  norm_num [Real.Gamma_nat_eq_factorial] at h
  rw [h]
  norm_num

/-- Any affine absolute-value allowance times the Laplace envelope
is integrable over the entire real line. -/
theorem integrable_affine (A B : ℝ) :
    Integrable (fun u : ℝ => (A + B * |u|) * Real.exp (-|u|)) := by
  have h := (integrable_exp_abs.const_mul A).add (integrable_abs_mul_exp.const_mul B)
  convert! h using 1
  ext u
  simp only [Pi.add_apply]
  ring

/-- The exact integral of the complete affine envelope has no hidden
tail allowance or unspecified integration constant. -/
theorem integral_affine (A B : ℝ) :
    (∫ u : ℝ, (A + B * |u|) * Real.exp (-|u|)) = 2 * A + 2 * B := by
  rw [show (fun u : ℝ => (A + B * |u|) * Real.exp (-|u|)) =
      (fun u => A * Real.exp (-|u|) + B * (|u| * Real.exp (-|u|))) by funext u; ring,
    integral_add (integrable_exp_abs.const_mul A) (integrable_abs_mul_exp.const_mul B),
    integral_const_mul, integral_const_mul, integral_exp_abs, integral_abs_mul_exp]
  ring

end
end RiemannGaussian.SechVerticalKernel
