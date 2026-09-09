/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplaceBoundaryHeat

/-!
# Exact algebra of the Cauchy--Green source

These rules retain the non-holomorphic contribution of a real-smooth
quotient. They allow a bounded regularization of a meromorphic carrier
to be used in the existing area--boundary framework without silently
treating that regularization as holomorphic.
-/

open Complex
namespace RiemannGaussian
noncomputable section

/-- A complex-differentiable function has zero Cauchy--Green source. -/
theorem complexCauchyGreenSource_eq_zero {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) : complexCauchyGreenSource f z = 0 := by
  have hcr := (differentiableAt_complex_iff_differentiableAt_real.mp hf).2
  simp only [complexCauchyGreenSource, hcr, smul_eq_mul, sub_self]

/-- The source is additive for real-differentiable functions. -/
theorem complexCauchyGreenSource_add {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    complexCauchyGreenSource (fun w => f w + g w) z =
      complexCauchyGreenSource f z + complexCauchyGreenSource g z := by
  change complexCauchyGreenSource (f + g) z = _
  unfold complexCauchyGreenSource
  rw [(hf.hasFDerivAt.add hg.hasFDerivAt).fderiv]
  simp only [add_apply, smul_eq_mul]
  ring

/-- The exact product rule keeps both non-holomorphic terms. -/
theorem complexCauchyGreenSource_mul {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    complexCauchyGreenSource (fun w => f w * g w) z =
      complexCauchyGreenSource f z * g z + f z * complexCauchyGreenSource g z := by
  change complexCauchyGreenSource (f * g) z = _
  unfold complexCauchyGreenSource
  rw [(hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- The real-differentiable quotient rule, with actual nonvanishing
of the denominator and its own source term retained. -/
theorem complexCauchyGreenSource_div {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (hgz : g z ≠ 0) :
    complexCauchyGreenSource (fun w => f w / g w) z =
      (complexCauchyGreenSource f z * g z - f z * complexCauchyGreenSource g z) / g z ^ 2 := by
  have hi := (hasFDerivAt_inv' (𝕜 := ℝ) hgz).comp z hg.hasFDerivAt
  have hp := hf.hasFDerivAt.mul hi
  change complexCauchyGreenSource (f * (Inv.inv ∘ g)) z = _
  unfold complexCauchyGreenSource
  rw [hp.fderiv]
  simp [ContinuousLinearMap.mulLeftRight_apply]
  field_simp
  ring

/-- Conjugating a holomorphic function supplies its full antiholomorphic
derivative rather than a zero source. -/
theorem complexCauchyGreenSource_conj {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) :
    complexCauchyGreenSource (fun w => starRingEnd ℂ (f w)) z =
      2 * I * starRingEnd ℂ (deriv f z) := by
  have hd := hf.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have hc := Complex.conjCLE.hasFDerivAt.comp z hd
  change complexCauchyGreenSource (Complex.conjCLE ∘ f) z = _
  unfold complexCauchyGreenSource
  rw [hc.fderiv]
  simp
  ring

/-- Rotating the input by `i` retains the exact opposite Jacobian in
the antiholomorphic source. -/
theorem complexCauchyGreenSource_comp_I_mul {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f (I * z)) :
    complexCauchyGreenSource (fun w => f (I * w)) z =
      -I * complexCauchyGreenSource f (I * z) := by
  have hd := ((hasDerivAt_id z).const_mul I).hasFDerivAt.restrictScalars ℝ
  have hc := hf.hasFDerivAt.comp z hd
  change complexCauchyGreenSource (f ∘ (fun w => I * w)) z = _
  unfold complexCauchyGreenSource
  rw [hc.fderiv]
  simp
  ring_nf
  simp [I_sq]

/-- Global real differentiability and a continuous explicit source
give Cauchy--Green on every closed rectangle, with actual area integrability. -/
theorem rectangularBoundaryIntegral_eq_cauchyGreenSource
    (f : ℂ → ℂ) (hf : Differentiable ℝ f) (hc : Continuous (complexCauchyGreenSource f))
    (l v b u : ℝ) :
    rectangularBoundaryIntegral l v b u f =
      ∫ x : ℝ in l..v, ∫ y : ℝ in b..u, complexCauchyGreenSource f ((x : ℂ) + (y : ℂ) * I) := by
  have hgreen := Complex.integral_boundary_rect_of_differentiableOn_real f
    ((l : ℂ) + (b : ℂ) * I) ((v : ℂ) + (u : ℂ) * I) hf.differentiableOn
    (hc.continuousOn.integrableOn_compact (isCompact_uIcc.reProdIm isCompact_uIcc))
  simpa [rectangularBoundaryIntegral, complexCauchyGreenSource, smul_eq_mul] using hgreen

end
end RiemannGaussian
