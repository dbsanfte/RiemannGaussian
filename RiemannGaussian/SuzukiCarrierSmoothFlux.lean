/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarrierSmooth

/-!
# Full signed area identities through all carrier poles

The actual smooth carrier satisfies Cauchy--Green on every rectangle,
including rectangles containing genuine denominator poles and common
xi zeros. Real-differentiable weights retain both source terms. The
existing Gaussian boundary heat is rotated into spectral coordinates
and instantiated with all its differentiability conditions discharged.
-/

open Complex Filter MeasureTheory Real Set Topology
open scoped ContDiff
namespace RiemannGaussian
noncomputable section

/-- The unweighted signed area identity crosses every genuine carrier
pole, since global smoothness has already been proved for the actual factors. -/
theorem suzukiXiSmoothCarrier_rectangularCauchyGreen {r : ℝ} (hr : 0 < r)
    (l v b u : ℝ) :
    rectangularBoundaryIntegral l v b u (suzukiXiSmoothCarrier r) =
      ∫ x : ℝ in l..v, ∫ y : ℝ in b..u,
        suzukiXiSmoothCarrierSource r ((x : ℂ) + (y : ℂ) * I) := by
  have hc : Continuous (complexCauchyGreenSource (suzukiXiSmoothCarrier r)) := by
    convert continuous_suzukiXiSmoothCarrierSource hr using 1
    funext z
    exact complexCauchyGreenSource_suzukiXiSmoothCarrier hr z
  simpa only [complexCauchyGreenSource_suzukiXiSmoothCarrier hr] using
    rectangularBoundaryIntegral_eq_cauchyGreenSource _
      ((contDiff_suzukiXiSmoothCarrier hr).differentiable (by simp)) hc l v b u

/-- Arbitrary real-differentiable weights retain their own source term
and the full carrier Wronskian in the same area integral. -/
theorem suzukiXiSmoothCarrier_weighted_rectangularCauchyGreen {r : ℝ} (hr : 0 < r)
    (B : ℂ → ℂ) (hB : Differentiable ℝ B) (hBc : Continuous (complexCauchyGreenSource B))
    (l v b u : ℝ) :
    rectangularBoundaryIntegral l v b u (fun z => B z * suzukiXiSmoothCarrier r z) =
      ∫ x : ℝ in l..v, ∫ y : ℝ in b..u,
        B ((x : ℂ) + (y : ℂ) * I) * suzukiXiSmoothCarrierSource r ((x : ℂ) + (y : ℂ) * I) +
          suzukiXiSmoothCarrier r ((x : ℂ) + (y : ℂ) * I) *
            complexCauchyGreenSource B ((x : ℂ) + (y : ℂ) * I) := by
  have hS := (contDiff_suzukiXiSmoothCarrier hr).differentiable (by simp)
  have he (z : ℂ) : complexCauchyGreenSource (fun w => B w * suzukiXiSmoothCarrier r w) z =
      B z * suzukiXiSmoothCarrierSource r z + suzukiXiSmoothCarrier r z * complexCauchyGreenSource B z := by
    rw [complexCauchyGreenSource_mul (hB z) (hS z), complexCauchyGreenSource_suzukiXiSmoothCarrier hr]
    ring
  have hc : Continuous (complexCauchyGreenSource (fun z => B z * suzukiXiSmoothCarrier r z)) := by
    have heq := funext he
    rw [heq]
    exact (hB.continuous.mul (continuous_suzukiXiSmoothCarrierSource hr)).add
      ((contDiff_suzukiXiSmoothCarrier hr).continuous.mul hBc)
  simpa only [he] using rectangularBoundaryIntegral_eq_cauchyGreenSource _ (hB.fun_mul hS) hc l v b u

/-- The existing arithmetic boundary heat, rotated to the actual
spectral coordinate so its zero boundary is `Im(z)=0`. -/
def suzukiSmoothSpectralBoundaryHeat (x tau : ℝ) (z : ℂ) : ℂ :=
  suzukiChebyshevLaplaceBoundaryHeatKernel x tau (I * z)

/-- Exact spectral Gaussian formula, retaining the signed vertical
coordinate rather than replacing it by an absolute value. -/
theorem suzukiSmoothSpectralBoundaryHeat_eq (x tau : ℝ) (z : ℂ) :
    suzukiSmoothSpectralBoundaryHeat x tau z =
      ((2 * z.im * Real.exp (-tau * ((x - z.re) ^ 2 + z.im ^ 2)) : ℝ) : ℂ) := by
  simp [suzukiSmoothSpectralBoundaryHeat]

/-- The actual rotated heat is real differentiable everywhere. -/
theorem differentiable_suzukiSmoothSpectralBoundaryHeat (x tau : ℝ) :
    Differentiable ℝ (suzukiSmoothSpectralBoundaryHeat x tau) := by
  intro z
  exact (differentiableAt_real_suzukiChebyshevLaplaceBoundaryHeatKernel x tau (I * z)).comp z
    (((hasDerivAt_id z).const_mul I).differentiableAt.restrictScalars ℝ)

/-- The full Gaussian source has the rotated antiholomorphic Jacobian. -/
theorem complexCauchyGreenSource_suzukiSmoothSpectralBoundaryHeat (x tau : ℝ) (z : ℂ) :
    complexCauchyGreenSource (suzukiSmoothSpectralBoundaryHeat x tau) z =
      -I * suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource x tau (I * z) := by
  change complexCauchyGreenSource (fun w => suzukiChebyshevLaplaceBoundaryHeatKernel x tau (I * w)) z = _
  rw [complexCauchyGreenSource_comp_I_mul
    (differentiableAt_real_suzukiChebyshevLaplaceBoundaryHeatKernel x tau (I * z))]
  congr 1
  exact cauchyGreenSource_suzukiChebyshevLaplaceBoundaryHeatKernel x tau (I * z)

/-- Continuity of the actual rotated source discharges the area
integrability premise on every compact rectangle. -/
theorem continuous_source_suzukiSmoothSpectralBoundaryHeat (x tau : ℝ) :
    Continuous (complexCauchyGreenSource (suzukiSmoothSpectralBoundaryHeat x tau)) := by
  have heq := funext (complexCauchyGreenSource_suzukiSmoothSpectralBoundaryHeat x tau)
  rw [heq]
  exact continuous_const.mul
    ((continuous_suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource x tau).comp (by fun_prop))

/-- The heat weight vanishes exactly on the original real boundary. -/
@[simp] theorem suzukiSmoothSpectralBoundaryHeat_ofReal (x tau t : ℝ) :
    suzukiSmoothSpectralBoundaryHeat x tau (t : ℂ) = 0 := by
  simp [suzukiSmoothSpectralBoundaryHeat_eq]

/-- Both signed area terms remain in one literal Gaussian-weighted
identity for the actual carrier. No pole order or internal zero is excluded. -/
theorem suzukiXiSmoothCarrier_boundaryHeat_rectangularCauchyGreen {r : ℝ} (hr : 0 < r)
    (x tau l v b u : ℝ) :
    rectangularBoundaryIntegral l v b u
      (fun z => suzukiSmoothSpectralBoundaryHeat x tau z * suzukiXiSmoothCarrier r z) =
      ∫ a : ℝ in l..v, ∫ y : ℝ in b..u,
        suzukiSmoothSpectralBoundaryHeat x tau ((a : ℂ) + (y : ℂ) * I) *
          suzukiXiSmoothCarrierSource r ((a : ℂ) + (y : ℂ) * I) -
        I * suzukiXiSmoothCarrier r ((a : ℂ) + (y : ℂ) * I) *
          suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource x tau (I * ((a : ℂ) + (y : ℂ) * I)) := by
  rw [suzukiXiSmoothCarrier_weighted_rectangularCauchyGreen hr _
    (differentiable_suzukiSmoothSpectralBoundaryHeat x tau)
    (continuous_source_suzukiSmoothSpectralBoundaryHeat x tau)]
  apply intervalIntegral.integral_congr
  intro a _ha
  apply intervalIntegral.integral_congr
  intro y _hy
  dsimp only
  rw [complexCauchyGreenSource_suzukiSmoothSpectralBoundaryHeat]
  ring

end
end RiemannGaussian
