/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarrierMassVariation

/-!
# The actual reflection current and its explicit remainder

The full source separates into a total horizontal derivative, signed
mass variation and an explicitly bounded remainder. This retains the
companion heat term and is valid through the complete carrier divisor.
Only the two reflection nodes are excluded from derivative identities.
-/

open Complex Filter MeasureTheory Set Topology
open scoped ContDiff
namespace RiemannGaussian
noncomputable section

/-- The literal complex reflection weight times the Gaussian on one horizontal line. -/
def suzukiXiHorizontalReflectionHeat (rho : NontrivialZetaZero) (c tau y x : ℝ) : ℂ :=
  suzukiXiReflectionWeight rho ((x : ℂ) + (y : ℂ) * I) *
    suzukiSmoothSpectralBoundaryHeat c tau ((x : ℂ) + (y : ℂ) * I)

/-- The full bounded-field current before taking a horizontal derivative. -/
def suzukiXiReflectionMassCurrent (rho : NontrivialZetaZero) (r c tau y x : ℝ) : ℂ :=
  suzukiXiHorizontalReflectionHeat rho c tau y x *
    (suzukiXiHorizontalMass r y x : ℂ) * suzukiXiHorizontalCarrier r y x

/-- The signed variation retained after integration by parts. -/
def suzukiXiReflectionMassVariation (rho : NontrivialZetaZero) (r c tau y x : ℝ) : ℂ :=
  suzukiXiHorizontalReflectionHeat rho c tau y x * suzukiXiHorizontalCarrier r y x *
    ((deriv (suzukiXiHorizontalMass r y) x : ℝ) : ℂ)

/-- The exact weight-derivative and companion-heat remainder, with complex signs intact. -/
def suzukiXiReflectionMassRemainder (rho : NontrivialZetaZero) (r c tau y x : ℝ) : ℂ :=
  2 * I * (r : ℂ) ^ 2 * deriv (suzukiXiHorizontalReflectionHeat rho c tau y) x *
      (suzukiXiHorizontalMass r y x : ℂ) * suzukiXiHorizontalCarrier r y x +
    I * suzukiXiReflectionWeight rho ((x : ℂ) + (y : ℂ) * I) *
      suzukiXiHorizontalCarrier r y x *
        suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource c tau (I * ((x : ℂ) + (y : ℂ) * I))

/-- The actual spectral Gaussian is globally real smooth. -/
theorem contDiff_suzukiSmoothSpectralBoundaryHeat (c tau : ℝ) :
    ContDiff ℝ ∞ (suzukiSmoothSpectralBoundaryHeat c tau) := by
  have he : suzukiSmoothSpectralBoundaryHeat c tau = fun z : ℂ =>
      ((2 * z.im * Real.exp (-tau * ((c - z.re) ^ 2 + z.im ^ 2)) : ℝ) : ℂ) := by
    funext z
    exact suzukiSmoothSpectralBoundaryHeat_eq c tau z
  rw [he]
  have hi : ContDiff ℝ ∞ (fun z : ℂ => z.im) := Complex.imCLM.contDiff
  have hre : ContDiff ℝ ∞ (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  exact Complex.ofRealCLM.contDiff.comp
    ((contDiff_const.mul hi).mul
      ((contDiff_const.mul (((contDiff_const.sub hre).pow 2).add (hi.pow 2))).exp))

/-- The actual horizontal weight is smooth away from its two reflection nodes. -/
theorem contDiffAt_suzukiXiHorizontalReflectionHeat (rho : NontrivialZetaZero)
    (c tau y x : ℝ)
    (ha : (x : ℂ) + (y : ℂ) * I ≠ zetaSpectralCoordinate rho.1)
    (hb : (x : ℂ) + (y : ℂ) * I ≠ starRingEnd ℂ (zetaSpectralCoordinate rho.1)) :
    ContDiffAt ℝ ∞ (suzukiXiHorizontalReflectionHeat rho c tau y) x := by
  have hl : ContDiff ℝ ∞ (fun u : ℝ => (u : ℂ) + (y : ℂ) * I) :=
    Complex.ofRealCLM.contDiff.add contDiff_const
  exact (((analyticAt_suzukiXiReflectionWeight rho ha hb).contDiffAt.restrict_scalars ℝ).comp x hl.contDiffAt).mul
    ((contDiff_suzukiSmoothSpectralBoundaryHeat c tau).contDiffAt.comp x hl.contDiffAt)

/-- The actual current is smooth through all carrier poles and common zeros. -/
theorem contDiffAt_suzukiXiReflectionMassCurrent (rho : NontrivialZetaZero)
    {r : ℝ} (hr : 0 < r) (c tau y x : ℝ)
    (ha : (x : ℂ) + (y : ℂ) * I ≠ zetaSpectralCoordinate rho.1)
    (hb : (x : ℂ) + (y : ℂ) * I ≠ starRingEnd ℂ (zetaSpectralCoordinate rho.1)) :
    ContDiffAt ℝ ∞ (suzukiXiReflectionMassCurrent rho r c tau y) x := by
  exact ((contDiffAt_suzukiXiHorizontalReflectionHeat rho c tau y x ha hb).mul
    (Complex.ofRealCLM.contDiff.comp (contDiff_suzukiXiHorizontalMass hr y)).contDiffAt).mul
      (contDiff_suzukiXiHorizontalCarrier hr y).contDiffAt

/-- The full reflection density keeps a total derivative, the complete
signed mass variation and both explicit remainder terms. -/
theorem suzukiXiSmoothReflectionSource_eq_mass_current_deriv
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) (c tau y x : ℝ)
    (ha : (x : ℂ) + (y : ℂ) * I ≠ zetaSpectralCoordinate rho.1)
    (hb : (x : ℂ) + (y : ℂ) * I ≠ starRingEnd ℂ (zetaSpectralCoordinate rho.1)) :
    suzukiXiSmoothReflectionSource rho r c tau ((x : ℂ) + (y : ℂ) * I) =
      2 * I * (r : ℂ) ^ 2 * deriv (suzukiXiReflectionMassCurrent rho r c tau y) x -
        4 * I * (r : ℂ) ^ 2 * suzukiXiReflectionMassVariation rho r c tau y x -
          suzukiXiReflectionMassRemainder rho r c tau y x := by
  have hp := ((contDiffAt_suzukiXiHorizontalReflectionHeat rho c tau y x ha hb).differentiableAt (by simp)).hasDerivAt
  have hm := ((contDiff_suzukiXiHorizontalMass hr y).differentiable (by simp) x).hasDerivAt.ofReal_comp
  have hS := ((contDiff_suzukiXiHorizontalCarrier hr y).differentiable (by simp) x).hasDerivAt
  have hd := ((hp.fun_mul hm).fun_mul hS).deriv
  change deriv (suzukiXiReflectionMassCurrent rho r c tau y) x = _ at hd
  rw [hd]
  unfold suzukiXiSmoothReflectionSource suzukiXiSmoothBoundaryHeatBulk
  rw [suzukiXiSmoothCarrierSource_eq_horizontal_mass_variation hr]
  unfold suzukiXiReflectionMassVariation suzukiXiReflectionMassRemainder suzukiXiHorizontalReflectionHeat
  change _ = _
  dsimp only [suzukiXiHorizontalCarrier]
  ring

/-- The derivative-free current has a uniform bound with all arithmetic
normalization factors included. -/
theorem norm_suzukiXiReflectionMassCurrent_le (rho : NontrivialZetaZero)
    {r : ℝ} (hr : 0 < r) (c tau y x : ℝ) :
    ‖suzukiXiReflectionMassCurrent rho r c tau y x‖ ≤
      ‖suzukiXiHorizontalReflectionHeat rho c tau y x‖ / (2*r^3) := by
  unfold suzukiXiReflectionMassCurrent
  rw [mul_assoc, norm_mul]
  calc
    _ ≤ ‖suzukiXiHorizontalReflectionHeat rho c tau y x‖ * (1/(2*r^3)) :=
      mul_le_mul_of_nonneg_left (norm_suzukiXiNormalizedMass_mul_carrier_le hr _) (norm_nonneg _)
    _ = _ := by ring

/-- An independent pointwise envelope for the complete explicit
remainder. The signed mass variation is retained outside this estimate. -/
theorem norm_suzukiXiReflectionMassRemainder_le (rho : NontrivialZetaZero)
    {r : ℝ} (hr : 0 < r) (c tau y x : ℝ) :
    ‖suzukiXiReflectionMassRemainder rho r c tau y x‖ ≤
      ‖deriv (suzukiXiHorizontalReflectionHeat rho c tau y) x‖ / r +
        ‖suzukiXiReflectionWeight rho ((x : ℂ) + (y : ℂ) * I) *
          suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource c tau (I * ((x : ℂ) + (y : ℂ) * I))‖ / (2*r) := by
  let P := suzukiXiHorizontalReflectionHeat rho c tau y
  let U := suzukiXiHorizontalMass r y
  let S := suzukiXiHorizontalCarrier r y
  let H := suzukiXiReflectionWeight rho ((x : ℂ) + (y : ℂ) * I) *
    suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource c tau (I * ((x : ℂ) + (y : ℂ) * I))
  have he : suzukiXiReflectionMassRemainder rho r c tau y x =
      (2 * I * (r : ℂ)^2 * deriv P x) * ((U x : ℂ) * S x) + I * H * S x := by
    dsimp [suzukiXiReflectionMassRemainder, P, U, S, H]
    ring
  rw [he]
  have hUS := norm_suzukiXiNormalizedMass_mul_carrier_le hr ((x : ℂ) + (y : ℂ) * I)
  have hS := norm_suzukiXiSmoothCarrier_le hr ((x : ℂ) + (y : ℂ) * I)
  change ‖(U x : ℂ) * S x‖ ≤ _ at hUS
  change ‖S x‖ ≤ _ at hS
  calc
    _ ≤ ‖(2 * I * (r : ℂ)^2 * deriv P x) * ((U x : ℂ) * S x)‖ + ‖I * H * S x‖ := norm_add_le _ _
    _ = 2 * r^2 * ‖deriv P x‖ * ‖(U x : ℂ) * S x‖ + ‖H‖ * ‖S x‖ := by
      simp only [norm_mul, norm_pow, norm_I, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr, norm_ofNat, mul_one, one_mul]
    _ ≤ 2 * r^2 * ‖deriv P x‖ * (1/(2*r^3)) + ‖H‖ * (1/(2*r)) := by
      gcongr
    _ = _ := by dsimp [P, H]; field_simp

end
end RiemannGaussian
