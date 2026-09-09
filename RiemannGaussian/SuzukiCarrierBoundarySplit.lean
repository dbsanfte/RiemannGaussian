/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarrierPrincipalValue

/-!
# An unconditional separated integral for every Suzuki Gram entry

The common counterterm is supported on precisely the repeated real-node
entries. Subtract it from each channel before integration. Both resulting
mixed kernels are absolutely integrable, and their signed difference gives
the original Gram, with all pairs and all analytic multiplicities retained.

The principal-value theorem identifies the subtraction on the exceptional
entries with the actual symmetric cutoff limit. Off-axis denominator poles
and the global contour comparison remain explicit future obligations.
-/

open Complex MeasureTheory
open scoped Classical

namespace RiemannGaussian
noncomputable section

/-- The common counterterm matrix: a real-node pole occurs exactly when
both mixed denominator nodes coincide on the real axis. -/
def suzukiXiGramRealCounterterm (rho sigma : NontrivialZetaZero) (x : ℝ) : ℂ :=
  if starRingEnd ℂ (zetaSpectralCoordinate rho.1) = zetaSpectralCoordinate sigma.1 ∧
      (zetaSpectralCoordinate sigma.1).im = 0 then
    suzukiXiRealNodeCounterterm sigma x else 0

/-- The first carrier channel with its exact real pole subtracted. -/
def suzukiXiRegularizedGramChannel (rho sigma : NontrivialZetaZero) (x : ℝ) : ℂ :=
  suzukiRealAxisXiZeroCarrier x /
      (((x : ℂ) - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
        ((x : ℂ) - zetaSpectralCoordinate sigma.1)) -
    suzukiXiGramRealCounterterm rho sigma x

/-- The reflected channel with the very same counterterm subtracted. -/
def suzukiXiRegularizedGramSharpChannel (rho sigma : NontrivialZetaZero) (x : ℝ) : ℂ :=
  suzukiXiSharpCarrier (x : ℂ) /
      (((x : ℂ) - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
        ((x : ℂ) - zetaSpectralCoordinate sigma.1)) -
    suzukiXiGramRealCounterterm rho sigma x

/-- Every first-channel mixed entry is absolutely integrable after the
canonical subtraction, unconditionally on the full genuine xi divisor. -/
theorem integrable_suzukiXiRegularizedGramChannel (rho sigma : NontrivialZetaZero) :
    Integrable (suzukiXiRegularizedGramChannel rho sigma) := by
  by_cases h : starRingEnd ℂ (zetaSpectralCoordinate rho.1) = zetaSpectralCoordinate sigma.1 ∧
      (zetaSpectralCoordinate sigma.1).im = 0
  · have heq : suzukiXiRegularizedGramChannel rho sigma =
        suzukiXiRealNodeRegularizedChannel sigma := by
      funext x
      unfold suzukiXiRegularizedGramChannel suzukiXiGramRealCounterterm
      rw [if_pos h, h.1, ← pow_two]
      rfl
    rw [heq]
    exact integrable_suzukiXiRealNodeRegularizedChannel sigma h.2
  · have hp : zetaSpectralCoordinate (NontrivialZetaZero.conjugatePartner rho).1 ≠
        zetaSpectralCoordinate sigma.1 ∨ (zetaSpectralCoordinate sigma.1).im ≠ 0 := by
      rw [NontrivialZetaZero.spectralCoordinate_conjugatePartner]
      tauto
    unfold suzukiXiRegularizedGramChannel suzukiXiGramRealCounterterm
    simp only [if_neg h, sub_zero]
    simpa only [NontrivialZetaZero.spectralCoordinate_conjugatePartner] using
      integrable_suzukiXiCarrier_two_resolvents_of_no_real_collision
        (NontrivialZetaZero.conjugatePartner rho) sigma hp

/-- Every reflected mixed entry is also absolutely integrable after that
same subtraction, with no orthogonality or zero-location premise. -/
theorem integrable_suzukiXiRegularizedGramSharpChannel (rho sigma : NontrivialZetaZero) :
    Integrable (suzukiXiRegularizedGramSharpChannel rho sigma) := by
  by_cases h : starRingEnd ℂ (zetaSpectralCoordinate rho.1) = zetaSpectralCoordinate sigma.1 ∧
      (zetaSpectralCoordinate sigma.1).im = 0
  · have heq : suzukiXiRegularizedGramSharpChannel rho sigma =
        fun x : ℝ ↦ suzukiXiSharpCarrier (x : ℂ) /
          ((x : ℂ) - zetaSpectralCoordinate sigma.1) ^ 2 - suzukiXiRealNodeCounterterm sigma x := by
      funext x
      unfold suzukiXiRegularizedGramSharpChannel suzukiXiGramRealCounterterm
      rw [if_pos h, h.1, ← pow_two]
    rw [heq]
    exact integrable_suzukiXiRealNodeRegularizedSharpChannel sigma h.2
  · have hp : zetaSpectralCoordinate (NontrivialZetaZero.conjugatePartner rho).1 ≠
        zetaSpectralCoordinate sigma.1 ∨ (zetaSpectralCoordinate sigma.1).im ≠ 0 := by
      rw [NontrivialZetaZero.spectralCoordinate_conjugatePartner]
      tauto
    unfold suzukiXiRegularizedGramSharpChannel suzukiXiGramRealCounterterm
    simp only [if_neg h, sub_zero]
    simpa only [NontrivialZetaZero.spectralCoordinate_conjugatePartner] using
      integrable_suzukiXiSharpCarrier_two_resolvents_of_no_real_collision
        (NontrivialZetaZero.conjugatePartner rho) sigma hp

/-- Before any integration, the common matrix subtraction cancels exactly
and restores the original complex continuation of the signed Gram. -/
theorem suzukiXiRegularizedGramChannel_sub_sharp (rho sigma : NontrivialZetaZero) (x : ℝ) :
    (suzukiXiRegularizedGramChannel rho sigma x -
      suzukiXiRegularizedGramSharpChannel rho sigma x) / (2 * I) =
        suzukiXiCarrierGramContinuation rho sigma (x : ℂ) := by
  unfold suzukiXiRegularizedGramChannel suzukiXiRegularizedGramSharpChannel
    suzukiXiCarrierGramContinuation suzukiRealAxisXiZeroCarrier
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- Every genuine mixed Gram entry is the signed difference of two
absolutely integrable channels. The formula covers real and multiple nodes
as well as all nonreal reflected pairs. -/
theorem suzukiXiBoundaryCarrierGramKernel_eq_regularized_split
    (rho sigma : NontrivialZetaZero) :
    suzukiXiBoundaryCarrierGramKernel rho sigma =
      ((∫ x : ℝ, suzukiXiRegularizedGramChannel rho sigma x) -
        (∫ x : ℝ, suzukiXiRegularizedGramSharpChannel rho sigma x)) / (2 * I) := by
  rw [suzukiXiBoundaryCarrierGramKernel_eq_continuation_integral]
  calc
    _ = ∫ x : ℝ, (suzukiXiRegularizedGramChannel rho sigma x -
        suzukiXiRegularizedGramSharpChannel rho sigma x) / (2 * I) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦
        (suzukiXiRegularizedGramChannel_sub_sharp rho sigma x).symm
    _ = _ := by
      rw [integral_div, integral_sub (integrable_suzukiXiRegularizedGramChannel rho sigma)
        (integrable_suzukiXiRegularizedGramSharpChannel rho sigma)]

end
end RiemannGaussian
