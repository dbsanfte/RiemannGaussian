/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarrierFiniteContour
import RiemannGaussian.SuzukiCarrierSafeContour

/-!
# The finite signed mixed contour comparison

Separate the bottom from the other three sides of the actual first
carrier rectangle, then couple it with its conjugate-transposed entry.
The exact result is the reflected xi source plus the full Hermitian
carrier-pole correction. This keeps both mixed indices and every complex
pole coefficient before any norm or limit is taken.

The displaced bottom expression is not identified with the real-axis
Gram here. That boundary limit, and control of the remaining sides and
complete pole correction, remain explicit obligations.
-/

open Complex MeasureTheory
namespace RiemannGaussian
noncomputable section

/-- The actual left-to-right bottom-side integral, retaining both mixed
nodes and the independent horizontal and vertical cutoffs. -/
def suzukiXiMixedCarrierBottomIntegral (rho sigma : NontrivialZetaZero) (l r b : ℝ) : ℂ :=
  ∫ x : ℝ in l..r, suzukiXiMixedCarrierChannel rho sigma ((x : ℂ) + (b : ℂ) * I)

/-- The other three sides with their exact counterclockwise orientation:
the top is subtracted, the right is upward and the left downward. -/
def suzukiXiMixedCarrierOtherSides (rho sigma : NontrivialZetaZero) (l r b u : ℝ) : ℂ :=
  -(∫ x : ℝ in l..r, suzukiXiMixedCarrierChannel rho sigma ((x : ℂ) + (u : ℂ) * I)) +
    I * (∫ y : ℝ in b..u, suzukiXiMixedCarrierChannel rho sigma ((r : ℂ) + (y : ℂ) * I)) -
    I * (∫ y : ℝ in b..u, suzukiXiMixedCarrierChannel rho sigma ((l : ℂ) + (y : ℂ) * I))

/-- The actual bottom and three remaining sides reconstruct the original
rectangular contour exactly, before any estimate. -/
theorem suzukiXiMixedCarrierBottom_add_otherSides (rho sigma : NontrivialZetaZero)
    (l r b u : ℝ) :
    suzukiXiMixedCarrierBottomIntegral rho sigma l r b +
      suzukiXiMixedCarrierOtherSides rho sigma l r b u =
        rectangularBoundaryIntegral l r b u (suzukiXiMixedCarrierChannel rho sigma) := by
  unfold suzukiXiMixedCarrierBottomIntegral suzukiXiMixedCarrierOtherSides rectangularBoundaryIntegral
  ring

/-- The displaced signed bottom matrix. Conjugation exchanges both
indices; it is not a diagonal norm-square replacement. -/
def suzukiXiDisplacedBottomGram (rho sigma : NontrivialZetaZero) (l r b : ℝ) : ℂ :=
  (suzukiXiMixedCarrierBottomIntegral rho sigma l r b -
    starRingEnd ℂ (suzukiXiMixedCarrierBottomIntegral sigma rho l r b)) / (2 * I)

/-- The remaining signed contour-side matrix with the same conjugate
transpose and orientation as the displaced bottom matrix. -/
def suzukiXiOtherSidesGram (rho sigma : NontrivialZetaZero) (l r b u : ℝ) : ℂ :=
  (suzukiXiMixedCarrierOtherSides rho sigma l r b u -
    starRingEnd ℂ (suzukiXiMixedCarrierOtherSides sigma rho l r b u)) / (2 * I)

/-- The full signed finite mixed comparison: the bottom plus its three
oriented side corrections equals the reflected xi source plus the complete
complex carrier-pole contribution and its conjugate transpose. -/
theorem suzukiXiDisplacedBottomGram_add_otherSides_eq_source_and_poles
    (rho sigma : NontrivialZetaZero) {l r b u : ℝ}
    (hadm : SuzukiXiCarrierRectangleAdmissible l r b u) :
    suzukiXiDisplacedBottomGram rho sigma l r b + suzukiXiOtherSidesGram rho sigma l r b u =
      (Real.pi : ℂ) *
        (suzukiXiMixedContourXiSource rho sigma l r b u +
          starRingEnd ℂ (suzukiXiMixedContourXiSource sigma rho l r b u) +
          (∑ c ∈ suzukiXiCarrierGenuinePoleWindow l r b u, suzukiXiMixedCarrierPoleResidue rho sigma c) +
          starRingEnd ℂ (∑ c ∈ suzukiXiCarrierGenuinePoleWindow l r b u,
            suzukiXiMixedCarrierPoleResidue sigma rho c)) := by
  have heq : suzukiXiDisplacedBottomGram rho sigma l r b +
      suzukiXiOtherSidesGram rho sigma l r b u =
      (rectangularBoundaryIntegral l r b u (suzukiXiMixedCarrierChannel rho sigma) -
        starRingEnd ℂ (rectangularBoundaryIntegral l r b u (suzukiXiMixedCarrierChannel sigma rho))) /
          (2 * I) := by
    rw [← suzukiXiMixedCarrierBottom_add_otherSides, ← suzukiXiMixedCarrierBottom_add_otherSides]
    unfold suzukiXiDisplacedBottomGram suzukiXiOtherSidesGram
    rw [map_add]
    ring
  rw [heq, suzukiXiMixedCarrierChannel_rectangle_eq_source_add_poles rho sigma hadm,
    suzukiXiMixedCarrierChannel_rectangle_eq_source_add_poles sigma rho hadm]
  simp only [map_mul, map_add, conj_ofReal, conj_I]
  push_cast
  field_simp
  ring

/-- The actual outer horizontal integral has a uniform vanishing bound
for variable admissible-contour coordinates: height at least R and width
at most 4R give the bound 16/R, for R at least one. -/
theorem norm_suzukiXiMixedCarrierBottomIntegral_le_of_safe_height
    (rho sigma : NontrivialZetaZero) {R l r u : ℝ}
    (hR : 1 ≤ R) (hu : R ≤ u) (hwidth : |r - l| ≤ 4 * R) :
    ‖suzukiXiMixedCarrierBottomIntegral rho sigma l r u‖ ≤ 16 / R := by
  have hRpos : 0 < R := by linarith
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := l) (b := r) (fun x _ =>
      norm_suzukiXiCarrier_upper_horizontal_integrand_le rho sigma (hR.trans hu) x)
  have hbound : ‖suzukiXiMixedCarrierBottomIntegral rho sigma l r u‖ ≤
      (4 / u ^ 2) * |r - l| := by
    simpa only [suzukiXiMixedCarrierBottomIntegral, suzukiXiMixedCarrierChannel,
      mul_comm I (u : ℂ)] using hnorm
  calc
    ‖suzukiXiMixedCarrierBottomIntegral rho sigma l r u‖ ≤ (4 / u ^ 2) * |r - l| := hbound
    _ ≤ (4 / R ^ 2) * (4 * R) := by gcongr
    _ = 16 / R := by field_simp; ring

end
end RiemannGaussian
