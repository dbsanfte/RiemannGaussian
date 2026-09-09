/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarrierReflectionBounds

/-!
# An explicit signed source budget for a hypothetical right-half zero

The canonical reflection difference has nonnegative actual Gram energy
and an exactly negative reflected xi source. We keep its complete pole
and strip-side correction as one real quantity. The safe outer error
has the stronger cubic bound coming from reflection cancellation.

The resulting lower bound is a necessary consequence of the hypothetical
zero. An independent upper bound below this threshold remains the open
arithmetic step; it is not supplied by the contour identity.
-/

open Complex Filter MeasureTheory Set
namespace RiemannGaussian
noncomputable section

/-- A right-half zero lies below the real spectral axis, while its exact
partner lies inside every upper rectangle enclosing their common real
coordinate and reaching height one half. -/
theorem suzukiXiRightHalf_reflection_window_membership
    (rho : NontrivialZetaZero) (hzero : 1 / 2 < rho.1.re) {l r u : ℝ}
    (hl : l < (zetaSpectralCoordinate rho.1).re)
    (hr : (zetaSpectralCoordinate rho.1).re < r) (hu : 1 / 2 ≤ u) :
    zetaSpectralCoordinate rho.conjugatePartner.1 ∈ suzukiXiCarrierPoleWindow l r 0 u ∧
      zetaSpectralCoordinate rho.1 ∉ suzukiXiCarrierPoleWindow l r 0 u := by
  have him : (zetaSpectralCoordinate rho.1).im < 0 := by
    rw [zetaSpectralCoordinate_im]
    linarith
  have hupper : (zetaSpectralCoordinate rho.conjugatePartner.1).im < 1 / 2 :=
    (le_abs_self _).trans_lt (NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho.conjugatePartner)
  have hu0 : 0 ≤ u := by linarith
  constructor
  · apply mem_suzukiXiCarrierPoleWindow.mpr
    constructor
    · have hrp : (zetaSpectralCoordinate rho.conjugatePartner.1).re =
          (zetaSpectralCoordinate rho.1).re := by
        rw [NontrivialZetaZero.spectralCoordinate_conjugatePartner, conj_re]
      have hip : 0 ≤ (zetaSpectralCoordinate rho.conjugatePartner.1).im := by
        rw [NontrivialZetaZero.spectralCoordinate_conjugatePartner, conj_im]
        linarith
      have hreal : l ≤ (zetaSpectralCoordinate rho.conjugatePartner.1).re ∧
          (zetaSpectralCoordinate rho.conjugatePartner.1).re ≤ r := by
        rw [hrp]
        exact ⟨hl.le, hr.le⟩
      simpa [Complex.Rectangle, Complex.mem_reProdIm, uIcc_of_le (hl.trans hr).le,
        uIcc_of_le hu0] using And.intro hreal
          (And.intro hip (hupper.le.trans hu))
    · exact Or.inl ((riemannXiSpectral_eq_zero_iff_exists_zetaZero _).mpr ⟨_, rfl⟩)
  · intro hc
    have hb : 0 ≤ (zetaSpectralCoordinate rho.1).im := by
      have hm := (mem_suzukiXiCarrierPoleWindow.mp hc).1
      have hm' : (l ≤ (zetaSpectralCoordinate rho.1).re ∧ (zetaSpectralCoordinate rho.1).re ≤ r) ∧
          0 ≤ (zetaSpectralCoordinate rho.1).im ∧ (zetaSpectralCoordinate rho.1).im ≤ u := by
        simpa [Complex.Rectangle, Complex.mem_reProdIm, uIcc_of_le (hl.trans hr).le,
          uIcc_of_le hu0] using hm
      exact hm'.2.1
    exact (not_le_of_gt him) hb

/-- The entire pole and fixed-height side correction tested against the
canonical reflection difference. It retains every mixed residue and the
signed strip integral in the same quantity. -/
def suzukiXiReflectionStripCorrection (rho : NontrivialZetaZero) (l r u : ℝ) : ℝ :=
  2 * Real.pi * (suzukiXiReflectionPairQuadratic rho (fun a b =>
    ∑ c ∈ suzukiXiCarrierGenuinePoleWindow l r 0 u, suzukiXiMixedCarrierPoleResidue a b c)).re -
      (suzukiXiReflectionPairQuadratic rho (fun a b => suzukiXiCarrierStripSidesGram a b l r)).re

/-- The exact signed real comparison for the reflection difference at a
right-half zero. Its nonnegative Gram energy is retained, as is the entire
safe side error before applying the cubic bound. -/
theorem suzukiXiReflectionStripCorrection_eq_source_add_energy_add_error
    (rho : NontrivialZetaZero) (hzero : 1 / 2 < rho.1.re) {l r u : ℝ}
    (hadm : SuzukiXiCarrierRealRectangleAdmissible l r u)
    (hl : l < (zetaSpectralCoordinate rho.1).re)
    (hr : (zetaSpectralCoordinate rho.1).re < r) (hu : 1 / 2 ≤ u) :
    suzukiXiReflectionStripCorrection rho l r u =
      2 * Real.pi / (analyticZetaZeroMultiplicity rho : ℝ) +
        (suzukiXiReflectionPairQuadratic rho (fun a b =>
          suzukiXiTruncatedBoundaryCarrierGramKernel a b l r)).re +
        (suzukiXiReflectionPairQuadratic rho (fun a b =>
          suzukiXiOtherSidesGram a b l r 0 u - suzukiXiCarrierStripSidesGram a b l r)).re := by
  have him : (zetaSpectralCoordinate rho.1).im ≠ 0 := by
    rw [zetaSpectralCoordinate_im]
    linarith
  have hip : (zetaSpectralCoordinate rho.conjugatePartner.1).im ≠ 0 := by
    simpa only [NontrivialZetaZero.spectralCoordinate_conjugatePartner, conj_im, neg_ne_zero] using him
  have h00 := suzukiXiTruncatedGram_add_otherSides_eq_source_and_poles rho rho (Or.inr him) hadm
  have h01 := suzukiXiTruncatedGram_add_otherSides_eq_source_and_poles rho rho.conjugatePartner (Or.inr hip) hadm
  have h10 := suzukiXiTruncatedGram_add_otherSides_eq_source_and_poles rho.conjugatePartner rho (Or.inr him) hadm
  have h11 := suzukiXiTruncatedGram_add_otherSides_eq_source_and_poles
    rho.conjugatePartner rho.conjugatePartner (Or.inr hip) hadm
  let Z := fun a b => suzukiXiMixedContourXiSource a b l r 0 u
  let K := fun a b => ∑ c ∈ suzukiXiCarrierGenuinePoleWindow l r 0 u,
    suzukiXiMixedCarrierPoleResidue a b c
  have he : suzukiXiReflectionPairQuadratic rho
      (fun a b => suzukiXiTruncatedBoundaryCarrierGramKernel a b l r) +
        suzukiXiReflectionPairQuadratic rho (fun a b => suzukiXiOtherSidesGram a b l r 0 u) =
      (Real.pi : ℂ) * (suzukiXiReflectionPairQuadratic rho Z +
        starRingEnd ℂ (suzukiXiReflectionPairQuadratic rho Z) +
        suzukiXiReflectionPairQuadratic rho K + starRingEnd ℂ (suzukiXiReflectionPairQuadratic rho K)) := by
    simp only [suzukiXiReflectionPairQuadratic, map_add, map_sub, Z, K]
    linear_combination h00 - h01 - h10 + h11
  obtain ⟨hp, hn⟩ := suzukiXiRightHalf_reflection_window_membership rho hzero hl hr hu
  have hZ : suzukiXiReflectionPairQuadratic rho Z = -(analyticZetaZeroMultiplicity rho : ℂ)⁻¹ :=
    suzukiXiReflectionPairQuadratic_source_eq_neg_inv_multiplicity rho l r 0 u hp hn
  rw [hZ] at he
  have hre := congrArg Complex.re he
  have hm : ((analyticZetaZeroMultiplicity rho : ℂ)⁻¹).re =
      (analyticZetaZeroMultiplicity rho : ℝ)⁻¹ := by
    rw [show (analyticZetaZeroMultiplicity rho : ℂ) = ((analyticZetaZeroMultiplicity rho : ℝ) : ℂ) by simp,
      ← ofReal_inv, ofReal_re]
  simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
    conj_re, neg_re, hm] at hre
  have hsplit : suzukiXiReflectionPairQuadratic rho (fun a b =>
      suzukiXiOtherSidesGram a b l r 0 u - suzukiXiCarrierStripSidesGram a b l r) =
        suzukiXiReflectionPairQuadratic rho (fun a b => suzukiXiOtherSidesGram a b l r 0 u) -
          suzukiXiReflectionPairQuadratic rho (fun a b => suzukiXiCarrierStripSidesGram a b l r) := by
    unfold suzukiXiReflectionPairQuadratic
    ring
  rw [hsplit, sub_re]
  change 2 * Real.pi * (suzukiXiReflectionPairQuadratic rho K).re - _ = _
  rw [div_eq_mul_inv]
  linarith

/-- A hypothetical right-half zero forces the coupled strip correction
to reach its exact source, up to the proved cubic outer error. This is the
lower threshold that an independent upper bound must beat. -/
theorem suzukiXiReflectionStripCorrection_source_floor
    (rho : NontrivialZetaZero) (hzero : 1 / 2 < rho.1.re) {R l r u : ℝ}
    (hR : 1 ≤ R) (hadm : SuzukiXiCarrierRealRectangleAdmissible l r u)
    (hl : R ≤ |l|) (hr : R ≤ |r|) (ha : 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R)
    (hlnode : l < (zetaSpectralCoordinate rho.1).re)
    (hrnode : (zetaSpectralCoordinate rho.1).re < r)
    (hu : R ≤ u) (huR : u ≤ 2 * R) (hwidth : |r - l| ≤ 4 * R) :
    2 * Real.pi / (analyticZetaZeroMultiplicity rho : ℝ) -
        512 * (zetaSpectralCoordinate rho.1).im ^ 2 / R ^ 3 ≤
      suzukiXiReflectionStripCorrection rho l r u := by
  rw [suzukiXiReflectionStripCorrection_eq_source_add_energy_add_error rho hzero hadm hlnode hrnode
    (by linarith)]
  have henergy := suzukiXiReflectionPairQuadratic_truncatedGram_re_nonneg rho hadm.1.le
  have herror := norm_suzukiXiReflectionPairQuadratic_side_error_le rho hR hadm hl hr ha hu huR hwidth
  have hre := Complex.abs_re_le_norm (suzukiXiReflectionPairQuadratic rho (fun a b =>
    suzukiXiOtherSidesGram a b l r 0 u - suzukiXiCarrierStripSidesGram a b l r))
  have hlo := (abs_le.mp (hre.trans herror)).1
  linarith

/-- At every sufficiently large outer scale there are actual admissible
rectangles on which the hypothetical zero forces the explicit source floor.
All node-enclosure and contour-size conditions are discharged here. -/
theorem exists_suzukiXiReflectionStripCorrection_source_floor
    (rho : NontrivialZetaZero) (hzero : 1 / 2 < rho.1.re) {R : ℝ}
    (hR : 1 ≤ R) (ha : 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R) :
    ∃ l r u : ℝ, SuzukiXiCarrierRealRectangleAdmissible l r u ∧
      (-R - 1 < l ∧ l < -R) ∧ (R < r ∧ r < R + 1) ∧ (R < u ∧ u < R + 1) ∧
      2 * Real.pi / (analyticZetaZeroMultiplicity rho : ℝ) -
          512 * (zetaSpectralCoordinate rho.1).im ^ 2 / R ^ 3 ≤
        suzukiXiReflectionStripCorrection rho l r u := by
  obtain ⟨l, r, u, hadm, hl, hr, hu⟩ := exists_suzukiXiCarrierRealRectangleAdmissible hR
  refine ⟨l, r, u, hadm, hl, hr, hu, ?_⟩
  apply suzukiXiReflectionStripCorrection_source_floor rho hzero hR hadm
  · rw [abs_of_neg (by linarith [hl.2])]
    linarith [hl.2]
  · rw [abs_of_pos (by linarith [hr.1])]
    exact hr.1.le
  · exact ha
  · linarith [neg_le_abs (zetaSpectralCoordinate rho.1).re, hl.2]
  · linarith [le_abs_self (zetaSpectralCoordinate rho.1).re, hr.1]
  · exact hu.1.le
  · linarith [hu.2]
  · rw [abs_of_pos (sub_pos.mpr hadm.1)]
    linarith [hl.1, hr.2]

end
end RiemannGaussian
