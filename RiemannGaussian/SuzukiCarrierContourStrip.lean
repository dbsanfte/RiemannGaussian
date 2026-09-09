/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarrierRealContour

/-!
# Localizing the remaining signed contour correction to the zero strip

The actual carrier is bounded by one above height one half. Its two
resolvents therefore make both outer vertical pieces small once their
real coordinates pass the chosen nodes. We retain an exact splitting
of the other three contour sides into their fixed-height strip pieces
and a quantitatively vanishing outer correction. No estimate for the
carrier inside the zero strip is assumed.
-/

open Complex MeasureTheory Set
namespace RiemannGaussian
noncomputable section

private lemma vertical_distance {R v : ℝ} (hv : R ≤ |v|) {a : ℂ}
    (ha : 2 * |a.re| ≤ R) (y : ℝ) :
    R / 2 ≤ ‖(v : ℂ) + (y : ℂ) * I - a‖ := by
  calc
    R / 2 ≤ |v| - |a.re| := by linarith
    _ ≤ |v - a.re| := abs_sub_abs_le_abs_sub _ _
    _ = |((v : ℂ) + (y : ℂ) * I - a).re| := by simp
    _ ≤ ‖(v : ℂ) + (y : ℂ) * I - a‖ := Complex.abs_re_le_norm _

/-- The exact upper vertical mixed integral, beginning at the boundary
of the proved safe half-plane and retaining its real coordinate. -/
def suzukiXiMixedCarrierUpperVerticalIntegral
    (rho sigma : NontrivialZetaZero) (v u : ℝ) : ℂ :=
  ∫ y : ℝ in (1 / 2)..u, suzukiXiMixedCarrierChannel rho sigma ((v : ℂ) + (y : ℂ) * I)

/-- Above the zero strip, a remote vertical mixed channel is uniformly
bounded by `4/R^2`, with both node positions explicitly accounted for. -/
theorem norm_suzukiXiMixedCarrierChannel_vertical_le
    (rho sigma : NontrivialZetaZero) {R v y : ℝ} (hR : 0 < R)
    (hv : R ≤ |v|) (hrho : 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R)
    (hsigma : 2 * |(zetaSpectralCoordinate sigma.1).re| ≤ R) (hy : 1 / 2 ≤ y) :
    ‖suzukiXiMixedCarrierChannel rho sigma ((v : ℂ) + (y : ℂ) * I)‖ ≤ 4 / R ^ 2 := by
  have ha := vertical_distance hv (a := starRingEnd ℂ (zetaSpectralCoordinate rho.1))
    (by simpa only [conj_re] using hrho) y
  have hb := vertical_distance hv hsigma y
  have hC := norm_suzukiXiZeroCarrier_le_one_of_half_le_im
    (z := (v : ℂ) + (y : ℂ) * I) (by simpa using hy)
  unfold suzukiXiMixedCarrierChannel
  rw [norm_div, norm_mul]
  calc
    _ ≤ 1 / ((R / 2) * (R / 2)) := by gcongr
    _ = 4 / R ^ 2 := by ring

/-- The whole safe part of either outer vertical side has norm at most
`8/R` when its upper height is at most `2R`. -/
theorem norm_suzukiXiMixedCarrierUpperVerticalIntegral_le
    (rho sigma : NontrivialZetaZero) {R v u : ℝ} (hR : 1 ≤ R)
    (hv : R ≤ |v|) (hrho : 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R)
    (hsigma : 2 * |(zetaSpectralCoordinate sigma.1).re| ≤ R)
    (hu : 1 / 2 ≤ u) (huR : u ≤ 2 * R) :
    ‖suzukiXiMixedCarrierUpperVerticalIntegral rho sigma v u‖ ≤ 8 / R := by
  have hRpos : 0 < R := by linarith
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (1 / 2 : ℝ)) (b := u) (fun y hy =>
      norm_suzukiXiMixedCarrierChannel_vertical_le rho sigma hRpos hv hrho hsigma
        (show y ∈ Icc (1 / 2) u from by
          simpa only [uIcc_of_le hu] using uIoc_subset_uIcc hy).1)
  change ‖suzukiXiMixedCarrierUpperVerticalIntegral rho sigma v u‖ ≤ _ at hh
  calc
    _ ≤ (4 / R ^ 2) * |u - 1 / 2| := hh
    _ ≤ (4 / R ^ 2) * (2 * R) := by
      gcongr
      rw [abs_of_nonneg (by linarith)]
      linarith
    _ = 8 / R := by field_simp; ring

/-- The two original oriented vertical segments inside the zero strip.
Their heights stay fixed while the outer rectangle expands. -/
def suzukiXiMixedCarrierStripSides (rho sigma : NontrivialZetaZero) (l r : ℝ) : ℂ :=
  I * (∫ y : ℝ in 0..(1 / 2), suzukiXiMixedCarrierChannel rho sigma ((r : ℂ) + (y : ℂ) * I)) -
    I * (∫ y : ℝ in 0..(1 / 2), suzukiXiMixedCarrierChannel rho sigma ((l : ℂ) + (y : ℂ) * I))

/-- The top and the two safe vertical pieces, with their original
counterclockwise orientations. -/
def suzukiXiMixedCarrierSafeSides (rho sigma : NontrivialZetaZero) (l r u : ℝ) : ℂ :=
  -suzukiXiMixedCarrierBottomIntegral rho sigma l r u +
    I * suzukiXiMixedCarrierUpperVerticalIntegral rho sigma r u -
    I * suzukiXiMixedCarrierUpperVerticalIntegral rho sigma l u

/-- The full remaining sides split exactly at height one half. The
two narrow strip pieces remain signed and retain both mixed indices. -/
theorem suzukiXiMixedCarrierOtherSides_eq_strip_add_safe
    (rho sigma : NontrivialZetaZero) {l r u : ℝ}
    (hadm : SuzukiXiCarrierRealRectangleAdmissible l r u) :
    suzukiXiMixedCarrierOtherSides rho sigma l r 0 u =
      suzukiXiMixedCarrierStripSides rho sigma l r + suzukiXiMixedCarrierSafeSides rho sigma l r u := by
  have hcont (v : ℝ) (hv : ∀ c ∈ suzukiXiCarrierSingularSet, c.re ≠ v) :
      Continuous (fun y : ℝ => suzukiXiMixedCarrierChannel rho sigma ((v : ℂ) + (y : ℂ) * I)) := by
    apply continuous_comp_of_forall_analyticAt _ _ (by fun_prop)
    intro y
    apply analyticAt_suzukiXiMixedCarrierChannel_of_not_mem
    intro hc
    exact hv _ hc (by simp)
  have hl := hcont l (fun c hc => (hadm.2.2 c hc).1)
  have hr := hcont r (fun c hc => (hadm.2.2 c hc).2.1)
  have hel := intervalIntegral.integral_add_adjacent_intervals
    (hl.intervalIntegrable (μ := volume) 0 (1 / 2)) (hl.intervalIntegrable (μ := volume) (1 / 2) u)
  have her := intervalIntegral.integral_add_adjacent_intervals
    (hr.intervalIntegrable (μ := volume) 0 (1 / 2)) (hr.intervalIntegrable (μ := volume) (1 / 2) u)
  unfold suzukiXiMixedCarrierOtherSides suzukiXiMixedCarrierStripSides
    suzukiXiMixedCarrierSafeSides suzukiXiMixedCarrierBottomIntegral
    suzukiXiMixedCarrierUpperVerticalIntegral
  rw [← hel, ← her]
  ring

/-- All three safe outer pieces together cost at most `32/R`. This
bound leaves the original strip pieces and pole coefficients untouched. -/
theorem norm_suzukiXiMixedCarrierSafeSides_le
    (rho sigma : NontrivialZetaZero) {R l r u : ℝ} (hR : 1 ≤ R)
    (hl : R ≤ |l|) (hr : R ≤ |r|)
    (hrho : 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R)
    (hsigma : 2 * |(zetaSpectralCoordinate sigma.1).re| ≤ R)
    (hu : R ≤ u) (huR : u ≤ 2 * R) (hwidth : |r - l| ≤ 4 * R) :
    ‖suzukiXiMixedCarrierSafeSides rho sigma l r u‖ ≤ 32 / R := by
  have hu' : 1 / 2 ≤ u := by linarith
  have ht := norm_suzukiXiMixedCarrierBottomIntegral_le_of_safe_height rho sigma hR hu hwidth
  have hlv := norm_suzukiXiMixedCarrierUpperVerticalIntegral_le rho sigma hR hl hrho hsigma hu' huR
  have hrv := norm_suzukiXiMixedCarrierUpperVerticalIntegral_le rho sigma hR hr hrho hsigma hu' huR
  unfold suzukiXiMixedCarrierSafeSides
  calc
    _ ≤ ‖-suzukiXiMixedCarrierBottomIntegral rho sigma l r u +
        I * suzukiXiMixedCarrierUpperVerticalIntegral rho sigma r u‖ +
        ‖I * suzukiXiMixedCarrierUpperVerticalIntegral rho sigma l u‖ := norm_sub_le _ _
    _ ≤ (‖suzukiXiMixedCarrierBottomIntegral rho sigma l r u‖ +
        ‖suzukiXiMixedCarrierUpperVerticalIntegral rho sigma r u‖) +
        ‖suzukiXiMixedCarrierUpperVerticalIntegral rho sigma l u‖ := by
      have hn := norm_add_le (-suzukiXiMixedCarrierBottomIntegral rho sigma l r u)
        (I * suzukiXiMixedCarrierUpperVerticalIntegral rho sigma r u)
      simp only [norm_neg, norm_mul, norm_I, one_mul] at hn ⊢
      linarith
    _ ≤ 16 / R + 8 / R + 8 / R := by linarith
    _ = 32 / R := by ring

/-- The signed matrix of the two retained strip segments, with the
same conjugate transpose as the actual Gram comparison. -/
def suzukiXiCarrierStripSidesGram (rho sigma : NontrivialZetaZero) (l r : ℝ) : ℂ :=
  (suzukiXiMixedCarrierStripSides rho sigma l r -
    starRingEnd ℂ (suzukiXiMixedCarrierStripSides sigma rho l r)) / (2 * I)

/-- Removing the safe outer sides from the full signed side matrix
costs at most `32/R`, uniformly for the original ordered mixed pair. -/
theorem norm_suzukiXiOtherSidesGram_sub_strip_le
    (rho sigma : NontrivialZetaZero) {R l r u : ℝ} (hR : 1 ≤ R)
    (hadm : SuzukiXiCarrierRealRectangleAdmissible l r u)
    (hl : R ≤ |l|) (hr : R ≤ |r|)
    (hrho : 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R)
    (hsigma : 2 * |(zetaSpectralCoordinate sigma.1).re| ≤ R)
    (hu : R ≤ u) (huR : u ≤ 2 * R) (hwidth : |r - l| ≤ 4 * R) :
    ‖suzukiXiOtherSidesGram rho sigma l r 0 u - suzukiXiCarrierStripSidesGram rho sigma l r‖ ≤ 32 / R := by
  have ha := norm_suzukiXiMixedCarrierSafeSides_le rho sigma hR hl hr hrho hsigma hu huR hwidth
  have hb := norm_suzukiXiMixedCarrierSafeSides_le sigma rho hR hl hr hsigma hrho hu huR hwidth
  have he : suzukiXiOtherSidesGram rho sigma l r 0 u - suzukiXiCarrierStripSidesGram rho sigma l r =
      (suzukiXiMixedCarrierSafeSides rho sigma l r u -
        starRingEnd ℂ (suzukiXiMixedCarrierSafeSides sigma rho l r u)) / (2 * I) := by
    unfold suzukiXiOtherSidesGram suzukiXiCarrierStripSidesGram
    rw [suzukiXiMixedCarrierOtherSides_eq_strip_add_safe rho sigma hadm,
      suzukiXiMixedCarrierOtherSides_eq_strip_add_safe sigma rho hadm, map_add]
    ring
  rw [he, norm_div, show ‖(2 : ℂ) * I‖ = 2 by simp]
  have hn := norm_sub_le (suzukiXiMixedCarrierSafeSides rho sigma l r u)
    (starRingEnd ℂ (suzukiXiMixedCarrierSafeSides sigma rho l r u))
  rw [Complex.norm_conj] at hn
  linarith

/-- The actual real Gram comparison localizes to the two strip segments
with explicit error `32/R`. The reflected xi source, every genuine pole
and the conjugate-transposed correction remain inside the signed expression. -/
theorem norm_suzukiXiTruncatedGram_strip_comparison_le
    (rho sigma : NontrivialZetaZero)
    (h : starRingEnd ℂ (zetaSpectralCoordinate rho.1) ≠ zetaSpectralCoordinate sigma.1 ∨
      (zetaSpectralCoordinate sigma.1).im ≠ 0) {R l r u : ℝ} (hR : 1 ≤ R)
    (hadm : SuzukiXiCarrierRealRectangleAdmissible l r u)
    (hl : R ≤ |l|) (hr : R ≤ |r|)
    (hrho : 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R)
    (hsigma : 2 * |(zetaSpectralCoordinate sigma.1).re| ≤ R)
    (hu : R ≤ u) (huR : u ≤ 2 * R) (hwidth : |r - l| ≤ 4 * R) :
    ‖suzukiXiTruncatedBoundaryCarrierGramKernel rho sigma l r +
        suzukiXiCarrierStripSidesGram rho sigma l r -
      (Real.pi : ℂ) *
        (suzukiXiMixedContourXiSource rho sigma l r 0 u +
          starRingEnd ℂ (suzukiXiMixedContourXiSource sigma rho l r 0 u) +
          (∑ c ∈ suzukiXiCarrierGenuinePoleWindow l r 0 u, suzukiXiMixedCarrierPoleResidue rho sigma c) +
          starRingEnd ℂ (∑ c ∈ suzukiXiCarrierGenuinePoleWindow l r 0 u,
            suzukiXiMixedCarrierPoleResidue sigma rho c))‖ ≤ 32 / R := by
  rw [← suzukiXiTruncatedGram_add_otherSides_eq_source_and_poles rho sigma h hadm]
  have he : suzukiXiTruncatedBoundaryCarrierGramKernel rho sigma l r +
      suzukiXiCarrierStripSidesGram rho sigma l r -
        (suzukiXiTruncatedBoundaryCarrierGramKernel rho sigma l r +
          suzukiXiOtherSidesGram rho sigma l r 0 u) =
      -(suzukiXiOtherSidesGram rho sigma l r 0 u - suzukiXiCarrierStripSidesGram rho sigma l r) := by ring
  rw [he, norm_neg]
  exact norm_suzukiXiOtherSidesGram_sub_strip_le rho sigma hR hadm hl hr hrho hsigma hu huR hwidth

end
end RiemannGaussian
