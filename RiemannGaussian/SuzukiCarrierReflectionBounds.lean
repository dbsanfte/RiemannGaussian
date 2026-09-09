/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarrierReflectionContrast

/-!
# Cubic outer-contour decay from exact reflection cancellation

The reflection difference is kept inside the mixed channel before taking
its norm. The resulting quartic denominator gives an inverse-cube bound
for the three safe outer sides. Its numerator retains the square of the
actual node's distance from the critical line.
-/

open Complex MeasureTheory Set
namespace RiemannGaussian
noncomputable section

/-- Two quantitative node gaps and the actual unit carrier bound give
the full reflection channel a quartic decay bound. -/
theorem norm_suzukiXiReflectionCarrierChannel_le_of_gaps
    (rho : NontrivialZetaZero) {R : ℝ} {z : ℂ} (hR : 0 < R)
    (hC : ‖suzukiXiZeroCarrier z‖ ≤ 1)
    (ha : R / 2 ≤ ‖z - zetaSpectralCoordinate rho.1‖)
    (hb : R / 2 ≤ ‖z - starRingEnd ℂ (zetaSpectralCoordinate rho.1)‖) :
    ‖suzukiXiReflectionCarrierChannel rho z‖ ≤
      64 * (zetaSpectralCoordinate rho.1).im ^ 2 / R ^ 4 := by
  have hza := sub_ne_zero.mp (norm_pos_iff.mp ((half_pos hR).trans_le ha))
  have hzb := sub_ne_zero.mp (norm_pos_iff.mp ((half_pos hR).trans_le hb))
  rw [suzukiXiReflectionCarrierChannel_eq_quartic rho hza hzb]
  simp only [norm_div, norm_mul, norm_pow, norm_ofNat, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  calc
    _ ≤ (4 * (zetaSpectralCoordinate rho.1).im ^ 2 * 1) / ((R / 2) ^ 2 * (R / 2) ^ 2) := by gcongr
    _ = 64 * (zetaSpectralCoordinate rho.1).im ^ 2 / R ^ 4 := by ring

private lemma horizontal_gap (rho : NontrivialZetaZero) {R u : ℝ}
    (hR : 1 ≤ R) (hu : R ≤ u) (x : ℝ) :
    R / 2 ≤ ‖(x : ℂ) + (u : ℂ) * I - zetaSpectralCoordinate rho.1‖ := by
  have ha := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
  calc
    R / 2 ≤ u - (zetaSpectralCoordinate rho.1).im := by
      linarith [le_abs_self (zetaSpectralCoordinate rho.1).im]
    _ = ((x : ℂ) + (u : ℂ) * I - zetaSpectralCoordinate rho.1).im := by simp
    _ ≤ _ := Complex.im_le_norm _

private lemma vertical_gap (rho : NontrivialZetaZero) {R v : ℝ}
    (hv : R ≤ |v|) (ha : 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R) (y : ℝ) :
    R / 2 ≤ ‖(v : ℂ) + (y : ℂ) * I - zetaSpectralCoordinate rho.1‖ := by
  calc
    R / 2 ≤ |v| - |(zetaSpectralCoordinate rho.1).re| := by linarith
    _ ≤ |v - (zetaSpectralCoordinate rho.1).re| := abs_sub_abs_le_abs_sub _ _
    _ = |((v : ℂ) + (y : ℂ) * I - zetaSpectralCoordinate rho.1).re| := by simp
    _ ≤ _ := Complex.abs_re_le_norm _

/-- The actual reflection-contrast top costs at most the explicit
vertical-gap square times `256/R^3`. -/
theorem norm_integral_suzukiXiReflectionCarrierChannel_top_le
    (rho : NontrivialZetaZero) {R l r u : ℝ} (hR : 1 ≤ R)
    (hu : R ≤ u) (hwidth : |r - l| ≤ 4 * R) :
    ‖∫ x : ℝ in l..r, suzukiXiReflectionCarrierChannel rho ((x : ℂ) + (u : ℂ) * I)‖ ≤
      256 * (zetaSpectralCoordinate rho.1).im ^ 2 / R ^ 3 := by
  have hRpos : 0 < R := by linarith
  have hp (x : ℝ) : ‖suzukiXiReflectionCarrierChannel rho ((x : ℂ) + (u : ℂ) * I)‖ ≤
      64 * (zetaSpectralCoordinate rho.1).im ^ 2 / R ^ 4 := by
    apply norm_suzukiXiReflectionCarrierChannel_le_of_gaps rho hRpos
      (norm_suzukiXiZeroCarrier_le_one_of_half_le_im (by simpa using (show 1 / 2 ≤ u by linarith)))
      (horizontal_gap rho hR hu x)
    simpa only [NontrivialZetaZero.spectralCoordinate_conjugatePartner] using
      horizontal_gap rho.conjugatePartner hR hu x
  calc
    _ ≤ (64 * (zetaSpectralCoordinate rho.1).im ^ 2 / R ^ 4) * |r - l| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun x _ => hp x)
    _ ≤ (64 * (zetaSpectralCoordinate rho.1).im ^ 2 / R ^ 4) * (4 * R) := by gcongr
    _ = 256 * (zetaSpectralCoordinate rho.1).im ^ 2 / R ^ 3 := by field_simp; ring

/-- Each safe outer vertical reflection contrast costs at most the
actual vertical-gap square times `128/R^3`. -/
theorem norm_integral_suzukiXiReflectionCarrierChannel_vertical_le
    (rho : NontrivialZetaZero) {R v u : ℝ} (hR : 1 ≤ R)
    (hv : R ≤ |v|) (ha : 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R)
    (hu : 1 / 2 ≤ u) (huR : u ≤ 2 * R) :
    ‖∫ y : ℝ in (1 / 2)..u, suzukiXiReflectionCarrierChannel rho ((v : ℂ) + (y : ℂ) * I)‖ ≤
      128 * (zetaSpectralCoordinate rho.1).im ^ 2 / R ^ 3 := by
  have hRpos : 0 < R := by linarith
  have hp (y : ℝ) (hy : 1 / 2 ≤ y) :
      ‖suzukiXiReflectionCarrierChannel rho ((v : ℂ) + (y : ℂ) * I)‖ ≤
        64 * (zetaSpectralCoordinate rho.1).im ^ 2 / R ^ 4 := by
    apply norm_suzukiXiReflectionCarrierChannel_le_of_gaps rho hRpos
      (norm_suzukiXiZeroCarrier_le_one_of_half_le_im (by simpa using hy))
      (vertical_gap rho hv ha y)
    simpa only [NontrivialZetaZero.spectralCoordinate_conjugatePartner] using
      vertical_gap rho.conjugatePartner hv
        (by simpa only [NontrivialZetaZero.spectralCoordinate_conjugatePartner, conj_re] using ha) y
  calc
    _ ≤ (64 * (zetaSpectralCoordinate rho.1).im ^ 2 / R ^ 4) * |u - 1 / 2| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun y hy => hp y
        (show y ∈ Icc (1 / 2) u from by simpa only [uIcc_of_le hu] using uIoc_subset_uIcc hy).1)
    _ ≤ (64 * (zetaSpectralCoordinate rho.1).im ^ 2 / R ^ 4) * (2 * R) := by
      gcongr
      rw [abs_of_nonneg (by linarith)]
      linarith
    _ = 128 * (zetaSpectralCoordinate rho.1).im ^ 2 / R ^ 3 := by field_simp; ring

/-- The exact oriented safe outer contour for the coupled reflection
channel. Its cancellation is performed before any separate entry bound. -/
def suzukiXiReflectionCarrierSafeSides (rho : NontrivialZetaZero) (l r u : ℝ) : ℂ :=
  -(∫ x : ℝ in l..r, suzukiXiReflectionCarrierChannel rho ((x : ℂ) + (u : ℂ) * I)) +
    I * (∫ y : ℝ in (1 / 2)..u, suzukiXiReflectionCarrierChannel rho ((r : ℂ) + (y : ℂ) * I)) -
    I * (∫ y : ℝ in (1 / 2)..u, suzukiXiReflectionCarrierChannel rho ((l : ℂ) + (y : ℂ) * I))

/-- Keeping the reflection pair coupled improves the safe outer error
to `512*Im(alpha)^2/R^3`, retaining the actual distance from the critical line. -/
theorem norm_suzukiXiReflectionCarrierSafeSides_le
    (rho : NontrivialZetaZero) {R l r u : ℝ} (hR : 1 ≤ R)
    (hl : R ≤ |l|) (hr : R ≤ |r|) (ha : 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R)
    (hu : R ≤ u) (huR : u ≤ 2 * R) (hwidth : |r - l| ≤ 4 * R) :
    ‖suzukiXiReflectionCarrierSafeSides rho l r u‖ ≤
      512 * (zetaSpectralCoordinate rho.1).im ^ 2 / R ^ 3 := by
  have hu' : 1 / 2 ≤ u := by linarith
  have ht := norm_integral_suzukiXiReflectionCarrierChannel_top_le rho hR hu hwidth
  have hv := norm_integral_suzukiXiReflectionCarrierChannel_vertical_le rho hR hr ha hu' huR
  have hw := norm_integral_suzukiXiReflectionCarrierChannel_vertical_le rho hR hl ha hu' huR
  unfold suzukiXiReflectionCarrierSafeSides
  have hsum := norm_add_le
    (-(∫ x : ℝ in l..r, suzukiXiReflectionCarrierChannel rho ((x : ℂ) + (u : ℂ) * I)))
    (I * ∫ y : ℝ in (1 / 2)..u, suzukiXiReflectionCarrierChannel rho ((r : ℂ) + (y : ℂ) * I))
  have hsub := norm_sub_le
    (-(∫ x : ℝ in l..r, suzukiXiReflectionCarrierChannel rho ((x : ℂ) + (u : ℂ) * I)) +
      I * ∫ y : ℝ in (1 / 2)..u, suzukiXiReflectionCarrierChannel rho ((r : ℂ) + (y : ℂ) * I))
    (I * ∫ y : ℝ in (1 / 2)..u, suzukiXiReflectionCarrierChannel rho ((l : ℂ) + (y : ℂ) * I))
  simp only [norm_neg, norm_mul, norm_I, one_mul] at hsum hsub
  calc
    _ ≤ 256 * (zetaSpectralCoordinate rho.1).im ^ 2 / R ^ 3 +
        128 * (zetaSpectralCoordinate rho.1).im ^ 2 / R ^ 3 +
        128 * (zetaSpectralCoordinate rho.1).im ^ 2 / R ^ 3 := by linarith
    _ = _ := by ring

/-- On the actual admissible contour, coupling the four mixed safe-side
integrals gives exactly the integral of the reflection channel. -/
theorem suzukiXiReflectionPairQuadratic_safeSides
    (rho : NontrivialZetaZero) {l r u : ℝ}
    (hadm : SuzukiXiCarrierRealRectangleAdmissible l r u) :
    suzukiXiReflectionPairQuadratic rho (fun a b => suzukiXiMixedCarrierSafeSides a b l r u) =
      suzukiXiReflectionCarrierSafeSides rho l r u := by
  have hc (a b : NontrivialZetaZero) (γ : ℝ → ℂ) (hγ : Continuous γ)
      (hne : ∀ t, γ t ∉ suzukiXiCarrierSingularSet) :
      Continuous (fun t => suzukiXiMixedCarrierChannel a b (γ t)) :=
    continuous_comp_of_forall_analyticAt _ _ hγ
      (fun t => analyticAt_suzukiXiMixedCarrierChannel_of_not_mem a b (hne t))
  have htop (a b : NontrivialZetaZero) : IntervalIntegrable
      (fun x : ℝ => suzukiXiMixedCarrierChannel a b ((x : ℂ) + (u : ℂ) * I)) volume l r := by
    apply (hc a b _ (by fun_prop) _).intervalIntegrable
    intro x hx
    exact (hadm.2.2 _ hx).2.2 (by simp)
  have hright (a b : NontrivialZetaZero) : IntervalIntegrable
      (fun y : ℝ => suzukiXiMixedCarrierChannel a b ((r : ℂ) + (y : ℂ) * I)) volume (1 / 2) u := by
    apply (hc a b _ (by fun_prop) _).intervalIntegrable
    intro y hy
    exact (hadm.2.2 _ hy).2.1 (by simp)
  have hleft (a b : NontrivialZetaZero) : IntervalIntegrable
      (fun y : ℝ => suzukiXiMixedCarrierChannel a b ((l : ℂ) + (y : ℂ) * I)) volume (1 / 2) u := by
    apply (hc a b _ (by fun_prop) _).intervalIntegrable
    intro y hy
    exact (hadm.2.2 _ hy).1 (by simp)
  unfold suzukiXiReflectionCarrierSafeSides suzukiXiReflectionCarrierChannel
  rw [← suzukiXiReflectionPairQuadratic_intervalIntegral rho _ l r htop,
    ← suzukiXiReflectionPairQuadratic_intervalIntegral rho _ (1 / 2) u hright,
    ← suzukiXiReflectionPairQuadratic_intervalIntegral rho _ (1 / 2) u hleft]
  unfold suzukiXiReflectionPairQuadratic suzukiXiMixedCarrierSafeSides
    suzukiXiMixedCarrierBottomIntegral suzukiXiMixedCarrierUpperVerticalIntegral
  ring

/-- The reflection contrast of the signed side error has the cubic
bound itself, without multiplying four independent entry bounds. -/
theorem norm_suzukiXiReflectionPairQuadratic_side_error_le
    (rho : NontrivialZetaZero) {R l r u : ℝ} (hR : 1 ≤ R)
    (hadm : SuzukiXiCarrierRealRectangleAdmissible l r u)
    (hl : R ≤ |l|) (hr : R ≤ |r|) (ha : 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R)
    (hu : R ≤ u) (huR : u ≤ 2 * R) (hwidth : |r - l| ≤ 4 * R) :
    ‖suzukiXiReflectionPairQuadratic rho (fun a b =>
      suzukiXiOtherSidesGram a b l r 0 u - suzukiXiCarrierStripSidesGram a b l r)‖ ≤
        512 * (zetaSpectralCoordinate rho.1).im ^ 2 / R ^ 3 := by
  have he (a b : NontrivialZetaZero) :
      suzukiXiOtherSidesGram a b l r 0 u - suzukiXiCarrierStripSidesGram a b l r =
        (suzukiXiMixedCarrierSafeSides a b l r u -
          starRingEnd ℂ (suzukiXiMixedCarrierSafeSides b a l r u)) / (2 * I) := by
    unfold suzukiXiOtherSidesGram suzukiXiCarrierStripSidesGram
    rw [suzukiXiMixedCarrierOtherSides_eq_strip_add_safe a b hadm,
      suzukiXiMixedCarrierOtherSides_eq_strip_add_safe b a hadm, map_add]
    ring
  simp_rw [he]
  rw [suzukiXiReflectionPairQuadratic_signedProjection,
    suzukiXiReflectionPairQuadratic_safeSides rho hadm,
    norm_div, show ‖(2 : ℂ) * I‖ = 2 by simp]
  have hn := norm_sub_le (suzukiXiReflectionCarrierSafeSides rho l r u)
    (starRingEnd ℂ (suzukiXiReflectionCarrierSafeSides rho l r u))
  rw [Complex.norm_conj] at hn
  have hb := norm_suzukiXiReflectionCarrierSafeSides_le rho hR hl hr ha hu huR hwidth
  linarith

end
end RiemannGaussian
