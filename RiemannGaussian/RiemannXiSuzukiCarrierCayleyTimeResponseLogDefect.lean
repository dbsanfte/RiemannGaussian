import RiemannGaussian.RiemannXiSuzukiCarrierCayleyTimeResponseCollarPositivity
import RiemannGaussian.RiemannXiSpectralWindowMass
import RiemannGaussian.RiemannXiHyperbolicHeatWindow

/-!
# The Suzuki initial response as the height derivative of log defect

The finite signed Suzuki response and the Gaussian/hyperbolic log defect are
two descriptions of the same finite upper divisor.  This file joins them
without an infinite limiting argument.  A real logarithmic squared-distance
ratio is used as an antiderivative through the real boundary.  In a zero-free
vertical collar it agrees with the established pseudo-hyperbolic log defect,
and its height derivative is exactly twice the real part of the scaled finite
Blaschke response.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The logarithmic squared-distance ratio for an upper-half-plane point,
continued as a real-valued function along a vertical boundary line. -/
def upperHalfPlaneVerticalLogDefect
    (x y : ℝ) (alpha : ℂ) : ℝ :=
  Real.log (Complex.normSq
      (upperBoundaryApproachPoint x y - starRingEnd ℂ alpha)) -
    Real.log (Complex.normSq
      (upperBoundaryApproachPoint x y - alpha))

/-- At a distinct positive-height point, the vertical squared-distance ratio
is exactly the usual pseudo-hyperbolic logarithmic defect. -/
theorem upperHalfPlaneVerticalLogDefect_eq_neg_two_log_distance
    {x y : ℝ} {alpha : ℂ} (hy : 0 < y) (halpha : 0 < alpha.im)
    (hne : upperBoundaryApproachPoint x y ≠ alpha) :
    upperHalfPlaneVerticalLogDefect x y alpha =
      -2 * Real.log (upperHalfPlanePseudoHyperbolicDistance
        (upperBoundaryApproachPoint x y) alpha) := by
  have hupper : 0 < pairHyperbolicUpperSq
      (x - alpha.re) y alpha.im := by
    rw [show pairHyperbolicUpperSq (x - alpha.re) y alpha.im =
        Complex.normSq (upperBoundaryApproachPoint x y - alpha) by
      unfold pairHyperbolicUpperSq upperBoundaryApproachPoint Complex.normSq
      simp
      ring]
    exact Complex.normSq_pos.mpr (sub_ne_zero.mpr hne)
  have hlower : 0 < pairHyperbolicLowerSq
      (x - alpha.re) y alpha.im :=
    pairHyperbolicLowerSq_pos halpha hy
  have halphaForm :
      (alpha.re : ℂ) + Complex.I * (alpha.im : ℂ) = alpha := by
    rw [mul_comm]
    exact Complex.re_add_im alpha
  have hdistance :
      upperHalfPlanePseudoHyperbolicDistance
          (upperBoundaryApproachPoint x y) alpha =
        pairHyperbolicRadius (x - alpha.re) y alpha.im := by
    calc
      upperHalfPlanePseudoHyperbolicDistance
          (upperBoundaryApproachPoint x y) alpha =
          upperHalfPlanePseudoHyperbolicDistance
            ((x : ℂ) + Complex.I * (y : ℂ))
            ((alpha.re : ℂ) + Complex.I * (alpha.im : ℂ)) := by
        rw [halphaForm]
        unfold upperBoundaryApproachPoint
        ring
      _ = pairHyperbolicRadius (x - alpha.re) y alpha.im :=
        upperHalfPlanePseudoHyperbolicDistance_eq_pairRadius
          alpha.re alpha.im x y halpha hy
  calc
    upperHalfPlaneVerticalLogDefect x y alpha =
        Real.log (pairHyperbolicLowerSq (x - alpha.re) y alpha.im) -
          Real.log (pairHyperbolicUpperSq (x - alpha.re) y alpha.im) := by
      unfold upperHalfPlaneVerticalLogDefect
      congr 2
      · unfold pairHyperbolicLowerSq upperBoundaryApproachPoint
        simp [Complex.normSq_apply]
        ring
      · unfold pairHyperbolicUpperSq upperBoundaryApproachPoint
        simp [Complex.normSq_apply]
        ring
    _ = Real.log
        (pairHyperbolicLowerSq (x - alpha.re) y alpha.im /
          pairHyperbolicUpperSq (x - alpha.re) y alpha.im) := by
      rw [Real.log_div hlower.ne' hupper.ne']
    _ = -2 * Real.log
        (pairHyperbolicRadius (x - alpha.re) y alpha.im) :=
      pairHyperbolicLogRatio_eq_neg_two_log_radius hy halpha hupper
    _ = -2 * Real.log (upperHalfPlanePseudoHyperbolicDistance
        (upperBoundaryApproachPoint x y) alpha) := by rw [hdistance]

/-- The continued vertical defect vanishes exactly on the real boundary. -/
@[simp]
theorem upperHalfPlaneVerticalLogDefect_zero
    (x : ℝ) (alpha : ℂ) :
    upperHalfPlaneVerticalLogDefect x 0 alpha = 0 := by
  unfold upperHalfPlaneVerticalLogDefect
  rw [upperBoundaryApproachPoint_zero]
  have heq : Complex.normSq
      ((x : ℂ) - starRingEnd ℂ alpha) =
      Complex.normSq ((x : ℂ) - alpha) := by
    unfold Complex.normSq
    simp
  rw [heq]
  ring

/-- Exact derivative of the logarithmic squared-distance ratio at any point
where the two squared distances are nonzero. -/
theorem hasDerivAt_upperHalfPlaneVerticalLogDefect
    (x y : ℝ) (alpha : ℂ)
    (hminus : Complex.normSq
        (upperBoundaryApproachPoint x y - alpha) ≠ 0)
    (hplus : Complex.normSq
        (upperBoundaryApproachPoint x y - starRingEnd ℂ alpha) ≠ 0) :
    HasDerivAt (fun v : ℝ ↦ upperHalfPlaneVerticalLogDefect x v alpha)
      ((2 * y + 2 * alpha.im) /
          Complex.normSq
            (upperBoundaryApproachPoint x y - starRingEnd ℂ alpha) -
        (2 * y - 2 * alpha.im) /
          Complex.normSq (upperBoundaryApproachPoint x y - alpha)) y := by
  let D : ℝ := Complex.normSq ((x : ℂ) - alpha)
  let a : ℝ := alpha.im
  have hplusEq : Complex.normSq
      (upperBoundaryApproachPoint x y - starRingEnd ℂ alpha) =
      D + y ^ 2 + 2 * y * a := by
    rw [normSq_upperBoundaryApproachPoint_sub_conj]
  have hminusEq : Complex.normSq
      (upperBoundaryApproachPoint x y - alpha) =
      D + y ^ 2 - 2 * y * a := by
    rw [normSq_upperBoundaryApproachPoint_sub]
  have hsq : HasDerivAt (fun v : ℝ ↦ v ^ 2) (2 * y) y := by
    simpa [two_mul] using (hasDerivAt_pow 2 y)
  have hlin : HasDerivAt (fun v : ℝ ↦ 2 * v * a) (2 * a) y := by
    simpa [mul_comm, mul_left_comm] using
      (hasDerivAt_id y).const_mul (2 * a)
  have hqplus : HasDerivAt
      (fun v : ℝ ↦ D + v ^ 2 + 2 * v * a)
      (2 * y + 2 * a) y := by
    have h := (((hasDerivAt_const (𝕜 := ℝ) y D).add hsq).add hlin)
    simpa only [Pi.add_apply, zero_add] using! h
  have hqminus : HasDerivAt
      (fun v : ℝ ↦ D + v ^ 2 - 2 * v * a)
      (2 * y - 2 * a) y := by
    have h := (((hasDerivAt_const (𝕜 := ℝ) y D).add hsq).sub hlin)
    simpa only [Pi.add_apply, Pi.sub_apply, zero_add] using! h
  have hqplusNe : D + y ^ 2 + 2 * y * a ≠ 0 := by
    rw [← hplusEq]
    exact hplus
  have hqminusNe : D + y ^ 2 - 2 * y * a ≠ 0 := by
    rw [← hminusEq]
    exact hminus
  have hderiv := (hqplus.log hqplusNe).sub (hqminus.log hqminusNe)
  have hfun : (fun v : ℝ ↦ upperHalfPlaneVerticalLogDefect x v alpha) =
      fun v : ℝ ↦ Real.log (D + v ^ 2 + 2 * v * a) -
        Real.log (D + v ^ 2 - 2 * v * a) := by
    funext v
    unfold upperHalfPlaneVerticalLogDefect
    rw [normSq_upperBoundaryApproachPoint_sub_conj,
      normSq_upperBoundaryApproachPoint_sub]
  rw [hfun, hplusEq, hminusEq]
  simpa [D, a] using! hderiv

/-- One multiplicity-counted upper-zero contribution to the vertically
continued real log defect. -/
def zetaUpperVerticalLogDefectSummand
    (x y : ℝ) (rho : NontrivialZetaZero) : ℝ :=
  (analyticZetaZeroMultiplicity rho : ℝ) *
    upperHalfPlaneVerticalLogDefect x y
      (zetaSpectralCoordinate rho.1)

/-- The vertically continued real log defect in one finite upper spectral
window. -/
def riemannXiUpperVerticalLogDefectWindow
    (x y T : ℝ) : ℝ :=
  ∑ rho ∈ spectralUpperZetaZeroWindow T,
    zetaUpperVerticalLogDefectSummand x y rho

/-- The real-valued finite hyperbolic log-defect sum underlying the existing
extended-nonnegative window. -/
def riemannXiUpperHyperbolicLogDefectRealWindow
    (z : ℂ) (T : ℝ) : ℝ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    zetaUpperHyperbolicLogDefectSummand z rho

/-- The positive-proper-time action of one finite spectral heat window. -/
def riemannXiUpperHyperbolicHeatActionWindow
    (z : ℂ) (T : ℝ) : ℝ≥0∞ :=
  ∫⁻ tau in Set.Ioi (0 : ℝ),
    ENNReal.ofReal (riemannXiUpperHyperbolicHeatWindow z tau T)

/-- One selected vertical summand agrees with the established hyperbolic log
defect at every distinct positive-height observation point. -/
theorem zetaUpperVerticalLogDefectSummand_eq_hyperbolic
    {x y : ℝ} (rho : NontrivialZetaZero) (hy : 0 < y)
    (hupper : 0 < (zetaSpectralCoordinate rho.1).im)
    (hne : upperBoundaryApproachPoint x y ≠
      zetaSpectralCoordinate rho.1) :
    zetaUpperVerticalLogDefectSummand x y rho =
      zetaUpperHyperbolicLogDefectSummand
        (upperBoundaryApproachPoint x y) rho := by
  unfold zetaUpperVerticalLogDefectSummand
    zetaUpperHyperbolicLogDefectSummand
  rw [if_pos hupper,
    upperHalfPlaneVerticalLogDefect_eq_neg_two_log_distance
      hy hupper hne]

/-- At positive height, a noncolliding vertical window is exactly the
real-valued finite hyperbolic log-defect window already used by the Gaussian
proper-time construction. -/
theorem riemannXiUpperVerticalLogDefectWindow_eq_hyperbolicRealWindow
    {x y T : ℝ} (hy : 0 < y)
    (hne : ∀ rho ∈ spectralUpperZetaZeroWindow T,
      upperBoundaryApproachPoint x y ≠ zetaSpectralCoordinate rho.1) :
    riemannXiUpperVerticalLogDefectWindow x y T =
      riemannXiUpperHyperbolicLogDefectRealWindow
        (upperBoundaryApproachPoint x y) T := by
  unfold riemannXiUpperVerticalLogDefectWindow
    riemannXiUpperHyperbolicLogDefectRealWindow
    spectralUpperZetaZeroWindow
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro rho hrho
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · rw [if_pos hupper]
    exact zetaUpperVerticalLogDefectSummand_eq_hyperbolic
      rho hy hupper
        (hne rho (mem_spectralUpperZetaZeroWindow.mpr ⟨hrho, hupper⟩))
  · rw [if_neg hupper, zetaUpperHyperbolicLogDefectSummand,
      if_neg hupper]

/-- Taking `ofReal` of the finite real hyperbolic window recovers exactly
the established `ℝ≥0∞` window whenever selected upper zeros do not collide
with the observation point. -/
theorem ofReal_riemannXiUpperHyperbolicLogDefectRealWindow_eq
    {z : ℂ} (hz : 0 < z.im) {T : ℝ}
    (hne : ∀ rho ∈ spectralUpperZetaZeroWindow T,
      z ≠ zetaSpectralCoordinate rho.1) :
    ENNReal.ofReal (riemannXiUpperHyperbolicLogDefectRealWindow z T) =
      riemannXiUpperHyperbolicLogDefectWindow z T := by
  unfold riemannXiUpperHyperbolicLogDefectRealWindow
    riemannXiUpperHyperbolicLogDefectWindow
  rw [ENNReal.ofReal_sum_of_nonneg]
  intro rho hrho
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · apply zetaUpperHyperbolicLogDefectSummand_nonneg hz rho
    exact hne rho (mem_spectralUpperZetaZeroWindow.mpr ⟨hrho, hupper⟩)
  · rw [zetaUpperHyperbolicLogDefectSummand, if_neg hupper]

/-- Finite Tonelli identity: the positive-proper-time action of a finite
spectral heat window is exactly its finite hyperbolic log-defect window. -/
theorem riemannXiUpperHyperbolicHeatActionWindow_eq_logDefectWindow
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0)
    (T : ℝ) :
    riemannXiUpperHyperbolicHeatActionWindow z T =
      riemannXiUpperHyperbolicLogDefectWindow z T := by
  unfold riemannXiUpperHyperbolicHeatActionWindow
    riemannXiUpperHyperbolicHeatWindow
    riemannXiUpperHyperbolicLogDefectWindow
  calc
    (∫⁻ tau in Set.Ioi (0 : ℝ),
        ENNReal.ofReal
          (∑ rho ∈ spectralZetaZeroWindow T,
            zetaUpperHyperbolicHeatSummand z tau rho)) =
        ∫⁻ tau in Set.Ioi (0 : ℝ),
          ∑ rho ∈ spectralZetaZeroWindow T,
            ENNReal.ofReal
              (zetaUpperHyperbolicHeatSummand z tau rho) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with tau htau
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro rho _hrho
      exact zetaUpperHyperbolicHeatSummand_nonneg hz htau rho
    _ = ∑ rho ∈ spectralZetaZeroWindow T,
          ∫⁻ tau in Set.Ioi (0 : ℝ),
            ENNReal.ofReal
              (zetaUpperHyperbolicHeatSummand z tau rho) := by
      exact MeasureTheory.lintegral_finsetSum'
        (spectralZetaZeroWindow T)
        (fun rho _hrho ↦
          aemeasurable_ofReal_zetaUpperHyperbolicHeatSummand z rho)
    _ = ∑ rho ∈ spectralZetaZeroWindow T,
          ENNReal.ofReal
            (zetaUpperHyperbolicLogDefectSummand z rho) := by
      apply Finset.sum_congr rfl
      intro rho _hrho
      exact lintegral_ofReal_zetaUpperHyperbolicHeatSummand hz hxi rho

/-- The derivative of one multiplicity-counted vertical defect is exactly
twice the real part of its scaled signed Blaschke response. -/
theorem hasDerivAt_zetaUpperVerticalLogDefectSummand
    {x y : ℝ} (rho : NontrivialZetaZero) (hy : 0 ≤ y)
    (hupper : 0 < (zetaSpectralCoordinate rho.1).im)
    (hradial : y ^ 2 < Complex.normSq
      ((x : ℂ) - zetaSpectralCoordinate rho.1)) :
    HasDerivAt
      (fun v : ℝ ↦ zetaUpperVerticalLogDefectSummand x v rho)
      (2 * (-Complex.I * zetaUpperBlaschkeLogDerivativeSummand
        (upperBoundaryApproachPoint x y) rho).re) y := by
  let alpha : ℂ := zetaSpectralCoordinate rho.1
  let z : ℂ := upperBoundaryApproachPoint x y
  have hminus : Complex.normSq (z - alpha) ≠ 0 := by
    apply ne_of_gt
    apply Complex.normSq_pos.mpr
    intro hzero
    have heq : z = alpha := sub_eq_zero.mp hzero
    have hre := congrArg Complex.re heq
    have him := congrArg Complex.im heq
    dsimp [z, alpha] at hre him
    simp only [upperBoundaryApproachPoint_re,
      upperBoundaryApproachPoint_im] at hre him
    rw [Complex.normSq_apply] at hradial
    simp only [sub_re, ofReal_re, sub_im, ofReal_im] at hradial
    rw [← hre, ← him] at hradial
    nlinarith
  have hplus : Complex.normSq (z - starRingEnd ℂ alpha) ≠ 0 := by
    apply ne_of_gt
    apply Complex.normSq_pos.mpr
    intro hzero
    have heq : z = starRingEnd ℂ alpha := sub_eq_zero.mp hzero
    have him := congrArg Complex.im heq
    dsimp [z, alpha] at him
    simp only [upperBoundaryApproachPoint_im] at him
    linarith
  have hbase := hasDerivAt_upperHalfPlaneVerticalLogDefect
    x y alpha hminus hplus
  unfold zetaUpperVerticalLogDefectSummand
  apply (hbase.const_mul
    (analyticZetaZeroMultiplicity rho : ℝ)).congr_deriv
  rw [re_neg_I_mul_zetaUpperBlaschkeLogDerivativeSummand_approach_eq
    x y rho hradial]
  have hminusEq : Complex.normSq (z - alpha) =
      Complex.normSq ((x : ℂ) - alpha) + y ^ 2 - 2 * y * alpha.im := by
    exact normSq_upperBoundaryApproachPoint_sub x y alpha
  have hplusEq : Complex.normSq (z - starRingEnd ℂ alpha) =
      Complex.normSq ((x : ℂ) - alpha) + y ^ 2 + 2 * y * alpha.im := by
    exact normSq_upperBoundaryApproachPoint_sub_conj x y alpha
  change
    (analyticZetaZeroMultiplicity rho : ℝ) *
        ((2 * y + 2 * alpha.im) /
            Complex.normSq (z - starRingEnd ℂ alpha) -
          (2 * y - 2 * alpha.im) /
            Complex.normSq (z - alpha)) =
      2 * ((analyticZetaZeroMultiplicity rho : ℝ) *
        (2 * alpha.im *
          (Complex.normSq ((x : ℂ) - alpha) - y ^ 2) /
            (Complex.normSq (z - alpha) *
              Complex.normSq (z - starRingEnd ℂ alpha))))
  field_simp [hminus, hplus]
  rw [hminusEq, hplusEq]
  ring

/-- Every finite vertical defect window vanishes on the real boundary. -/
@[simp]
theorem riemannXiUpperVerticalLogDefectWindow_zero
    (x T : ℝ) :
    riemannXiUpperVerticalLogDefectWindow x 0 T = 0 := by
  unfold riemannXiUpperVerticalLogDefectWindow
    zetaUpperVerticalLogDefectSummand
  simp

/-- In a uniform zero-free collar, the derivative of the complete finite
vertical defect window is exactly twice the scaled finite Blaschke response.
This is a finite identity: no convergence or differentiation of a series is
used. -/
theorem hasDerivAt_riemannXiUpperVerticalLogDefectWindow
    {x delta u : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hu : 0 ≤ u) (huSmall : u < delta / 2) (T : ℝ) :
    HasDerivAt
      (fun v : ℝ ↦ riemannXiUpperVerticalLogDefectWindow x v T)
      (2 * (-Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow
        (upperBoundaryApproachPoint x u) T).re) u := by
  unfold riemannXiUpperVerticalLogDefectWindow
  have hsum : HasDerivAt
      (fun v : ℝ ↦ ∑ rho ∈ spectralUpperZetaZeroWindow T,
        zetaUpperVerticalLogDefectSummand x v rho)
      (∑ rho ∈ spectralUpperZetaZeroWindow T,
        2 * (-Complex.I * zetaUpperBlaschkeLogDerivativeSummand
          (upperBoundaryApproachPoint x u) rho).re) u := by
    apply HasDerivAt.fun_sum
    intro rho hrho
    have hupper := (mem_spectralUpperZetaZeroWindow.mp hrho).2
    have hnorm := hgap rho hupper
    have huNorm : u < ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖ := by
      have hhalf : delta / 2 ≤
          ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖ :=
        (half_le_self hdelta.le).trans hnorm
      exact huSmall.trans_le hhalf
    have hradial : u ^ 2 < Complex.normSq
        ((x : ℂ) - zetaSpectralCoordinate rho.1) := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg
        ((x : ℂ) - zetaSpectralCoordinate rho.1)]
    exact hasDerivAt_zetaUpperVerticalLogDefectSummand
      rho hu hupper hradial
  apply hsum.congr_deriv
  unfold riemannXiUpperBlaschkeLogDerivativeWindow
  rw [Finset.mul_sum, Complex.re_sum]
  simp only [mul_re, neg_re, I_re, neg_im, I_im]
  rw [Finset.mul_sum]

/-- A single signed Blaschke response is continuous along a vertical line at
every point avoiding its zero and reflected pole. -/
theorem continuousAt_zetaUpperBlaschkeLogDerivativeSummand_approach
    {x u : ℝ} (rho : NontrivialZetaZero)
    (hminus : upperBoundaryApproachPoint x u ≠
      zetaSpectralCoordinate rho.1)
    (hplus : upperBoundaryApproachPoint x u ≠
      starRingEnd ℂ (zetaSpectralCoordinate rho.1)) :
    ContinuousAt
      (fun v : ℝ ↦ zetaUpperBlaschkeLogDerivativeSummand
        (upperBoundaryApproachPoint x v) rho) u := by
  have hminus' : upperBoundaryApproachPoint x u -
      zetaSpectralCoordinate rho.1 ≠ 0 := sub_ne_zero.mpr hminus
  have hplus' : upperBoundaryApproachPoint x u -
      starRingEnd ℂ (zetaSpectralCoordinate rho.1) ≠ 0 :=
    sub_ne_zero.mpr hplus
  unfold zetaUpperBlaschkeLogDerivativeSummand
  unfold upperBoundaryApproachPoint at hminus' hplus' ⊢
  fun_prop

/-- The scaled finite Blaschke response is continuous at every point of a
uniform zero-free vertical collar, including the boundary height `0`. -/
theorem continuousAt_two_mul_re_neg_I_blaschkeLogDerivativeWindow_approach
    {x delta u : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hu : 0 ≤ u) (huSmall : u < delta / 2) (T : ℝ) :
    ContinuousAt
      (fun v : ℝ ↦ 2 *
        (-Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow
          (upperBoundaryApproachPoint x v) T).re) u := by
  let s : Finset NontrivialZetaZero := spectralUpperZetaZeroWindow T
  let f : NontrivialZetaZero → ℝ → ℂ := fun rho v ↦
    zetaUpperBlaschkeLogDerivativeSummand
      (upperBoundaryApproachPoint x v) rho
  have hsummand : ∀ rho ∈ s, ContinuousAt (f rho) u := by
    intro rho hrho
    have hupper := (mem_spectralUpperZetaZeroWindow.mp hrho).2
    have hnorm := hgap rho hupper
    have huNorm : u < ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖ := by
      have hhalf : delta / 2 ≤
          ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖ :=
        (half_le_self hdelta.le).trans hnorm
      exact huSmall.trans_le hhalf
    have hradial : u ^ 2 < Complex.normSq
        ((x : ℂ) - zetaSpectralCoordinate rho.1) := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg
        ((x : ℂ) - zetaSpectralCoordinate rho.1)]
    have hminus : upperBoundaryApproachPoint x u ≠
        zetaSpectralCoordinate rho.1 := by
      intro heq
      have hre := congrArg Complex.re heq
      have him := congrArg Complex.im heq
      simp only [upperBoundaryApproachPoint_re,
        upperBoundaryApproachPoint_im] at hre him
      rw [Complex.normSq_apply] at hradial
      simp only [sub_re, ofReal_re, sub_im, ofReal_im] at hradial
      rw [← hre, ← him] at hradial
      nlinarith
    have hplus : upperBoundaryApproachPoint x u ≠
        starRingEnd ℂ (zetaSpectralCoordinate rho.1) := by
      intro heq
      have him := congrArg Complex.im heq
      simp only [upperBoundaryApproachPoint_im, conj_im] at him
      linarith
    exact continuousAt_zetaUpperBlaschkeLogDerivativeSummand_approach
      rho hminus hplus
  have hsumAux : ∀ q : Finset NontrivialZetaZero,
      (∀ rho ∈ q, ContinuousAt (f rho) u) →
        ContinuousAt (fun v : ℝ ↦ ∑ rho ∈ q, f rho v) u := by
    intro q hq
    induction q using Finset.induction_on with
    | empty =>
        simpa using
          (continuousAt_const : ContinuousAt (fun _v : ℝ ↦ (0 : ℂ)) u)
    | @insert rho q hrho ih =>
        have hhead := hq rho (by simp)
        have htail := ih (fun sigma hsigma ↦ hq sigma (by simp [hsigma]))
        have hadd : ContinuousAt
            (fun v : ℝ ↦ f rho v + ∑ sigma ∈ q, f sigma v) u := by
          simpa only [Pi.add_apply] using! hhead.add htail
        convert hadd using 1
        funext v
        rw [Finset.sum_insert hrho]
  have hsum : ContinuousAt (fun v : ℝ ↦ ∑ rho ∈ s, f rho v) u :=
    hsumAux s hsummand
  have hcomplex : ContinuousAt
      (fun v : ℝ ↦ -Complex.I * (∑ rho ∈ s, f rho v)) u := by
    fun_prop
  have hre : ContinuousAt
      (fun v : ℝ ↦ (-Complex.I * (∑ rho ∈ s, f rho v)).re) u :=
    Complex.continuous_re.continuousAt.comp hcomplex
  have hreal := hre.const_mul (2 : ℝ)
  simpa [s, f, riemannXiUpperBlaschkeLogDerivativeWindow] using hreal

/-- The height integral of twice the scaled finite Blaschke response is
exactly the finite vertically continued log defect. -/
theorem intervalIntegral_two_mul_re_neg_I_blaschkeLogDerivativeWindow_eq_verticalDefect
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2) (T : ℝ) :
    (∫ u : ℝ in 0..y, 2 *
      (-Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow
        (upperBoundaryApproachPoint x u) T).re) =
      riemannXiUpperVerticalLogDefectWindow x y T := by
  let g : ℝ → ℝ := fun u ↦ 2 *
    (-Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow
      (upperBoundaryApproachPoint x u) T).re
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) y,
      HasDerivAt
        (fun v : ℝ ↦ riemannXiUpperVerticalLogDefectWindow x v T)
        (g u) u := by
    intro u huIcc
    rw [Set.uIcc_of_le hy.le] at huIcc
    apply hasDerivAt_riemannXiUpperVerticalLogDefectWindow
      hdelta hgap huIcc.1 _ T
    exact huIcc.2.trans_lt hySmall
  have hcontinuous : ContinuousOn g (Set.uIcc (0 : ℝ) y) := by
    intro u huIcc
    rw [Set.uIcc_of_le hy.le] at huIcc
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_two_mul_re_neg_I_blaschkeLogDerivativeWindow_approach
      hdelta hgap huIcc.1 _ T
    exact huIcc.2.trans_lt hySmall
  have hintegrable : IntervalIntegrable g volume 0 y :=
    hcontinuous.intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hintegrable,
    riemannXiUpperVerticalLogDefectWindow_zero, sub_zero]

/-- The same height-antiderivative identity stated directly for the finite
zero-time Suzuki response. -/
theorem intervalIntegral_two_mul_re_suzukiInitialResponseWindow_eq_verticalDefect
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ u : ℝ in 0..y, 2 *
      (suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow
        0 T (upperBoundaryApproachPoint x u)).re) =
      riemannXiUpperVerticalLogDefectWindow x y T := by
  simpa only [
    suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow_zero_time hT]
    using
      (intervalIntegral_two_mul_re_neg_I_blaschkeLogDerivativeWindow_eq_verticalDefect
        hdelta hgap hy hySmall T)

/-- In the collar, the height integral of the finite Suzuki response is the
literal real hyperbolic log-defect window. -/
theorem intervalIntegral_two_mul_re_suzukiInitialResponseWindow_eq_hyperbolicRealWindow
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ u : ℝ in 0..y, 2 *
      (suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow
        0 T (upperBoundaryApproachPoint x u)).re) =
      riemannXiUpperHyperbolicLogDefectRealWindow
        (upperBoundaryApproachPoint x y) T := by
  rw [
    intervalIntegral_two_mul_re_suzukiInitialResponseWindow_eq_verticalDefect
      hdelta hgap hy hySmall hT]
  apply riemannXiUpperVerticalLogDefectWindow_eq_hyperbolicRealWindow hy
  intro rho hrho
  have hupper := (mem_spectralUpperZetaZeroWindow.mp hrho).2
  have hsep := half_boundaryGap_le_norm_upperBoundaryApproachPoint_sub
    hdelta hgap hy hySmall rho hupper
  apply sub_ne_zero.mp
  rw [← norm_pos_iff]
  exact (half_pos hdelta).trans_le hsep

/-- Extended-nonnegative form of the exact bridge: applying `ofReal` to the
height-integrated finite Suzuki response gives precisely the established
finite spectral hyperbolic log-defect window. -/
theorem ofReal_intervalIntegral_two_mul_re_suzukiInitialResponseWindow_eq_logDefectWindow
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2)
    {T : ℝ} (hT : 0 ≤ T) :
    ENNReal.ofReal
        (∫ u : ℝ in 0..y, 2 *
          (suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow
            0 T (upperBoundaryApproachPoint x u)).re) =
      riemannXiUpperHyperbolicLogDefectWindow
        (upperBoundaryApproachPoint x y) T := by
  rw [
    intervalIntegral_two_mul_re_suzukiInitialResponseWindow_eq_hyperbolicRealWindow
      hdelta hgap hy hySmall hT]
  apply ofReal_riemannXiUpperHyperbolicLogDefectRealWindow_eq
    (by simpa using hy)
  intro rho hrho
  have hupper := (mem_spectralUpperZetaZeroWindow.mp hrho).2
  have hsep := half_boundaryGap_le_norm_upperBoundaryApproachPoint_sub
    hdelta hgap hy hySmall rho hupper
  apply sub_ne_zero.mp
  rw [← norm_pos_iff]
  exact (half_pos hdelta).trans_le hsep

/-- Blaschke-logarithmic-derivative form of the exact finite bridge, valid
for every real cutoff. -/
theorem ofReal_intervalIntegral_two_mul_re_neg_I_blaschkeLogDerivativeWindow_eq_logDefectWindow
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2) (T : ℝ) :
    ENNReal.ofReal
        (∫ u : ℝ in 0..y, 2 *
          (-Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow
            (upperBoundaryApproachPoint x u) T).re) =
      riemannXiUpperHyperbolicLogDefectWindow
        (upperBoundaryApproachPoint x y) T := by
  rw [
    intervalIntegral_two_mul_re_neg_I_blaschkeLogDerivativeWindow_eq_verticalDefect
      hdelta hgap hy hySmall T,
    riemannXiUpperVerticalLogDefectWindow_eq_hyperbolicRealWindow hy]
  · apply ofReal_riemannXiUpperHyperbolicLogDefectRealWindow_eq
      (by simpa using hy)
    intro rho hrho
    have hupper := (mem_spectralUpperZetaZeroWindow.mp hrho).2
    have hsep := half_boundaryGap_le_norm_upperBoundaryApproachPoint_sub
      hdelta hgap hy hySmall rho hupper
    apply sub_ne_zero.mp
    rw [← norm_pos_iff]
    exact (half_pos hdelta).trans_le hsep
  · intro rho hrho
    have hupper := (mem_spectralUpperZetaZeroWindow.mp hrho).2
    have hsep := half_boundaryGap_le_norm_upperBoundaryApproachPoint_sub
      hdelta hgap hy hySmall rho hupper
    apply sub_ne_zero.mp
    rw [← norm_pos_iff]
    exact (half_pos hdelta).trans_le hsep

/-- The finite height-integrated Blaschke response and the finite
positive-proper-time Gaussian heat action are exactly equal. -/
theorem ofReal_intervalIntegral_two_mul_re_neg_I_blaschkeLogDerivativeWindow_eq_heatActionWindow
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2) (T : ℝ) :
    ENNReal.ofReal
        (∫ u : ℝ in 0..y, 2 *
          (-Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow
            (upperBoundaryApproachPoint x u) T).re) =
      riemannXiUpperHyperbolicHeatActionWindow
        (upperBoundaryApproachPoint x y) T := by
  rw [
    ofReal_intervalIntegral_two_mul_re_neg_I_blaschkeLogDerivativeWindow_eq_logDefectWindow
      hdelta hgap hy hySmall T]
  symm
  apply riemannXiUpperHyperbolicHeatActionWindow_eq_logDefectWindow
    (by simpa using hy)
  exact riemannXiSpectral_upperBoundaryApproachPoint_ne_zero
    hdelta hgap hy hySmall

/-- Expanding finite height-integrated Blaschke responses converge to the
complete positive-proper-time Gaussian heat action.  This is the exact point
where the Suzuki-response and Gaussian-action constructions meet. -/
theorem tendsto_ofReal_intervalIntegral_two_mul_re_neg_I_blaschkeLogDerivativeWindow_atTop_heatAction
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2) :
    Tendsto
      (fun T : ℝ ↦ ENNReal.ofReal
        (∫ u : ℝ in 0..y, 2 *
          (-Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow
            (upperBoundaryApproachPoint x u) T).re))
      atTop
      (nhds (riemannXiUpperHyperbolicHeatAction
        (upperBoundaryApproachPoint x y))) := by
  have hz : 0 < (upperBoundaryApproachPoint x y).im := by
    simpa using hy
  have hxi : riemannXiSpectral (upperBoundaryApproachPoint x y) ≠ 0 :=
    riemannXiSpectral_upperBoundaryApproachPoint_ne_zero
      hdelta hgap hy hySmall
  have heq :
      (fun T : ℝ ↦ ENNReal.ofReal
        (∫ u : ℝ in 0..y, 2 *
          (-Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow
            (upperBoundaryApproachPoint x u) T).re)) =
      fun T : ℝ ↦ riemannXiUpperHyperbolicLogDefectWindow
        (upperBoundaryApproachPoint x y) T := by
    funext T
    exact
      ofReal_intervalIntegral_two_mul_re_neg_I_blaschkeLogDerivativeWindow_eq_logDefectWindow
        hdelta hgap hy hySmall T
  rw [heq, riemannXiUpperHyperbolicHeatAction_eq_logDefectMass hz hxi]
  exact tendsto_riemannXiUpperHyperbolicLogDefectWindow
    (upperBoundaryApproachPoint x y)

/-- The same complete-action convergence stated directly for expanding
finite zero-time Suzuki-response windows. -/
theorem tendsto_ofReal_intervalIntegral_two_mul_re_suzukiInitialResponseWindow_atTop_heatAction
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2) :
    Tendsto
      (fun T : ℝ ↦ ENNReal.ofReal
        (∫ u : ℝ in 0..y, 2 *
          (suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow
            0 T (upperBoundaryApproachPoint x u)).re))
      atTop
      (nhds (riemannXiUpperHyperbolicHeatAction
        (upperBoundaryApproachPoint x y))) := by
  apply
    (tendsto_ofReal_intervalIntegral_two_mul_re_neg_I_blaschkeLogDerivativeWindow_atTop_heatAction
      hdelta hgap hy hySmall).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  simp only [
    suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow_zero_time hT]

end

end RiemannGaussian
