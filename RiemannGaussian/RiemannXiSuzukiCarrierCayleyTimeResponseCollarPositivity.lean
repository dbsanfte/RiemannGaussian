import RiemannGaussian.RiemannXiSuzukiCarrierCayleyTimeResponseRigidity

/-!
# Termwise positivity of the Suzuki initial response in a boundary collar

The uniform collar obstruction can be sharpened algebraically.  For one
selected upper spectral zero `alpha`, the real part of its scaled signed
Blaschke response at `x + i y` has numerator

`2 * alpha.im * (normSq (x - alpha) - y^2)`.

It is therefore positive whenever the approach height is smaller than the
boundary distance to that zero.  The uniform upper-divisor gap makes this
simultaneous for every genuine upper zero.  Thus real-part cancellation is
impossible throughout a sufficiently short collar, already at each finite
spectral window.
-/

open Complex Filter Set Topology
open scoped Classical ComplexConjugate Topology

namespace RiemannGaussian

noncomputable section

/-- Exact real-part formula for one multiplicity-weighted signed upper-zero
response along a vertical approach. -/
theorem re_neg_I_mul_zetaUpperBlaschkeLogDerivativeSummand_approach_eq
    (x y : ℝ) (rho : NontrivialZetaZero)
    (hradial : y ^ 2 < Complex.normSq
      ((x : ℂ) - zetaSpectralCoordinate rho.1)) :
    (-Complex.I * zetaUpperBlaschkeLogDerivativeSummand
      (upperBoundaryApproachPoint x y) rho).re =
      (analyticZetaZeroMultiplicity rho : ℝ) *
        (2 * (zetaSpectralCoordinate rho.1).im *
          (Complex.normSq
              ((x : ℂ) - zetaSpectralCoordinate rho.1) - y ^ 2) /
            (Complex.normSq
                (upperBoundaryApproachPoint x y -
                  zetaSpectralCoordinate rho.1) *
              Complex.normSq
                (upperBoundaryApproachPoint x y - starRingEnd ℂ
                  (zetaSpectralCoordinate rho.1)))) := by
  let alpha : ℂ := zetaSpectralCoordinate rho.1
  let z : ℂ := upperBoundaryApproachPoint x y
  have hza : z - alpha ≠ 0 := by
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
  have hzc : z - starRingEnd ℂ alpha ≠ 0 := by
    intro hzero
    have heq : z = starRingEnd ℂ alpha := sub_eq_zero.mp hzero
    have hre := congrArg Complex.re heq
    have him := congrArg Complex.im heq
    dsimp [z, alpha] at hre him
    simp only [upperBoundaryApproachPoint_re,
      upperBoundaryApproachPoint_im] at hre him
    rw [Complex.normSq_apply] at hradial
    simp only [sub_re, ofReal_re, sub_im, ofReal_im] at hradial
    have him' : (zetaSpectralCoordinate rho.1).im = -y := by
      linarith
    rw [← hre, him'] at hradial
    nlinarith
  have hdiff :
      1 / (z - alpha) - 1 / (z - starRingEnd ℂ alpha) =
        (alpha - starRingEnd ℂ alpha) /
          ((z - alpha) * (z - starRingEnd ℂ alpha)) := by
    field_simp [hza, hzc]
    ring
  have hnum :
      alpha - starRingEnd ℂ alpha =
        ((2 * alpha.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp
    · simp
      ring
  have hdenRe :
      ((z - alpha) * (z - starRingEnd ℂ alpha)).re =
        Complex.normSq ((x : ℂ) - alpha) - y ^ 2 := by
    dsimp [z]
    unfold upperBoundaryApproachPoint Complex.normSq
    simp
    ring
  have hdenNorm :
      Complex.normSq ((z - alpha) * (z - starRingEnd ℂ alpha)) =
        Complex.normSq (z - alpha) *
          Complex.normSq (z - starRingEnd ℂ alpha) := by
    exact map_mul Complex.normSq _ _
  unfold zetaUpperBlaschkeLogDerivativeSummand
  change
    (-Complex.I * ((analyticZetaZeroMultiplicity rho : ℂ) *
      (1 / (z - alpha) - 1 / (z - starRingEnd ℂ alpha)))).re = _
  rw [hdiff, hnum]
  have hrearrange :
      -Complex.I * ((analyticZetaZeroMultiplicity rho : ℂ) *
        (((2 * alpha.im : ℝ) : ℂ) * Complex.I /
          ((z - alpha) * (z - starRingEnd ℂ alpha)))) =
        (((analyticZetaZeroMultiplicity rho : ℝ) *
          (2 * alpha.im) : ℝ) : ℂ) /
            ((z - alpha) * (z - starRingEnd ℂ alpha)) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    push_cast
    calc
      -Complex.I * ((analyticZetaZeroMultiplicity rho : ℂ) *
            (2 * (alpha.im : ℂ) * Complex.I *
              ((z - alpha) * (z - starRingEnd ℂ alpha))⁻¹)) =
          ((analyticZetaZeroMultiplicity rho : ℂ) *
            (2 * (alpha.im : ℂ))) *
              (-(Complex.I * Complex.I)) *
                ((z - alpha) * (z - starRingEnd ℂ alpha))⁻¹ := by ring
      _ = (analyticZetaZeroMultiplicity rho : ℂ) *
            (2 * (alpha.im : ℂ)) *
              ((z - alpha) * (z - starRingEnd ℂ alpha))⁻¹ := by
        rw [Complex.I_mul_I]
        ring
  rw [hrearrange, Complex.div_re, hdenRe, hdenNorm]
  simp only [ofReal_re, ofReal_im, zero_mul]
  dsimp [alpha, z]
  ring

/-- Every selected upper-zero summand has strictly positive scaled real part
throughout a collar shorter than half a uniform boundary gap. -/
theorem re_neg_I_mul_zetaUpperBlaschkeSelectedLogDerivativeSummand_approach_pos
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2)
    (rho : NontrivialZetaZero)
    (hupper : 0 < (zetaSpectralCoordinate rho.1).im) :
    0 < (-Complex.I *
      zetaUpperBlaschkeSelectedLogDerivativeSummand
        (upperBoundaryApproachPoint x y) rho).re := by
  let alpha : ℂ := zetaSpectralCoordinate rho.1
  let z : ℂ := upperBoundaryApproachPoint x y
  have hr : 0 < ‖(x : ℂ) - alpha‖ :=
    hdelta.trans_le (hgap rho hupper)
  have hyr : y < ‖(x : ℂ) - alpha‖ := by
    have hhalf : delta / 2 ≤ ‖(x : ℂ) - alpha‖ := by
      exact (half_le_self hdelta.le).trans (hgap rho hupper)
    exact hySmall.trans_le hhalf
  have hradial : y ^ 2 < Complex.normSq ((x : ℂ) - alpha) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith
  have hfirst : 0 < Complex.normSq (z - alpha) := by
    apply Complex.normSq_pos.mpr
    rw [← norm_pos_iff]
    have hsep := half_boundaryGap_le_norm_upperBoundaryApproachPoint_sub
      hdelta hgap hy hySmall rho hupper
    exact (half_pos hdelta).trans_le hsep
  have hsecond : 0 < Complex.normSq (z - starRingEnd ℂ alpha) := by
    apply Complex.normSq_pos.mpr
    exact sub_conj_ne_zero_of_im_pos (by simpa [z] using hy) hupper
  rw [zetaUpperBlaschkeSelectedLogDerivativeSummand, if_pos hupper,
    re_neg_I_mul_zetaUpperBlaschkeLogDerivativeSummand_approach_eq
      x y rho hradial]
  have hradialPos :
      0 < Complex.normSq ((x : ℂ) - alpha) - y ^ 2 := by
    linarith
  change 0 <
    (analyticZetaZeroMultiplicity rho : ℝ) *
      (2 * alpha.im *
        (Complex.normSq ((x : ℂ) - alpha) - y ^ 2) /
          (Complex.normSq (z - alpha) *
            Complex.normSq (z - starRingEnd ℂ alpha)))
  have hm : 0 < (analyticZetaZeroMultiplicity rho : ℝ) := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  exact mul_pos hm
    (div_pos (mul_pos (mul_pos (by norm_num) hupper) hradialPos)
      (mul_pos hfirst hsecond))

/-- The same strict positivity stated for the unselected upper-zero summand
used by each finite Blaschke window. -/
theorem re_neg_I_mul_zetaUpperBlaschkeLogDerivativeSummand_approach_pos
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2)
    (rho : NontrivialZetaZero)
    (hupper : 0 < (zetaSpectralCoordinate rho.1).im) :
    0 < (-Complex.I * zetaUpperBlaschkeLogDerivativeSummand
      (upperBoundaryApproachPoint x y) rho).re := by
  have hpositive :=
    re_neg_I_mul_zetaUpperBlaschkeSelectedLogDerivativeSummand_approach_pos
      hdelta hgap hy hySmall rho hupper
  rw [zetaUpperBlaschkeSelectedLogDerivativeSummand,
    if_pos hupper] at hpositive
  exact hpositive

/-- Without selecting an upper zero explicitly, every selected summand has
nonnegative scaled real part throughout the same collar. -/
theorem re_neg_I_mul_zetaUpperBlaschkeSelectedLogDerivativeSummand_approach_nonneg
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2)
    (rho : NontrivialZetaZero) :
    0 ≤ (-Complex.I *
      zetaUpperBlaschkeSelectedLogDerivativeSummand
        (upperBoundaryApproachPoint x y) rho).re := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · exact
      (re_neg_I_mul_zetaUpperBlaschkeSelectedLogDerivativeSummand_approach_pos
        hdelta hgap hy hySmall rho hupper).le
  · rw [zetaUpperBlaschkeSelectedLogDerivativeSummand, if_neg hupper,
      mul_zero, zero_re]

/-- Every finite signed Suzuki initial-velocity window has nonnegative real
part throughout a sufficiently short boundary collar.  No late-cutoff limit
is needed for this statement. -/
theorem suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow_zero_time_re_nonneg
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2)
    {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ (suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow
      0 T (upperBoundaryApproachPoint x y)).re := by
  rw [suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow_zero_time
    hT]
  unfold riemannXiUpperBlaschkeLogDerivativeWindow
  rw [Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_nonneg
  intro rho hrho
  have hupper := (mem_spectralUpperZetaZeroWindow.mp hrho).2
  exact
    (re_neg_I_mul_zetaUpperBlaschkeLogDerivativeSummand_approach_pos
      hdelta hgap hy hySmall rho hupper).le

/-- Once a genuine window contains one upper zero, its finite signed Suzuki
initial velocity has strictly positive real part everywhere in the collar. -/
theorem suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow_zero_time_re_pos_of_upper_zero
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2)
    (rho : NontrivialZetaZero)
    (hupper : 0 < (zetaSpectralCoordinate rho.1).im)
    {T : ℝ} (hT : |(zetaSpectralCoordinate rho.1).re| ≤ T) :
    0 < (suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow
      0 T (upperBoundaryApproachPoint x y)).re := by
  have hTnonneg : 0 ≤ T :=
    (abs_nonneg (zetaSpectralCoordinate rho.1).re).trans hT
  rw [suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow_zero_time
    hTnonneg]
  unfold riemannXiUpperBlaschkeLogDerivativeWindow
  rw [Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_pos'
  · intro sigma hsigma
    have hsigmaUpper := (mem_spectralUpperZetaZeroWindow.mp hsigma).2
    exact
      (re_neg_I_mul_zetaUpperBlaschkeLogDerivativeSummand_approach_pos
        hdelta hgap hy hySmall sigma hsigmaUpper).le
  · refine ⟨rho, ?_,
      re_neg_I_mul_zetaUpperBlaschkeLogDerivativeSummand_approach_pos
        hdelta hgap hy hySmall rho hupper⟩
    apply mem_spectralUpperZetaZeroWindow.mpr
    exact ⟨(mem_spectralZetaZeroWindow hTnonneg rho).mpr hT, hupper⟩

/-- In the gap collar, the real part of a finite signed Suzuki initial
velocity vanishes exactly when its upper spectral window is empty. -/
theorem suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow_zero_time_re_eq_zero_iff
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2)
    {T : ℝ} (hT : 0 ≤ T) :
    (suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow
        0 T (upperBoundaryApproachPoint x y)).re = 0 ↔
      spectralUpperZetaZeroWindow T = ∅ := by
  rw [suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow_zero_time
    hT]
  unfold riemannXiUpperBlaschkeLogDerivativeWindow
  rw [Finset.mul_sum, Complex.re_sum]
  have hnonneg : ∀ rho ∈ spectralUpperZetaZeroWindow T,
      0 ≤ (-Complex.I * zetaUpperBlaschkeLogDerivativeSummand
        (upperBoundaryApproachPoint x y) rho).re := by
    intro rho hrho
    have hupper := (mem_spectralUpperZetaZeroWindow.mp hrho).2
    exact
      (re_neg_I_mul_zetaUpperBlaschkeLogDerivativeSummand_approach_pos
        hdelta hgap hy hySmall rho hupper).le
  constructor
  · intro hsum
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro rho hrho
    have hzero :=
      (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum rho hrho
    have hupper := (mem_spectralUpperZetaZeroWindow.mp hrho).2
    exact
      (ne_of_gt
        (re_neg_I_mul_zetaUpperBlaschkeLogDerivativeSummand_approach_pos
          hdelta hgap hy hySmall rho hupper)) hzero
  · intro hempty
    rw [hempty]
    simp

/-- In the same collar, every nonnegative exact xi reflection-residual window
has nonnegative scaled real part. -/
theorem re_neg_I_mul_riemannXiUpperSpectralReflectionResidual_nonneg
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2)
    {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ (-Complex.I * riemannXiUpperSpectralReflectionResidual
      (upperBoundaryApproachPoint x y) T).re := by
  have hxi : riemannXiSpectral
      (upperBoundaryApproachPoint x y) ≠ 0 :=
    riemannXiSpectral_upperBoundaryApproachPoint_ne_zero
      hdelta hgap hy hySmall
  have hz : 0 < (upperBoundaryApproachPoint x y).im := by
    simpa using hy
  have hresponse :=
    suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow_zero_time_re_nonneg
      hdelta hgap hy hySmall hT
  rw [
    suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow_zero_time_eq_reflectionResidual
      hz hxi hT] at hresponse
  exact hresponse

/-- Once the window contains one upper zero, the exact xi reflection residual
has strictly positive scaled real part everywhere in the collar. -/
theorem re_neg_I_mul_riemannXiUpperSpectralReflectionResidual_pos_of_upper_zero
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2)
    (rho : NontrivialZetaZero)
    (hupper : 0 < (zetaSpectralCoordinate rho.1).im)
    {T : ℝ} (hT : |(zetaSpectralCoordinate rho.1).re| ≤ T) :
    0 < (-Complex.I * riemannXiUpperSpectralReflectionResidual
      (upperBoundaryApproachPoint x y) T).re := by
  have hTnonneg : 0 ≤ T :=
    (abs_nonneg (zetaSpectralCoordinate rho.1).re).trans hT
  have hxi : riemannXiSpectral
      (upperBoundaryApproachPoint x y) ≠ 0 :=
    riemannXiSpectral_upperBoundaryApproachPoint_ne_zero
      hdelta hgap hy hySmall
  have hz : 0 < (upperBoundaryApproachPoint x y).im := by
    simpa using hy
  have hresponse :=
    suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow_zero_time_re_pos_of_upper_zero
      hdelta hgap hy hySmall rho hupper hT
  rw [
    suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow_zero_time_eq_reflectionResidual
      hz hxi hTnonneg] at hresponse
  exact hresponse

/-- In the gap collar, an exact finite spectral-xi reflection residual is
zero exactly when its genuine upper spectral window is empty.  Thus there is
no possible complex cancellation masking an upper zero in this region. -/
theorem riemannXiUpperSpectralReflectionResidual_eq_zero_iff_upperWindow_empty
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2)
    {T : ℝ} (hT : 0 ≤ T) :
    riemannXiUpperSpectralReflectionResidual
        (upperBoundaryApproachPoint x y) T = 0 ↔
      spectralUpperZetaZeroWindow T = ∅ := by
  have hxi : riemannXiSpectral
      (upperBoundaryApproachPoint x y) ≠ 0 :=
    riemannXiSpectral_upperBoundaryApproachPoint_ne_zero
      hdelta hgap hy hySmall
  have hz : 0 < (upperBoundaryApproachPoint x y).im := by
    simpa using hy
  constructor
  · intro hzero
    apply
      (suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow_zero_time_re_eq_zero_iff
        hdelta hgap hy hySmall hT).mp
    rw [
      suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow_zero_time_eq_reflectionResidual
        hz hxi hT,
      hzero, mul_zero, zero_re]
  · intro hempty
    rw [riemannXiUpperSpectralReflectionResidual_eq_logDerivativeWindow
      hz hxi hT]
    unfold riemannXiUpperBlaschkeLogDerivativeWindow
    rw [hempty]
    simp

end

end RiemannGaussian
