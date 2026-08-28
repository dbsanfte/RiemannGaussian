import RiemannGaussian.RiemannXiSuzukiSpectralStaticContourBoundaryRecovery
import RiemannGaussian.RiemannXiSuzukiCarrierCayleyTimeResponseLogDefectComplete

/-!
# Safe-axis transport from the static detector to positive log defect

The static contour recovers the complete Blaschke logarithmic derivative at
safe imaginary observation points.  This module begins the coercive transport
of that response.  Along the ray `z = i y`, `y > 1`, the real part of the
scaled Blaschke response is the exact height derivative of the
pseudo-hyperbolic logarithmic defect, with no small-collar assumption.

For every finite genuine spectral window, integrating the negative response
from height `1` to infinity recovers its positive logarithmic defect at `i`.
The expanding windows then exhaust the complete RH-equivalent log-defect
mass.  All limit orders remain explicit: no interchange of the spectral
cutoff and the infinite height integral is assumed.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Exact safe-axis real-part formula for one multiplicity-weighted Blaschke
summand.  Unlike the collar-positivity formula, this identity is valid at
every height strictly above `1`; its numerator may have either sign. -/
theorem re_neg_I_mul_zetaUpperBlaschkeLogDerivativeSummand_safeAxis_eq
    {y : ℝ} (hy : 1 ≤ y) (rho : NontrivialZetaZero) :
    (-Complex.I * zetaUpperBlaschkeLogDerivativeSummand
      (upperBoundaryApproachPoint 0 y) rho).re =
      (analyticZetaZeroMultiplicity rho : ℝ) *
        (2 * (zetaSpectralCoordinate rho.1).im *
          (Complex.normSq
              ((0 : ℂ) - zetaSpectralCoordinate rho.1) - y ^ 2) /
            (Complex.normSq
                (upperBoundaryApproachPoint 0 y -
                  zetaSpectralCoordinate rho.1) *
              Complex.normSq
                (upperBoundaryApproachPoint 0 y - starRingEnd ℂ
                  (zetaSpectralCoordinate rho.1)))) := by
  let alpha : ℂ := zetaSpectralCoordinate rho.1
  let z : ℂ := upperBoundaryApproachPoint 0 y
  have habs := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
  have hySub : 0 < y - alpha.im := by
    dsimp [alpha]
    nlinarith [le_abs_self (zetaSpectralCoordinate rho.1).im]
  have hyAdd : 0 < y + alpha.im := by
    dsimp [alpha]
    nlinarith [neg_le_abs (zetaSpectralCoordinate rho.1).im]
  have hza : z - alpha ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    dsimp [z] at him
    simp only [upperBoundaryApproachPoint_im] at him
    linarith
  have hzc : z - starRingEnd ℂ alpha ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    dsimp [z] at him
    simp only [upperBoundaryApproachPoint_im] at him
    linarith
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
        Complex.normSq ((0 : ℂ) - alpha) - y ^ 2 := by
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

/-- On the safe imaginary axis, the derivative of one raw vertical log
defect is exactly twice the real part of its scaled Blaschke response. -/
theorem hasDerivAt_zetaUpperVerticalLogDefectSummand_safeAxis
    {y : ℝ} (hy : 1 ≤ y) (rho : NontrivialZetaZero) :
    HasDerivAt
      (fun v : ℝ ↦ zetaUpperVerticalLogDefectSummand 0 v rho)
      (2 * (-Complex.I * zetaUpperBlaschkeLogDerivativeSummand
        (upperBoundaryApproachPoint 0 y) rho).re) y := by
  let alpha : ℂ := zetaSpectralCoordinate rho.1
  let z : ℂ := upperBoundaryApproachPoint 0 y
  have habs := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
  have hySub : 0 < y - alpha.im := by
    dsimp [alpha]
    nlinarith [le_abs_self (zetaSpectralCoordinate rho.1).im]
  have hyAdd : 0 < y + alpha.im := by
    dsimp [alpha]
    nlinarith [neg_le_abs (zetaSpectralCoordinate rho.1).im]
  have hminus : Complex.normSq (z - alpha) ≠ 0 := by
    exact (Complex.normSq_pos.mpr (by
      intro hzero
      have him := congrArg Complex.im hzero
      dsimp [z] at him
      simp only [upperBoundaryApproachPoint_im] at him
      linarith)).ne'
  have hplus : Complex.normSq (z - starRingEnd ℂ alpha) ≠ 0 := by
    exact (Complex.normSq_pos.mpr (by
      intro hzero
      have him := congrArg Complex.im hzero
      dsimp [z] at him
      simp only [upperBoundaryApproachPoint_im] at him
      linarith)).ne'
  have hbase := hasDerivAt_upperHalfPlaneVerticalLogDefect
    0 y alpha hminus hplus
  have hminusEq : Complex.normSq (z - alpha) =
      Complex.normSq ((0 : ℂ) - alpha) + y ^ 2 - 2 * y * alpha.im := by
    exact normSq_upperBoundaryApproachPoint_sub 0 y alpha
  have hplusEq : Complex.normSq (z - starRingEnd ℂ alpha) =
      Complex.normSq ((0 : ℂ) - alpha) + y ^ 2 + 2 * y * alpha.im := by
    exact normSq_upperBoundaryApproachPoint_sub_conj 0 y alpha
  unfold zetaUpperVerticalLogDefectSummand
  apply (hbase.const_mul
    (analyticZetaZeroMultiplicity rho : ℝ)).congr_deriv
  rw [re_neg_I_mul_zetaUpperBlaschkeLogDerivativeSummand_safeAxis_eq
    hy]
  change
    (analyticZetaZeroMultiplicity rho : ℝ) *
        ((2 * y + 2 * alpha.im) /
            Complex.normSq (z - starRingEnd ℂ alpha) -
          (2 * y - 2 * alpha.im) /
            Complex.normSq (z - alpha)) =
      2 * ((analyticZetaZeroMultiplicity rho : ℝ) *
        (2 * alpha.im *
          (Complex.normSq ((0 : ℂ) - alpha) - y ^ 2) /
            (Complex.normSq (z - alpha) *
              Complex.normSq (z - starRingEnd ℂ alpha))))
  field_simp [hminus, hplus]
  rw [hminusEq, hplusEq]
  ring

/-- At every safe height, the derivative of a finite vertical log-defect
window is exactly twice the real part of its finite Blaschke response. -/
theorem hasDerivAt_riemannXiUpperVerticalLogDefectWindow_safeAxis
    {y : ℝ} (hy : 1 ≤ y) (T : ℝ) :
    HasDerivAt
      (fun v : ℝ ↦ riemannXiUpperVerticalLogDefectWindow 0 v T)
      (2 * (-Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow
        (upperBoundaryApproachPoint 0 y) T).re) y := by
  unfold riemannXiUpperVerticalLogDefectWindow
  have hsum : HasDerivAt
      (fun v : ℝ ↦ ∑ rho ∈ spectralUpperZetaZeroWindow T,
        zetaUpperVerticalLogDefectSummand 0 v rho)
      (∑ rho ∈ spectralUpperZetaZeroWindow T,
        2 * (-Complex.I * zetaUpperBlaschkeLogDerivativeSummand
          (upperBoundaryApproachPoint 0 y) rho).re) y := by
    apply HasDerivAt.fun_sum
    intro rho _hrho
    exact hasDerivAt_zetaUpperVerticalLogDefectSummand_safeAxis hy rho
  apply hsum.congr_deriv
  unfold riemannXiUpperBlaschkeLogDerivativeWindow
  rw [Finset.mul_sum, Complex.re_sum]
  simp only [mul_re, neg_re, I_re, neg_im, I_im]
  rw [Finset.mul_sum]

/-- The scaled finite Blaschke response is continuous at every safe-axis
height. -/
theorem continuousAt_two_mul_re_neg_I_blaschkeLogDerivativeWindow_safeAxis
    {y : ℝ} (hy : 1 ≤ y) (T : ℝ) :
    ContinuousAt
      (fun v : ℝ ↦ 2 *
        (-Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow
          (upperBoundaryApproachPoint 0 v) T).re) y := by
  let s : Finset NontrivialZetaZero := spectralUpperZetaZeroWindow T
  let f : NontrivialZetaZero → ℝ → ℂ := fun rho v ↦
    zetaUpperBlaschkeLogDerivativeSummand
      (upperBoundaryApproachPoint 0 v) rho
  have hsummand : ∀ rho ∈ s, ContinuousAt (f rho) y := by
    intro rho _hrho
    let alpha : ℂ := zetaSpectralCoordinate rho.1
    have habs := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
    have hySub : 0 < y - alpha.im := by
      dsimp [alpha]
      nlinarith [le_abs_self (zetaSpectralCoordinate rho.1).im]
    have hyAdd : 0 < y + alpha.im := by
      dsimp [alpha]
      nlinarith [neg_le_abs (zetaSpectralCoordinate rho.1).im]
    have hminus : upperBoundaryApproachPoint 0 y ≠ alpha := by
      intro heq
      have him := congrArg Complex.im heq
      simp only [upperBoundaryApproachPoint_im] at him
      linarith
    have hplus : upperBoundaryApproachPoint 0 y ≠
        starRingEnd ℂ alpha := by
      intro heq
      have him := congrArg Complex.im heq
      simp only [upperBoundaryApproachPoint_im, conj_im] at him
      linarith
    exact continuousAt_zetaUpperBlaschkeLogDerivativeSummand_approach
      rho hminus hplus
  have hsumAux : ∀ q : Finset NontrivialZetaZero,
      (∀ rho ∈ q, ContinuousAt (f rho) y) →
        ContinuousAt (fun v : ℝ ↦ ∑ rho ∈ q, f rho v) y := by
    intro q hq
    induction q using Finset.induction_on with
    | empty =>
        simpa using
          (continuousAt_const : ContinuousAt (fun _v : ℝ ↦ (0 : ℂ)) y)
    | @insert rho q hrho ih =>
        have hhead := hq rho (by simp)
        have htail := ih (fun sigma hsigma ↦ hq sigma (by simp [hsigma]))
        have hadd : ContinuousAt
            (fun v : ℝ ↦ f rho v + ∑ sigma ∈ q, f sigma v) y := by
          simpa only [Pi.add_apply] using! hhead.add htail
        convert hadd using 1
        funext v
        rw [Finset.sum_insert hrho]
  have hsum : ContinuousAt (fun v : ℝ ↦ ∑ rho ∈ s, f rho v) y :=
    hsumAux s hsummand
  have hcomplex : ContinuousAt
      (fun v : ℝ ↦ -Complex.I * (∑ rho ∈ s, f rho v)) y := by
    fun_prop
  have hre : ContinuousAt
      (fun v : ℝ ↦ (-Complex.I * (∑ rho ∈ s, f rho v)).re) y :=
    Complex.continuous_re.continuousAt.comp hcomplex
  have hreal := hre.const_mul (2 : ℝ)
  simpa [s, f, riemannXiUpperBlaschkeLogDerivativeWindow] using hreal

/-- On every finite safe-axis segment, the height integral of the finite
Blaschke response is the exact change in the finite vertical log defect. -/
theorem intervalIntegral_two_mul_re_neg_I_blaschkeLogDerivativeWindow_safeAxis
    {R : ℝ} (hR : 1 ≤ R) (T : ℝ) :
    (∫ y : ℝ in 1..R, 2 *
      (-Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow
        (upperBoundaryApproachPoint 0 y) T).re) =
      riemannXiUpperVerticalLogDefectWindow 0 R T -
        riemannXiUpperVerticalLogDefectWindow 0 1 T := by
  let g : ℝ → ℝ := fun y ↦ 2 *
    (-Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow
      (upperBoundaryApproachPoint 0 y) T).re
  have hderiv : ∀ y ∈ uIcc (1 : ℝ) R,
      HasDerivAt
        (fun v : ℝ ↦ riemannXiUpperVerticalLogDefectWindow 0 v T)
        (g y) y := by
    intro y hy
    rw [uIcc_of_le hR] at hy
    exact hasDerivAt_riemannXiUpperVerticalLogDefectWindow_safeAxis
      hy.1 T
  have hcontinuous : ContinuousOn g (uIcc (1 : ℝ) R) := by
    intro y hy
    rw [uIcc_of_le hR] at hy
    exact
      (continuousAt_two_mul_re_neg_I_blaschkeLogDerivativeWindow_safeAxis
        hy.1 T).continuousWithinAt
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hcontinuous.intervalIntegrable

/-- Reversing the sign exposes the positive finite log defect at height `1`,
up to the still-visible endpoint defect at height `R`. -/
theorem intervalIntegral_neg_two_mul_re_neg_I_blaschkeLogDerivativeWindow_safeAxis
    {R : ℝ} (hR : 1 ≤ R) (T : ℝ) :
    (∫ y : ℝ in 1..R, -2 *
      (-Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow
        (upperBoundaryApproachPoint 0 y) T).re) =
      riemannXiUpperVerticalLogDefectWindow 0 1 T -
        riemannXiUpperVerticalLogDefectWindow 0 R T := by
  have hbase :=
    intervalIntegral_two_mul_re_neg_I_blaschkeLogDerivativeWindow_safeAxis
      hR T
  calc
    (∫ y : ℝ in 1..R, -2 *
        (-Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow
          (upperBoundaryApproachPoint 0 y) T).re) =
        -(∫ y : ℝ in 1..R, 2 *
          (-Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow
            (upperBoundaryApproachPoint 0 y) T).re) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro y _hy
      ring
    _ = _ := by rw [hbase]; ring

/-- The vertical logarithmic defect of one fixed upper-half-plane parameter
vanishes as the imaginary observation height tends to infinity. -/
theorem tendsto_upperHalfPlaneVerticalLogDefect_safeAxis_atTop_zero
    (alpha : ℂ) :
    Tendsto (fun y : ℝ ↦ upperHalfPlaneVerticalLogDefect 0 y alpha)
      atTop (nhds 0) := by
  let D : ℝ := Complex.normSq ((0 : ℂ) - alpha)
  let h : ℝ := alpha.im
  have hyTop : Tendsto (fun y : ℝ ↦ y) atTop atTop := tendsto_id
  have hySqTop : Tendsto (fun y : ℝ ↦ y ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  have hD : Tendsto (fun y : ℝ ↦ D / y ^ 2) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hySqTop
  have hh : Tendsto (fun y : ℝ ↦ (2 * h) / y) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hyTop
  have hnum : Tendsto
      (fun y : ℝ ↦ D / y ^ 2 + 1 + (2 * h) / y)
      atTop (nhds 1) := by
    simpa using (hD.add tendsto_const_nhds).add hh
  have hden : Tendsto
      (fun y : ℝ ↦ D / y ^ 2 + 1 - (2 * h) / y)
      atTop (nhds 1) := by
    simpa using (hD.add tendsto_const_nhds).sub hh
  have hratio : Tendsto
      (fun y : ℝ ↦
        (D / y ^ 2 + 1 + (2 * h) / y) /
          (D / y ^ 2 + 1 - (2 * h) / y))
      atTop (nhds 1) := by
    convert hnum.div hden (by norm_num) using 1
    · ext y
      rfl
    · norm_num
  have hlog : Tendsto
      (fun y : ℝ ↦ Real.log
        ((D / y ^ 2 + 1 + (2 * h) / y) /
          (D / y ^ 2 + 1 - (2 * h) / y)))
      atTop (nhds 0) := by
    simpa using hratio.log (by norm_num)
  apply hlog.congr'
  filter_upwards [eventually_ge_atTop (|h| + 1)] with y hy
  have hyPos : 0 < y := by
    have habs : 0 ≤ |h| := abs_nonneg h
    linarith
  have hySub : 0 < y - alpha.im := by
    dsimp [h] at hy
    nlinarith [le_abs_self alpha.im]
  have hyAdd : 0 < y + alpha.im := by
    dsimp [h] at hy
    nlinarith [neg_le_abs alpha.im]
  have hminus : 0 < Complex.normSq
      (upperBoundaryApproachPoint 0 y - alpha) := by
    apply Complex.normSq_pos.mpr
    intro heq
    have him := congrArg Complex.im heq
    have him' : y - alpha.im = 0 := by simpa using him
    linarith
  have hplus : 0 < Complex.normSq
      (upperBoundaryApproachPoint 0 y - starRingEnd ℂ alpha) := by
    apply Complex.normSq_pos.mpr
    intro heq
    have him := congrArg Complex.im heq
    have him' : y + alpha.im = 0 := by simpa using him
    linarith
  unfold upperHalfPlaneVerticalLogDefect
  rw [← Real.log_div hplus.ne' hminus.ne']
  congr 1
  rw [normSq_upperBoundaryApproachPoint_sub_conj,
    normSq_upperBoundaryApproachPoint_sub]
  dsimp [D, h]
  field_simp [hyPos.ne']

/-- Every fixed finite upper spectral window has vanishing vertical defect
at infinite safe-axis height. -/
theorem tendsto_riemannXiUpperVerticalLogDefectWindow_safeAxis_atTop_zero
    (T : ℝ) :
    Tendsto (fun y : ℝ ↦ riemannXiUpperVerticalLogDefectWindow 0 y T)
      atTop (nhds 0) := by
  unfold riemannXiUpperVerticalLogDefectWindow
    zetaUpperVerticalLogDefectSummand
  simpa using tendsto_finsetSum (spectralUpperZetaZeroWindow T)
    (fun rho _hrho ↦
      (tendsto_upperHalfPlaneVerticalLogDefect_safeAxis_atTop_zero
        (zetaSpectralCoordinate rho.1)).const_mul
          (analyticZetaZeroMultiplicity rho : ℝ))

/-- For each fixed finite spectral window, the improper integral of the
negative safe-axis Blaschke response exists and equals the window's vertical
log defect at height `1`. -/
theorem
    tendsto_intervalIntegral_neg_two_mul_re_neg_I_blaschkeLogDerivativeWindow_safeAxis
    (T : ℝ) :
    Tendsto
      (fun R : ℝ ↦ ∫ y : ℝ in 1..R, -2 *
        (-Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow
          (upperBoundaryApproachPoint 0 y) T).re)
      atTop
      (nhds (riemannXiUpperVerticalLogDefectWindow 0 1 T)) := by
  have hlimit : Tendsto
      (fun R : ℝ ↦ riemannXiUpperVerticalLogDefectWindow 0 1 T -
        riemannXiUpperVerticalLogDefectWindow 0 R T)
      atTop (nhds (riemannXiUpperVerticalLogDefectWindow 0 1 T)) := by
    simpa using tendsto_const_nhds.sub
      (tendsto_riemannXiUpperVerticalLogDefectWindow_safeAxis_atTop_zero T)
  apply hlimit.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  exact
    (intervalIntegral_neg_two_mul_re_neg_I_blaschkeLogDerivativeWindow_safeAxis
      hR T).symm

/-- The safe observation point `i` cannot collide with a genuine spectral
zeta zero, because every such zero lies strictly inside `|Im z| < 1/2`. -/
theorem I_ne_zetaSpectralCoordinate (rho : NontrivialZetaZero) :
    Complex.I ≠ zetaSpectralCoordinate rho.1 := by
  intro heq
  have habs := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
  rw [← heq] at habs
  norm_num at habs

/-- At height `1`, the finite vertical defect is exactly the existing real
pseudo-hyperbolic log-defect window at the safe point `i`. -/
theorem riemannXiUpperVerticalLogDefectWindow_zero_one_eq_hyperbolicRealWindow_I
    (T : ℝ) :
    riemannXiUpperVerticalLogDefectWindow 0 1 T =
      riemannXiUpperHyperbolicLogDefectRealWindow Complex.I T := by
  have hbase :=
    riemannXiUpperVerticalLogDefectWindow_eq_hyperbolicRealWindow
      (x := 0) (y := 1) (T := T) (by norm_num)
      (fun rho _hrho ↦ by
        simpa [upperBoundaryApproachPoint] using
          I_ne_zetaSpectralCoordinate rho)
  simpa [upperBoundaryApproachPoint] using hbase

/-- Every finite height-`1` safe-axis defect is nonnegative. -/
theorem riemannXiUpperVerticalLogDefectWindow_zero_one_nonneg (T : ℝ) :
    0 ≤ riemannXiUpperVerticalLogDefectWindow 0 1 T := by
  rw [
    riemannXiUpperVerticalLogDefectWindow_zero_one_eq_hyperbolicRealWindow_I]
  unfold riemannXiUpperHyperbolicLogDefectRealWindow
  apply Finset.sum_nonneg
  intro rho _hrho
  exact zetaUpperHyperbolicLogDefectSummand_nonneg
    (by norm_num) rho (I_ne_zetaSpectralCoordinate rho)

/-- Taking `ofReal` of the height-`1` finite vertical defect recovers the
positive extended-nonnegative hyperbolic defect window at `i`. -/
theorem ofReal_riemannXiUpperVerticalLogDefectWindow_zero_one_eq
    (T : ℝ) :
    ENNReal.ofReal (riemannXiUpperVerticalLogDefectWindow 0 1 T) =
      riemannXiUpperHyperbolicLogDefectWindow Complex.I T := by
  rw [
    riemannXiUpperVerticalLogDefectWindow_zero_one_eq_hyperbolicRealWindow_I]
  exact ofReal_riemannXiUpperHyperbolicLogDefectRealWindow_eq
    (by norm_num) (fun rho _hrho ↦ I_ne_zetaSpectralCoordinate rho)

/-- Along the canonical quantitative cutoffs, the positive values recovered
from the finite safe-axis improper integrals exhaust the complete
hyperbolic log-defect mass at `i`.  This is the outer spectral-window limit;
the inner infinite-height limit remains the preceding separate theorem. -/
theorem
    tendsto_ofReal_riemannXiUpperVerticalLogDefectWindow_zero_one_quantitative_complete
    :
    Tendsto
      (fun n : ℕ ↦ ENNReal.ofReal
        (riemannXiUpperVerticalLogDefectWindow 0 1
          (quantitativeSpectralBoundaryTruncation n)))
      atTop
      (nhds (riemannXiUpperHyperbolicLogDefectMass Complex.I)) := by
  have hlimit :=
    (tendsto_riemannXiUpperHyperbolicLogDefectWindow Complex.I).comp
      tendsto_quantitativeSpectralBoundaryTruncation_atTop
  apply hlimit.congr'
  exact Eventually.of_forall fun n ↦
    (ofReal_riemannXiUpperVerticalLogDefectWindow_zero_one_eq
      (quantitativeSpectralBoundaryTruncation n)).symm

/-- Spectral xi is nonzero at the fixed safe observation point `i`. -/
theorem riemannXiSpectral_I_ne_zero :
    riemannXiSpectral Complex.I ≠ 0 := by
  apply riemannXiSpectral_ne_zero_of_half_le_abs_im
  norm_num

/-- The complete safe-axis transport target at `i` is finite. -/
theorem riemannXiUpperHyperbolicLogDefectMass_I_ne_top :
    riemannXiUpperHyperbolicLogDefectMass Complex.I ≠ ∞ := by
  exact riemannXiUpperHyperbolicLogDefectMass_ne_top
    (by norm_num) riemannXiSpectral_I_ne_zero

/-- The finite real values recovered by the inner improper integrals
converge, along the quantitative spectral cutoffs, to the real value of the
complete log-defect mass at `i`. -/
theorem
    tendsto_riemannXiUpperVerticalLogDefectWindow_zero_one_quantitative_complete_toReal
    :
    Tendsto
      (fun n : ℕ ↦ riemannXiUpperVerticalLogDefectWindow 0 1
        (quantitativeSpectralBoundaryTruncation n))
      atTop
      (nhds
        (riemannXiUpperHyperbolicLogDefectMass Complex.I).toReal) := by
  have hlimit :=
    (ENNReal.tendsto_toReal
      riemannXiUpperHyperbolicLogDefectMass_I_ne_top).comp
        tendsto_ofReal_riemannXiUpperVerticalLogDefectWindow_zero_one_quantitative_complete
  apply hlimit.congr'
  exact Eventually.of_forall fun n ↦
    ENNReal.toReal_ofReal
      (riemannXiUpperVerticalLogDefectWindow_zero_one_nonneg
        (quantitativeSpectralBoundaryTruncation n))

/-- Vanishing of the complete safe-axis transport target at `i` is exactly
the Riemann hypothesis. -/
theorem riemannXiUpperHyperbolicLogDefectMass_I_eq_zero_iff_riemannHypothesis :
    riemannXiUpperHyperbolicLogDefectMass Complex.I = 0 ↔
      RiemannHypothesis := by
  exact
    riemannXiUpperHyperbolicLogDefectMass_eq_zero_iff_riemannHypothesis
      (by norm_num) riemannXiSpectral_I_ne_zero

/-- The real complete target of safe-axis transport vanishes exactly when
the Riemann hypothesis holds. -/
theorem
    riemannXiUpperHyperbolicLogDefectMass_I_toReal_eq_zero_iff_riemannHypothesis
    :
    (riemannXiUpperHyperbolicLogDefectMass Complex.I).toReal = 0 ↔
      RiemannHypothesis := by
  rw [ENNReal.toReal_eq_zero_iff]
  simp only [riemannXiUpperHyperbolicLogDefectMass_I_ne_top, or_false]
  exact
    riemannXiUpperHyperbolicLogDefectMass_I_eq_zero_iff_riemannHypothesis

/-- Two-stage safe-axis transport certificate.  First, for every fixed
quantitative cutoff, the finite response integral converges as the height
tends to infinity.  Second, those recovered nonnegative values converge as
the cutoff grows to the finite complete RH-equivalent defect.  The statement
deliberately does not exchange these two limits. -/
theorem safeAxisBlaschkeTransport_iteratedLimits_quantitative_complete :
    (∀ n : ℕ,
      Tendsto
        (fun R : ℝ ↦ ∫ y : ℝ in 1..R, -2 *
          (-Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow
            (upperBoundaryApproachPoint 0 y)
              (quantitativeSpectralBoundaryTruncation n)).re)
        atTop
        (nhds (riemannXiUpperVerticalLogDefectWindow 0 1
          (quantitativeSpectralBoundaryTruncation n)))) ∧
      Tendsto
        (fun n : ℕ ↦ riemannXiUpperVerticalLogDefectWindow 0 1
          (quantitativeSpectralBoundaryTruncation n))
        atTop
        (nhds
          (riemannXiUpperHyperbolicLogDefectMass Complex.I).toReal) := by
  constructor
  · intro n
    exact
      tendsto_intervalIntegral_neg_two_mul_re_neg_I_blaschkeLogDerivativeWindow_safeAxis
        (quantitativeSpectralBoundaryTruncation n)
  · exact
      tendsto_riemannXiUpperVerticalLogDefectWindow_zero_one_quantitative_complete_toReal

/-- Combined static-boundary and safe-axis transport certificate.  On every
compact safe-axis height interval strictly above `1`, the arithmetic static
boundary comparison recovers the complete Blaschke detector; with the same
quantitative cutoffs, the explicitly ordered height-then-window limits of
that detector recover the finite complete RH-equivalent log defect at `i`.
No limit interchange is part of the statement. -/
theorem
    staticBoundaryRecovery_and_safeAxisBlaschkeTransport_quantitative_complete
    {a b : ℝ} (ha : 1 < a) :
    TendstoUniformlyOn
      (fun n : ℕ ↦ fun v : ℝ ↦
        xiSpectralBlaschkePairedHorizontalBoundaryValueWindow
            (quantitativeSpectralBoundaryTruncation n)
            ((v : ℂ) * Complex.I) -
          xiSpectralBlaschkeOuterHorizontalPairWindow
            (quantitativeSpectralBoundaryTruncation n)
            ((v : ℂ) * Complex.I))
      (fun v : ℝ ↦
        -(((2 * Real.pi : ℝ) : ℂ)) *
          riemannXiUpperBlaschkeCompleteLogDerivative
            ((v : ℂ) * Complex.I))
      atTop (Icc a b) ∧
      ((∀ n : ℕ,
        Tendsto
          (fun R : ℝ ↦ ∫ y : ℝ in 1..R, -2 *
            (-Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow
              (upperBoundaryApproachPoint 0 y)
                (quantitativeSpectralBoundaryTruncation n)).re)
          atTop
          (nhds (riemannXiUpperVerticalLogDefectWindow 0 1
            (quantitativeSpectralBoundaryTruncation n)))) ∧
        Tendsto
          (fun n : ℕ ↦ riemannXiUpperVerticalLogDefectWindow 0 1
            (quantitativeSpectralBoundaryTruncation n))
          atTop
          (nhds
            (riemannXiUpperHyperbolicLogDefectMass Complex.I).toReal)) := by
  exact ⟨
    tendstoUniformlyOn_xiSpectralBlaschkePairedBoundary_sub_outer_quantitative_completeDetector
      ha,
    safeAxisBlaschkeTransport_iteratedLimits_quantitative_complete⟩

end

end RiemannGaussian
