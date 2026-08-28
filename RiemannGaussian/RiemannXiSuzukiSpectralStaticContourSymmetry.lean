import RiemannGaussian.RiemannXiSuzukiSpectralStaticContourDeformation

/-!
# Static spectral-contour symmetry

This module folds the four signed vertical boundary pieces of the static
spectral-xi contour onto the right half of a single vertical line.  On a
purely imaginary observation point, conjugation turns that folded contour
exactly into a real signed integral.  This isolates the cancellation required
at large quantitative heights without replacing it by an absolute-value
assumption.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The derivative of spectral xi commutes with complex conjugation. -/
theorem deriv_riemannXiSpectral_conj (z : ℂ) :
    deriv riemannXiSpectral (starRingEnd ℂ z) =
      starRingEnd ℂ (deriv riemannXiSpectral z) := by
  have hfun :
      (starRingEnd ℂ ∘ riemannXiSpectral ∘ starRingEnd ℂ) =
        riemannXiSpectral := by
    funext w
    simp [Function.comp_apply, riemannXiSpectral_conj]
  have hderiv :=
    congrFun (deriv_conj_conj (f := riemannXiSpectral))
      (starRingEnd ℂ z)
  rw [hfun] at hderiv
  simpa [Function.comp_apply] using hderiv

/-- The spectral-xi negative logarithmic derivative is anti-equivariant under
complex conjugation. -/
@[simp] theorem xiSpectralNegativeLogDerivative_conj (z : ℂ) :
    xiSpectralNegativeLogDerivative (starRingEnd ℂ z) =
      -starRingEnd ℂ (xiSpectralNegativeLogDerivative z) := by
  rw [xiSpectralNegativeLogDerivative_eq_I_mul_logDeriv,
    xiSpectralNegativeLogDerivative_eq_I_mul_logDeriv,
    logDeriv_apply, logDeriv_apply,
    deriv_riemannXiSpectral_conj, riemannXiSpectral_conj]
  simp

/-- The odd Cauchy factor obtained by folding a left vertical side onto the
right vertical line. -/
def xiSpectralBlaschkeRightFoldedVerticalKernel
    (T : ℝ) (z : ℂ) (y : ℝ) : ℂ :=
  let w : ℂ := (T : ℂ) + (y : ℂ) * Complex.I
  xiSpectralNegativeLogDerivative w *
    (1 / (z - w) - 1 / (z + w))

/-- Folding the left vertical kernel across the origin gives the odd Cauchy
difference on the right vertical line. -/
theorem xiSpectralBlaschkeRightFoldedVerticalKernel_eq
    (T : ℝ) (z : ℂ) (y : ℝ) :
    xiSpectralBlaschkeRightFoldedVerticalKernel T z y =
      xiSpectralBlaschkeRightVerticalKernel T z y +
        xiSpectralBlaschkeLeftVerticalKernel T z (-y) := by
  unfold xiSpectralBlaschkeRightFoldedVerticalKernel
    xiSpectralBlaschkeRightVerticalKernel
    xiSpectralBlaschkeLeftVerticalKernel
    xiSpectralBlaschkeContourKernel
  rw [show
      (((-T : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I) =
        -((T : ℂ) + (y : ℂ) * Complex.I) by
      push_cast
      ring,
    xiSpectralNegativeLogDerivative_neg]
  ring

/-- The folded right-line kernel is integrable whenever the static vertical
boundary avoids spectral xi zeros. -/
theorem intervalIntegrable_xiSpectralBlaschkeRightFoldedVerticalKernel
    {z : ℂ} (hz : 1 < z.im)
    {T : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T) :
    IntervalIntegrable
      (xiSpectralBlaschkeRightFoldedVerticalKernel T z)
      volume (-1) 1 := by
  let R : ℝ → ℂ := xiSpectralBlaschkeRightVerticalKernel T z
  let L : ℝ → ℂ := xiSpectralBlaschkeLeftVerticalKernel T z
  have hR : IntervalIntegrable R volume (-1) 1 := by
    simpa [R] using
      intervalIntegrable_xiSpectralBlaschkeRightVerticalKernel
        hz hT hboundary
  have hL : IntervalIntegrable L volume (-1) 1 := by
    simpa [L] using
      intervalIntegrable_xiSpectralBlaschkeLeftVerticalKernel
        hz hT hboundary
  have hLneg : IntervalIntegrable (fun y ↦ L (-y)) volume (-1) 1 := by
    simpa using (IntervalIntegrable.iff_comp_neg).mp hL.symm
  rw [show
      xiSpectralBlaschkeRightFoldedVerticalKernel T z =
        fun y ↦ R y + L (-y) by
      funext y
      exact xiSpectralBlaschkeRightFoldedVerticalKernel_eq T z y]
  exact hR.add hLneg

/-- At zero inner height, the four signed vertical contour pieces equal the
difference of the two half-integrals of the folded right-line kernel. -/
theorem xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_eq_folded
    {z : ℂ} (hz : 1 < z.im)
    {T : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T) :
    xiSpectralBlaschkeSignedVerticalRemainderWindow T 0 z =
      Complex.I * ((∫ y : ℝ in (0 : ℝ)..1,
        xiSpectralBlaschkeRightFoldedVerticalKernel T z y) -
          ∫ y : ℝ in (-1 : ℝ)..0,
            xiSpectralBlaschkeRightFoldedVerticalKernel T z y) := by
  let R : ℝ → ℂ := xiSpectralBlaschkeRightVerticalKernel T z
  let L : ℝ → ℂ := xiSpectralBlaschkeLeftVerticalKernel T z
  let F : ℝ → ℂ :=
    xiSpectralBlaschkeRightFoldedVerticalKernel T z
  have hRfull : IntervalIntegrable R volume (-1) 1 := by
    simpa [R] using
      intervalIntegrable_xiSpectralBlaschkeRightVerticalKernel
        hz hT hboundary
  have hLfull : IntervalIntegrable L volume (-1) 1 := by
    simpa [L] using
      intervalIntegrable_xiSpectralBlaschkeLeftVerticalKernel
        hz hT hboundary
  have hRupper : IntervalIntegrable R volume 0 1 :=
    hRfull.mono_set (by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
        uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      exact Icc_subset_Icc (by norm_num) le_rfl)
  have hRlower : IntervalIntegrable R volume (-1) 0 :=
    hRfull.mono_set (by
      rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0),
        uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      exact Icc_subset_Icc le_rfl (by norm_num))
  have hLupper : IntervalIntegrable L volume 0 1 :=
    hLfull.mono_set (by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
        uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      exact Icc_subset_Icc (by norm_num) le_rfl)
  have hLlower : IntervalIntegrable L volume (-1) 0 :=
    hLfull.mono_set (by
      rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0),
        uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      exact Icc_subset_Icc le_rfl (by norm_num))
  have hLnegUpper : IntervalIntegrable (fun y ↦ L (-y)) volume 0 1 := by
    simpa using (IntervalIntegrable.iff_comp_neg).mp hLlower.symm
  have hLnegLower : IntervalIntegrable (fun y ↦ L (-y)) volume (-1) 0 := by
    simpa using (IntervalIntegrable.iff_comp_neg).mp hLupper.symm
  have hF : F = fun y ↦ R y + L (-y) := by
    funext y
    exact xiSpectralBlaschkeRightFoldedVerticalKernel_eq T z y
  rw [show
      (∫ y : ℝ in (0 : ℝ)..1, F y) =
        (∫ y : ℝ in (0 : ℝ)..1, R y) +
          ∫ y : ℝ in (-1 : ℝ)..0, L y by
      rw [hF, intervalIntegral.integral_add hRupper hLnegUpper,
        intervalIntegral.integral_comp_neg]
      simp,
    show
      (∫ y : ℝ in (-1 : ℝ)..0, F y) =
        (∫ y : ℝ in (-1 : ℝ)..0, R y) +
          ∫ y : ℝ in (0 : ℝ)..1, L y by
      rw [hF, intervalIntegral.integral_add hRlower hLnegLower,
        intervalIntegral.integral_comp_neg]
      simp]
  let RU : ℂ := ∫ y : ℝ in (0 : ℝ)..1, R y
  let LU : ℂ := ∫ y : ℝ in (0 : ℝ)..1, L y
  let RL : ℂ := ∫ y : ℝ in (-1 : ℝ)..0, R y
  let LL : ℂ := ∫ y : ℝ in (-1 : ℝ)..0, L y
  unfold xiSpectralBlaschkeSignedVerticalRemainderWindow
  simp only [neg_zero]
  change
    Complex.I * RU - Complex.I * LU -
          Complex.I * RL + Complex.I * LL =
      Complex.I * ((RU + LL) - (RL + LU))
  ring

/-- At a purely imaginary observation point, reflection of the vertical
parameter is negative complex conjugation of the folded kernel. -/
@[simp]
theorem xiSpectralBlaschkeRightFoldedVerticalKernel_neg_of_imaginary
    (T v y : ℝ) :
    xiSpectralBlaschkeRightFoldedVerticalKernel T
        ((v : ℂ) * Complex.I) (-y) =
      -starRingEnd ℂ
        (xiSpectralBlaschkeRightFoldedVerticalKernel T
          ((v : ℂ) * Complex.I) y) := by
  let z : ℂ := (v : ℂ) * Complex.I
  let w : ℂ := (T : ℂ) + (y : ℂ) * Complex.I
  have hw :
      ((T : ℂ) + ((-y : ℝ) : ℂ) * Complex.I) =
        starRingEnd ℂ w := by
    dsimp [w]
    apply Complex.ext <;> simp
  have hz : starRingEnd ℂ z = -z := by
    dsimp [z]
    simp
  have hkernel :
      starRingEnd ℂ (1 / (z - w) - 1 / (z + w)) =
        1 / (z - starRingEnd ℂ w) -
          1 / (z + starRingEnd ℂ w) := by
    rw [map_sub]
    simp only [one_div, map_inv₀, map_sub, map_add, hz]
    rw [show -z - starRingEnd ℂ w =
          -(z + starRingEnd ℂ w) by ring,
      show -z + starRingEnd ℂ w =
          -(z - starRingEnd ℂ w) by ring]
    simp only [inv_neg]
    ring
  unfold xiSpectralBlaschkeRightFoldedVerticalKernel
  dsimp only
  rw [hw]
  change
    xiSpectralNegativeLogDerivative (starRingEnd ℂ w) *
        (1 / (z - starRingEnd ℂ w) -
          1 / (z + starRingEnd ℂ w)) =
      -starRingEnd ℂ
        (xiSpectralNegativeLogDerivative w *
          (1 / (z - w) - 1 / (z + w)))
  rw [xiSpectralNegativeLogDerivative_conj, ← hkernel, map_mul]
  ring

/-- At a purely imaginary observation point, the zero-inner-height vertical
remainder is `I` times an upper-half integral plus its conjugate. -/
theorem xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_imaginary_eq
    {v : ℝ} (hv : 1 < v)
    {T : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T) :
    xiSpectralBlaschkeSignedVerticalRemainderWindow T 0
        ((v : ℂ) * Complex.I) =
      Complex.I *
        ((∫ y : ℝ in (0 : ℝ)..1,
          xiSpectralBlaschkeRightFoldedVerticalKernel T
            ((v : ℂ) * Complex.I) y) +
          starRingEnd ℂ
            (∫ y : ℝ in (0 : ℝ)..1,
              xiSpectralBlaschkeRightFoldedVerticalKernel T
                ((v : ℂ) * Complex.I) y)) := by
  let F : ℝ → ℂ :=
    xiSpectralBlaschkeRightFoldedVerticalKernel T
      ((v : ℂ) * Complex.I)
  have hz : 1 < (((v : ℂ) * Complex.I)).im := by simpa
  rw [xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_eq_folded
    hz hT hboundary]
  have hlower :
      (∫ y : ℝ in (-1 : ℝ)..0, F y) =
        -starRingEnd ℂ (∫ y : ℝ in (0 : ℝ)..1, F y) := by
    calc
      (∫ y : ℝ in (-1 : ℝ)..0, F y) =
          ∫ y : ℝ in (0 : ℝ)..1, F (-y) := by
        rw [intervalIntegral.integral_comp_neg]
        simp
      _ = ∫ y : ℝ in (0 : ℝ)..1,
          -starRingEnd ℂ (F y) := by
        apply intervalIntegral.integral_congr
        intro y _hy
        exact
          xiSpectralBlaschkeRightFoldedVerticalKernel_neg_of_imaginary
            T v y
      _ = -(∫ y : ℝ in (0 : ℝ)..1,
          starRingEnd ℂ (F y)) :=
        intervalIntegral.integral_neg
      _ = -starRingEnd ℂ (∫ y : ℝ in (0 : ℝ)..1, F y) := by
        rw [intervalIntegral.intervalIntegral_conj]
  change Complex.I *
      ((∫ y : ℝ in (0 : ℝ)..1, F y) -
        ∫ y : ℝ in (-1 : ℝ)..0, F y) = _
  rw [hlower]
  ring

/-- The zero-inner-height signed vertical remainder is purely imaginary at a
purely imaginary observation point above the spectral strip. -/
theorem xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_imaginary_re
    {v : ℝ} (hv : 1 < v)
    {T : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T) :
    (xiSpectralBlaschkeSignedVerticalRemainderWindow T 0
      ((v : ℂ) * Complex.I)).re = 0 := by
  rw [xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_imaginary_eq
    hv hT hboundary]
  simp

/-- Multiplication by `-I` identifies the imaginary-axis vertical remainder
with twice the real signed integral of the folded upper-half kernel. -/
theorem neg_I_mul_xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_imaginary
    {v : ℝ} (hv : 1 < v)
    {T : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T) :
    -Complex.I *
        xiSpectralBlaschkeSignedVerticalRemainderWindow T 0
          ((v : ℂ) * Complex.I) =
      ((2 * (∫ y : ℝ in (0 : ℝ)..1,
        (xiSpectralBlaschkeRightFoldedVerticalKernel T
          ((v : ℂ) * Complex.I) y).re) : ℝ) : ℂ) := by
  let F : ℝ → ℂ :=
    xiSpectralBlaschkeRightFoldedVerticalKernel T
      ((v : ℂ) * Complex.I)
  let J : ℂ := ∫ y : ℝ in (0 : ℝ)..1, F y
  have hz : 1 < (((v : ℂ) * Complex.I)).im := by simpa
  have hFfull : IntervalIntegrable F volume (-1) 1 := by
    simpa [F] using
      intervalIntegrable_xiSpectralBlaschkeRightFoldedVerticalKernel
        hz hT hboundary
  have hFupper : IntervalIntegrable F volume 0 1 :=
    hFfull.mono_set (by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
        uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      exact Icc_subset_Icc (by norm_num) le_rfl)
  have hre :
      (∫ y : ℝ in (0 : ℝ)..1, (F y).re) = J.re := by
    simpa [J] using intervalIntegral.intervalIntegral_re hFupper
  rw [xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_imaginary_eq
    hv hT hboundary]
  change -Complex.I *
      (Complex.I * (J + starRingEnd ℂ J)) =
    ((2 * (∫ y : ℝ in (0 : ℝ)..1, (F y).re) : ℝ) : ℂ)
  rw [hre]
  apply Complex.ext
  · simp
    ring
  · simp

/-- The folded Cauchy factor contributes at most `2 / T` on a positive right
vertical line. -/
theorem norm_xiSpectralBlaschkeRightFoldedVerticalKernel_le
    {T : ℝ} (hT : 0 < T) (v y : ℝ) :
    ‖xiSpectralBlaschkeRightFoldedVerticalKernel T
        ((v : ℂ) * Complex.I) y‖ ≤
      (2 / T) *
        ‖xiSpectralNegativeLogDerivative
          ((T : ℂ) + (y : ℂ) * Complex.I)‖ := by
  let z : ℂ := (v : ℂ) * Complex.I
  let w : ℂ := (T : ℂ) + (y : ℂ) * Complex.I
  have hminus : T ≤ ‖z - w‖ := by
    calc
      T = |(z - w).re| := by
        simp [z, w, abs_of_pos hT]
      _ ≤ ‖z - w‖ := Complex.abs_re_le_norm _
  have hplus : T ≤ ‖z + w‖ := by
    calc
      T = |(z + w).re| := by
        simp [z, w, abs_of_pos hT]
      _ ≤ ‖z + w‖ := Complex.abs_re_le_norm _
  have hminusInv : ‖1 / (z - w)‖ ≤ 1 / T := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hT hminus
  have hplusInv : ‖1 / (z + w)‖ ≤ 1 / T := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hT hplus
  unfold xiSpectralBlaschkeRightFoldedVerticalKernel
  dsimp only
  change ‖xiSpectralNegativeLogDerivative w *
      (1 / (z - w) - 1 / (z + w))‖ ≤ _
  rw [norm_mul]
  calc
    ‖xiSpectralNegativeLogDerivative w‖ *
        ‖1 / (z - w) - 1 / (z + w)‖ ≤
      ‖xiSpectralNegativeLogDerivative w‖ *
        (‖1 / (z - w)‖ + ‖1 / (z + w)‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
    _ ≤ ‖xiSpectralNegativeLogDerivative w‖ *
        (1 / T + 1 / T) := by
      gcongr
    _ = (2 / T) * ‖xiSpectralNegativeLogDerivative w‖ := by
      ring

/-- On the quantitative zero-free contour sequence, the imaginary-axis
vertical remainder is bounded by `4 / T` times the right-line logarithmic
derivative `L¹` norm.  This is a baseline absolute estimate; the exact signed
identity above records the stronger cancellation still needed at infinity. -/
theorem norm_xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_imaginary_quantitative_le
    {v : ℝ} (hv : 1 < v) (n : ℕ) :
    ‖xiSpectralBlaschkeSignedVerticalRemainderWindow
        (quantitativeSpectralBoundaryTruncation n) 0
        ((v : ℂ) * Complex.I)‖ ≤
      (4 / quantitativeSpectralBoundaryTruncation n) *
        (∫ y : ℝ in (0 : ℝ)..1,
          ‖xiSpectralNegativeLogDerivative
            ((quantitativeSpectralBoundaryTruncation n : ℂ) +
              (y : ℂ) * Complex.I)‖) := by
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  have hT : 0 < T :=
    (Nat.cast_nonneg n).trans_lt
      (by simpa [T] using (quantitativeSpectralBoundaryTruncation_spec n).1)
  have hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T := by
    simpa [T] using quantitativeSpectralBoundaryTruncation_zeroFree n
  let F : ℝ → ℂ :=
    xiSpectralBlaschkeRightFoldedVerticalKernel T
      ((v : ℂ) * Complex.I)
  let L : ℝ → ℂ := fun y ↦
    xiSpectralNegativeLogDerivative
      ((T : ℂ) + (y : ℂ) * Complex.I)
  let J : ℂ := ∫ y : ℝ in (0 : ℝ)..1, F y
  have hz : 1 < (((v : ℂ) * Complex.I)).im := by simpa
  have hFfull : IntervalIntegrable F volume (-1) 1 := by
    simpa [F] using
      intervalIntegrable_xiSpectralBlaschkeRightFoldedVerticalKernel
        hz hT.le hboundary
  have hFupper : IntervalIntegrable F volume 0 1 :=
    hFfull.mono_set (by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
        uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      exact Icc_subset_Icc (by norm_num) le_rfl)
  have hLfull : IntervalIntegrable L volume (-1) 1 := by
    simpa [L] using
      intervalIntegrable_xiSpectralNegativeLogDerivative_quantitative n
  have hLupper : IntervalIntegrable L volume 0 1 :=
    hLfull.mono_set (by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
        uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      exact Icc_subset_Icc (by norm_num) le_rfl)
  have hpoint (y : ℝ) (_hy : y ∈ Icc (0 : ℝ) 1) :
      ‖F y‖ ≤ (2 / T) * ‖L y‖ := by
    exact norm_xiSpectralBlaschkeRightFoldedVerticalKernel_le hT v y
  have hnormIntegral :
      (∫ y : ℝ in (0 : ℝ)..1, ‖F y‖) ≤
        (2 / T) * (∫ y : ℝ in (0 : ℝ)..1, ‖L y‖) := by
    calc
      (∫ y : ℝ in (0 : ℝ)..1, ‖F y‖) ≤
          ∫ y : ℝ in (0 : ℝ)..1, (2 / T) * ‖L y‖ := by
        exact intervalIntegral.integral_mono_on (by norm_num)
          hFupper.norm (hLupper.norm.const_mul (2 / T)) hpoint
      _ = (2 / T) * (∫ y : ℝ in (0 : ℝ)..1, ‖L y‖) := by
        rw [intervalIntegral.integral_const_mul]
  have hJ :
      ‖J‖ ≤ ∫ y : ℝ in (0 : ℝ)..1, ‖F y‖ := by
    exact intervalIntegral.norm_integral_le_integral_norm (by norm_num)
  rw [xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_imaginary_eq
    hv hT.le hboundary]
  change ‖Complex.I * (J + starRingEnd ℂ J)‖ ≤
    (4 / T) * (∫ y : ℝ in (0 : ℝ)..1, ‖L y‖)
  rw [norm_mul, norm_I, one_mul]
  calc
    ‖J + starRingEnd ℂ J‖ ≤
        ‖J‖ + ‖starRingEnd ℂ J‖ := norm_add_le _ _
    _ = 2 * ‖J‖ := by simp; ring
    _ ≤ 2 * (∫ y : ℝ in (0 : ℝ)..1, ‖F y‖) :=
      mul_le_mul_of_nonneg_left hJ (by norm_num)
    _ ≤ 2 * ((2 / T) *
        (∫ y : ℝ in (0 : ℝ)..1, ‖L y‖)) :=
      mul_le_mul_of_nonneg_left hnormIntegral (by norm_num)
    _ = (4 / T) * (∫ y : ℝ in (0 : ℝ)..1, ‖L y‖) := by
      ring

end

end RiemannGaussian
