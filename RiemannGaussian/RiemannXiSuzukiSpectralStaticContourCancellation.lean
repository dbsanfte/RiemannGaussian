import RiemannGaussian.RiemannXiSuzukiSpectralStaticContourSymmetry

/-!
# Large-height cancellation for the static spectral contour

The folded imaginary-axis Cauchy kernel has a dominant constant term
`-2 / T`.  This module subtracts that term and proves a uniform inverse-square
bound for the remainder.  The existing subquadratic logarithmic-derivative
estimate then makes the integrated remainder vanish on the quantitative
zero-free contour sequence.  Thus the static vertical boundary is reduced,
unconditionally, to one signed integral of the real part of the spectral-xi
negative logarithmic derivative.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The Cauchy-factor error left after removing its dominant `-2 / T`
term on a purely imaginary observation point. -/
def xiSpectralBlaschkeImaginaryAxisCauchyRemainder
    (T v y : ℝ) : ℂ :=
  let z : ℂ := (v : ℂ) * Complex.I
  let w : ℂ := (T : ℂ) + (y : ℂ) * Complex.I
  (1 / (z - w) - 1 / (z + w)) + ((2 / T : ℝ) : ℂ)

/-- On the upper half of a positive vertical segment, the renormalized
Cauchy factor has uniform inverse-square decay. -/
theorem norm_xiSpectralBlaschkeImaginaryAxisCauchyRemainder_le
    {T v y : ℝ} (hT : 0 < T) (hv : 1 < v)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ‖xiSpectralBlaschkeImaginaryAxisCauchyRemainder T v y‖ ≤
      2 * v / T ^ 2 := by
  let z : ℂ := (v : ℂ) * Complex.I
  let w : ℂ := (T : ℂ) + (y : ℂ) * Complex.I
  have hminusNorm : T ≤ ‖z - w‖ := by
    calc
      T = |(z - w).re| := by
        simp [z, w, abs_of_pos hT]
      _ ≤ ‖z - w‖ := Complex.abs_re_le_norm _
  have hplusNorm : T ≤ ‖z + w‖ := by
    calc
      T = |(z + w).re| := by
        simp [z, w, abs_of_pos hT]
      _ ≤ ‖z + w‖ := Complex.abs_re_le_norm _
  have hminus : z - w ≠ 0 :=
    norm_ne_zero_iff.mp (ne_of_gt (hT.trans_le hminusNorm))
  have hplus : z + w ≠ 0 :=
    norm_ne_zero_iff.mp (ne_of_gt (hT.trans_le hplusNorm))
  have hTcomplex : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hnegTcomplex : ((-T : ℝ) : ℂ) ≠ 0 := by exact_mod_cast neg_ne_zero.mpr hT.ne'
  have hfirstEq :
      1 / (z - w) + ((1 / T : ℝ) : ℂ) =
        (z - w)⁻¹ - ((-T : ℝ) : ℂ)⁻¹ := by
    rw [one_div]
    push_cast
    rw [inv_neg]
    ring
  have hsecondEq :
      -(1 / (z + w)) + ((1 / T : ℝ) : ℂ) =
        (T : ℂ)⁻¹ - (z + w)⁻¹ := by
    rw [one_div]
    push_cast
    ring
  have hfirstNorm :
      ‖1 / (z - w) + ((1 / T : ℝ) : ℂ)‖ ≤
        (v - y) / T ^ 2 := by
    rw [hfirstEq, inv_sub_inv hminus hnegTcomplex, norm_div,
      norm_mul]
    have hnum : ‖((-T : ℝ) : ℂ) - (z - w)‖ = v - y := by
      have hid : ((-T : ℝ) : ℂ) - (z - w) =
          -((v - y : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [z, w]
      rw [hid]
      rw [norm_mul, norm_neg, norm_real, norm_I, mul_one,
        Real.norm_eq_abs,
        abs_of_nonneg (by linarith)]
    rw [hnum, norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hT]
    apply div_le_div_of_nonneg_left (by linarith) (sq_pos_of_pos hT)
    simpa [pow_two] using
      mul_le_mul_of_nonneg_right hminusNorm hT.le
  have hsecondNorm :
      ‖-(1 / (z + w)) + ((1 / T : ℝ) : ℂ)‖ ≤
        (v + y) / T ^ 2 := by
    rw [hsecondEq, inv_sub_inv hTcomplex hplus, norm_div,
      norm_mul]
    have hnum : ‖(z + w) - (T : ℂ)‖ = v + y := by
      have hid : (z + w) - (T : ℂ) =
          ((v + y : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [z, w]
      rw [hid]
      rw [norm_mul, norm_real, norm_I, mul_one,
        Real.norm_eq_abs,
        abs_of_nonneg (by linarith)]
    rw [hnum, norm_real, Real.norm_eq_abs, abs_of_pos hT]
    apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hT)
    simpa [pow_two] using
      mul_le_mul_of_nonneg_left hplusNorm hT.le
  unfold xiSpectralBlaschkeImaginaryAxisCauchyRemainder
  dsimp only
  rw [show
      (1 / (z - w) - 1 / (z + w)) + ((2 / T : ℝ) : ℂ) =
        (1 / (z - w) + ((1 / T : ℝ) : ℂ)) +
          (-(1 / (z + w)) + ((1 / T : ℝ) : ℂ)) by
      push_cast
      ring]
  calc
    ‖(1 / (z - w) + ((1 / T : ℝ) : ℂ)) +
        (-(1 / (z + w)) + ((1 / T : ℝ) : ℂ))‖ ≤
      ‖1 / (z - w) + ((1 / T : ℝ) : ℂ)‖ +
        ‖-(1 / (z + w)) + ((1 / T : ℝ) : ℂ)‖ :=
      norm_add_le _ _
    _ ≤ (v - y) / T ^ 2 + (v + y) / T ^ 2 :=
      add_le_add hfirstNorm hsecondNorm
    _ = 2 * v / T ^ 2 := by ring

/-- Pointwise, the real folded kernel differs from `-(2 / T)` times the
real logarithmic derivative by an inverse-square error. -/
theorem abs_xiSpectralBlaschkeRightFoldedVerticalKernel_re_add_main_le
    {T v y : ℝ} (hT : 0 < T) (hv : 1 < v)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    |(xiSpectralBlaschkeRightFoldedVerticalKernel T
          ((v : ℂ) * Complex.I) y).re +
        (2 / T) *
          (xiSpectralNegativeLogDerivative
            ((T : ℂ) + (y : ℂ) * Complex.I)).re| ≤
      (2 * v / T ^ 2) *
        ‖xiSpectralNegativeLogDerivative
          ((T : ℂ) + (y : ℂ) * Complex.I)‖ := by
  let z : ℂ := (v : ℂ) * Complex.I
  let w : ℂ := (T : ℂ) + (y : ℂ) * Complex.I
  let D : ℂ := xiSpectralNegativeLogDerivative w
  let K : ℂ := 1 / (z - w) - 1 / (z + w)
  let R : ℂ := K + ((2 / T : ℝ) : ℂ)
  have hR : ‖R‖ ≤ 2 * v / T ^ 2 := by
    simpa [R, K, z, w,
      xiSpectralBlaschkeImaginaryAxisCauchyRemainder] using
      norm_xiSpectralBlaschkeImaginaryAxisCauchyRemainder_le
        hT hv hy0 hy1
  have hid :
      (xiSpectralBlaschkeRightFoldedVerticalKernel T z y).re +
          (2 / T) * D.re = (D * R).re := by
    unfold xiSpectralBlaschkeRightFoldedVerticalKernel
    dsimp only
    change (D * K).re + (2 / T) * D.re = (D * R).re
    simp [mul_re, R, K]
    ring
  change |(xiSpectralBlaschkeRightFoldedVerticalKernel T z y).re +
      (2 / T) * D.re| ≤ (2 * v / T ^ 2) * ‖D‖
  rw [hid]
  calc
    |(D * R).re| ≤ ‖D * R‖ := Complex.abs_re_le_norm _
    _ = ‖D‖ * ‖R‖ := norm_mul _ _
    _ ≤ ‖D‖ * (2 * v / T ^ 2) :=
      mul_le_mul_of_nonneg_left hR (norm_nonneg _)
    _ = (2 * v / T ^ 2) * ‖D‖ := mul_comm _ _

/-- The pointwise Cauchy-factor cancellation integrates on the quantitative
zero-free right line with the genuine logarithmic-derivative `L¹` norm as
majorant. -/
theorem abs_intervalIntegral_xiSpectralBlaschkeRightFoldedVerticalKernel_re_add_main_quantitative_le
    {v : ℝ} (hv : 1 < v) (n : ℕ) :
    |(∫ y : ℝ in (0 : ℝ)..1,
          (xiSpectralBlaschkeRightFoldedVerticalKernel
            (quantitativeSpectralBoundaryTruncation n)
            ((v : ℂ) * Complex.I) y).re) +
        (2 / quantitativeSpectralBoundaryTruncation n) *
          (∫ y : ℝ in (0 : ℝ)..1,
            (xiSpectralNegativeLogDerivative
              ((quantitativeSpectralBoundaryTruncation n : ℂ) +
                (y : ℂ) * Complex.I)).re)| ≤
      (2 * v / quantitativeSpectralBoundaryTruncation n ^ 2) *
        (∫ y : ℝ in (0 : ℝ)..1,
          ‖xiSpectralNegativeLogDerivative
            ((quantitativeSpectralBoundaryTruncation n : ℂ) +
              (y : ℂ) * Complex.I)‖) := by
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let z : ℂ := (v : ℂ) * Complex.I
  let F : ℝ → ℂ := xiSpectralBlaschkeRightFoldedVerticalKernel T z
  let D : ℝ → ℂ := fun y ↦
    xiSpectralNegativeLogDerivative
      ((T : ℂ) + (y : ℂ) * Complex.I)
  let g : ℝ → ℝ := fun y ↦ (F y).re + (2 / T) * (D y).re
  have hT : 0 < T :=
    (Nat.cast_nonneg n).trans_lt
      (by simpa [T] using (quantitativeSpectralBoundaryTruncation_spec n).1)
  have hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T := by
    simpa [T] using quantitativeSpectralBoundaryTruncation_zeroFree n
  have hz : 1 < z.im := by simpa [z]
  have hFfull : IntervalIntegrable F volume (-1) 1 := by
    simpa [F] using
      intervalIntegrable_xiSpectralBlaschkeRightFoldedVerticalKernel
        hz hT.le hboundary
  have hFupper : IntervalIntegrable F volume 0 1 :=
    hFfull.mono_set (by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
        uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      exact Icc_subset_Icc (by norm_num) le_rfl)
  have hDfull : IntervalIntegrable D volume (-1) 1 := by
    simpa [D, T] using
      intervalIntegrable_xiSpectralNegativeLogDerivative_quantitative n
  have hDupper : IntervalIntegrable D volume 0 1 :=
    hDfull.mono_set (by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
        uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      exact Icc_subset_Icc (by norm_num) le_rfl)
  have hFre : IntervalIntegrable (fun y ↦ (F y).re) volume 0 1 :=
    ⟨by
      simpa [Function.comp_def] using
        Complex.reCLM.integrableOn_comp hFupper.1,
    by simp⟩
  have hDre : IntervalIntegrable (fun y ↦ (D y).re) volume 0 1 :=
    ⟨by
      simpa [Function.comp_def] using
        Complex.reCLM.integrableOn_comp hDupper.1,
    by simp⟩
  have hg : IntervalIntegrable g volume 0 1 :=
    hFre.add (hDre.const_mul (2 / T))
  have hpoint (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) :
      |g y| ≤ (2 * v / T ^ 2) * ‖D y‖ := by
    exact
      abs_xiSpectralBlaschkeRightFoldedVerticalKernel_re_add_main_le
        hT hv hy.1 hy.2
  have hmono :
      (∫ y : ℝ in (0 : ℝ)..1, |g y|) ≤
        ∫ y : ℝ in (0 : ℝ)..1, (2 * v / T ^ 2) * ‖D y‖ := by
    exact intervalIntegral.integral_mono_on (by norm_num) hg.abs
      (hDupper.norm.const_mul (2 * v / T ^ 2)) hpoint
  have heq :
      (∫ y : ℝ in (0 : ℝ)..1, g y) =
        (∫ y : ℝ in (0 : ℝ)..1, (F y).re) +
          (2 / T) * (∫ y : ℝ in (0 : ℝ)..1, (D y).re) := by
    rw [intervalIntegral.integral_add hFre
      (hDre.const_mul (2 / T)), intervalIntegral.integral_const_mul]
  change |(∫ y : ℝ in (0 : ℝ)..1, (F y).re) +
      (2 / T) * (∫ y : ℝ in (0 : ℝ)..1, (D y).re)| ≤
    (2 * v / T ^ 2) *
      (∫ y : ℝ in (0 : ℝ)..1, ‖D y‖)
  rw [← heq]
  calc
    |∫ y : ℝ in (0 : ℝ)..1, g y| ≤
        ∫ y : ℝ in (0 : ℝ)..1, |g y| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ y : ℝ in (0 : ℝ)..1,
        (2 * v / T ^ 2) * ‖D y‖ := hmono
    _ = (2 * v / T ^ 2) *
        (∫ y : ℝ in (0 : ℝ)..1, ‖D y‖) := by
      rw [intervalIntegral.integral_const_mul]

/-- The inverse-square-weighted upper-half `L¹` norm of the genuine
spectral-xi logarithmic derivative tends to zero on the quantitative contour
sequence. -/
theorem tendsto_inv_sq_mul_intervalIntegral_norm_xiSpectralNegativeLogDerivative_quantitative_upper_zero :
    Tendsto
      (fun n : ℕ ↦
        (1 / quantitativeSpectralBoundaryTruncation n ^ 2) *
          (∫ y : ℝ in (0 : ℝ)..1,
            ‖xiSpectralNegativeLogDerivative
              ((quantitativeSpectralBoundaryTruncation n : ℂ) +
                (y : ℂ) * Complex.I)‖))
      atTop (nhds 0) := by
  rcases riemannXi_threeHalvesGrowth with ⟨A, hA, hThreeHalves⟩
  rcases riemannXi_quadraticGrowth with ⟨B, hB, hQuadratic⟩
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦ mul_nonneg (by positivity)
      (intervalIntegral.integral_nonneg_of_forall (by norm_num)
        (fun y ↦ norm_nonneg _))
  · exact Eventually.of_forall fun n ↦ by
      let T : ℝ := quantitativeSpectralBoundaryTruncation n
      let D : ℝ → ℂ := fun y ↦
        xiSpectralNegativeLogDerivative
          ((T : ℂ) + (y : ℂ) * Complex.I)
      let L : ℝ :=
        2 * ((2 * (B * (xiCanonicalRadius n + 1) ^ 2)) /
            (xiCanonicalRadius n / 4)) +
          (A * (2 * xiCanonicalRadius n + 1) ^ (3 / 2 : ℝ) /
              Real.log 2) *
            (4 / xiCanonicalRadius n +
              2 * Real.log
                (1 + 3 / spectralBoundarySeparation n))
      have hT : 0 < T :=
        (Nat.cast_nonneg n).trans_lt
          (by simpa [T] using
            (quantitativeSpectralBoundaryTruncation_spec n).1)
      have hDfull : IntervalIntegrable D volume (-1) 1 := by
        simpa [D, T] using
          intervalIntegrable_xiSpectralNegativeLogDerivative_quantitative n
      have hupperFull :
          (∫ y : ℝ in (0 : ℝ)..1, ‖D y‖) ≤
            ∫ y : ℝ in (-1 : ℝ)..1, ‖D y‖ := by
        exact intervalIntegral.integral_mono_interval (by norm_num)
          (by norm_num) le_rfl
          (Eventually.of_forall fun y ↦ norm_nonneg (D y)) hDfull.norm
      have hfullL :
          (∫ y : ℝ in (-1 : ℝ)..1, ‖D y‖) ≤ L := by
        simpa [D, T, L] using
          intervalIntegral_norm_xiSpectralNegativeLogDerivative_quantitative_le_of_growth
            hA hThreeHalves hB hQuadratic n
      have hL : 0 ≤ L :=
        (intervalIntegral.integral_nonneg_of_forall (by norm_num)
          (fun y ↦ norm_nonneg (D y))).trans hfullL
      change (1 / T ^ 2) *
          (∫ y : ℝ in (0 : ℝ)..1, ‖D y‖) ≤
        suzukiXiWeilVerticalExplicitMajorant A B 0 n
      calc
        (1 / T ^ 2) * (∫ y : ℝ in (0 : ℝ)..1, ‖D y‖) ≤
            (1 / T ^ 2) *
              (∫ y : ℝ in (-1 : ℝ)..1, ‖D y‖) :=
          mul_le_mul_of_nonneg_left hupperFull (by positivity)
        _ ≤ (1 / T ^ 2) * L :=
          mul_le_mul_of_nonneg_left hfullL (by positivity)
        _ ≤ suzukiXiWeilVerticalExplicitMajorant A B 0 n := by
          unfold suzukiXiWeilVerticalExplicitMajorant
          change (1 / T ^ 2) * L ≤
            2 * ((2 * (Real.exp |(0 : ℝ)| + 1) / T ^ 2) * L)
          rw [abs_zero, Real.exp_zero]
          have hx : 0 ≤ (1 / T ^ 2) * L :=
            mul_nonneg (by positivity) hL
          calc
            (1 / T ^ 2) * L ≤ 8 * ((1 / T ^ 2) * L) := by
              linarith
            _ = 2 * ((2 * (1 + 1) / T ^ 2) * L) := by ring
  · exact tendsto_suzukiXiWeilVerticalExplicitMajorant_zero
      hA hThreeHalves hB 0

/-- After its dominant `-(2 / T)` real logarithmic-derivative term is
removed, the integrated folded kernel tends to zero. -/
theorem tendsto_xiSpectralBlaschkeRightFoldedVerticalKernel_re_add_main_quantitative_zero
    {v : ℝ} (hv : 1 < v) :
    Tendsto
      (fun n : ℕ ↦
        (∫ y : ℝ in (0 : ℝ)..1,
          (xiSpectralBlaschkeRightFoldedVerticalKernel
            (quantitativeSpectralBoundaryTruncation n)
            ((v : ℂ) * Complex.I) y).re) +
          (2 / quantitativeSpectralBoundaryTruncation n) *
            (∫ y : ℝ in (0 : ℝ)..1,
              (xiSpectralNegativeLogDerivative
                ((quantitativeSpectralBoundaryTruncation n : ℂ) +
                  (y : ℂ) * Complex.I)).re))
      atTop (nhds 0) := by
  let e : ℕ → ℝ := fun n ↦
    (1 / quantitativeSpectralBoundaryTruncation n ^ 2) *
      (∫ y : ℝ in (0 : ℝ)..1,
        ‖xiSpectralNegativeLogDerivative
          ((quantitativeSpectralBoundaryTruncation n : ℂ) +
            (y : ℂ) * Complex.I)‖)
  let M : ℕ → ℝ := fun n ↦
    (2 * v / quantitativeSpectralBoundaryTruncation n ^ 2) *
      (∫ y : ℝ in (0 : ℝ)..1,
        ‖xiSpectralNegativeLogDerivative
          ((quantitativeSpectralBoundaryTruncation n : ℂ) +
            (y : ℂ) * Complex.I)‖)
  have he : Tendsto e atTop (nhds 0) := by
    simpa [e] using
      tendsto_inv_sq_mul_intervalIntegral_norm_xiSpectralNegativeLogDerivative_quantitative_upper_zero
  have hM : Tendsto M atTop (nhds 0) := by
    have heq : M = fun n ↦ (2 * v) * e n := by
      funext n
      dsimp [M, e]
      ring
    rw [heq]
    simpa using tendsto_const_nhds.mul he
  refine squeeze_zero_norm' ?_ hM
  exact Eventually.of_forall fun n ↦ by
    simpa [M, Real.norm_eq_abs] using
      abs_intervalIntegral_xiSpectralBlaschkeRightFoldedVerticalKernel_re_add_main_quantitative_le
        hv n

/-- The zero-inner-height static vertical boundary is asymptotic to
`-(4 / T)` times the upper-half integral of the real spectral-xi negative
logarithmic derivative.  This is the surviving signed main term; all
absolute-value errors have been proved to vanish. -/
theorem tendsto_neg_I_mul_xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_imaginary_add_logDerivative_main_quantitative_zero
    {v : ℝ} (hv : 1 < v) :
    Tendsto
      (fun n : ℕ ↦
        -Complex.I *
            xiSpectralBlaschkeSignedVerticalRemainderWindow
              (quantitativeSpectralBoundaryTruncation n) 0
              ((v : ℂ) * Complex.I) +
          (((4 / quantitativeSpectralBoundaryTruncation n) *
            (∫ y : ℝ in (0 : ℝ)..1,
              (xiSpectralNegativeLogDerivative
                ((quantitativeSpectralBoundaryTruncation n : ℂ) +
                  (y : ℂ) * Complex.I)).re) : ℝ) : ℂ))
      atTop (nhds 0) := by
  let E : ℕ → ℝ := fun n ↦
    (∫ y : ℝ in (0 : ℝ)..1,
      (xiSpectralBlaschkeRightFoldedVerticalKernel
        (quantitativeSpectralBoundaryTruncation n)
        ((v : ℂ) * Complex.I) y).re) +
      (2 / quantitativeSpectralBoundaryTruncation n) *
        (∫ y : ℝ in (0 : ℝ)..1,
          (xiSpectralNegativeLogDerivative
            ((quantitativeSpectralBoundaryTruncation n : ℂ) +
              (y : ℂ) * Complex.I)).re)
  have hE : Tendsto E atTop (nhds 0) := by
    simpa [E] using
      tendsto_xiSpectralBlaschkeRightFoldedVerticalKernel_re_add_main_quantitative_zero
        hv
  have htwoE : Tendsto (fun n ↦ 2 * E n) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hE
  have hreal : Tendsto
      (fun n : ℕ ↦
        2 * (∫ y : ℝ in (0 : ℝ)..1,
          (xiSpectralBlaschkeRightFoldedVerticalKernel
            (quantitativeSpectralBoundaryTruncation n)
            ((v : ℂ) * Complex.I) y).re) +
          (4 / quantitativeSpectralBoundaryTruncation n) *
            (∫ y : ℝ in (0 : ℝ)..1,
              (xiSpectralNegativeLogDerivative
                ((quantitativeSpectralBoundaryTruncation n : ℂ) +
                  (y : ℂ) * Complex.I)).re))
      atTop (nhds 0) := by
    have heq : (fun n : ℕ ↦
        2 * (∫ y : ℝ in (0 : ℝ)..1,
          (xiSpectralBlaschkeRightFoldedVerticalKernel
            (quantitativeSpectralBoundaryTruncation n)
            ((v : ℂ) * Complex.I) y).re) +
          (4 / quantitativeSpectralBoundaryTruncation n) *
            (∫ y : ℝ in (0 : ℝ)..1,
              (xiSpectralNegativeLogDerivative
                ((quantitativeSpectralBoundaryTruncation n : ℂ) +
                  (y : ℂ) * Complex.I)).re)) =
        fun n ↦ 2 * E n := by
      funext n
      dsimp [E]
      ring
    rw [heq]
    exact htwoE
  have hcomplex := hreal.ofReal
  have heq : (fun n : ℕ ↦
      -Complex.I *
          xiSpectralBlaschkeSignedVerticalRemainderWindow
            (quantitativeSpectralBoundaryTruncation n) 0
            ((v : ℂ) * Complex.I) +
        (((4 / quantitativeSpectralBoundaryTruncation n) *
          (∫ y : ℝ in (0 : ℝ)..1,
            (xiSpectralNegativeLogDerivative
              ((quantitativeSpectralBoundaryTruncation n : ℂ) +
                (y : ℂ) * Complex.I)).re) : ℝ) : ℂ)) =
      fun n ↦
        ((2 * (∫ y : ℝ in (0 : ℝ)..1,
            (xiSpectralBlaschkeRightFoldedVerticalKernel
              (quantitativeSpectralBoundaryTruncation n)
              ((v : ℂ) * Complex.I) y).re) +
          (4 / quantitativeSpectralBoundaryTruncation n) *
            (∫ y : ℝ in (0 : ℝ)..1,
              (xiSpectralNegativeLogDerivative
                ((quantitativeSpectralBoundaryTruncation n : ℂ) +
                  (y : ℂ) * Complex.I)).re) : ℝ) : ℂ) := by
    funext n
    have hT : 0 ≤ quantitativeSpectralBoundaryTruncation n :=
      ((Nat.cast_nonneg n).trans_lt
        (quantitativeSpectralBoundaryTruncation_spec n).1).le
    rw [neg_I_mul_xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_imaginary
      hv hT (quantitativeSpectralBoundaryTruncation_zeroFree n)]
    push_cast
    ring
  rw [heq]
  simpa using hcomplex

end

end RiemannGaussian
