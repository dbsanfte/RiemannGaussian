import RiemannGaussian.RiemannXiSuzukiSpectralStaticContourCancellation

/-!
# Endpoint form of the static-contour main term

This module identifies the real part of the spectral-xi negative logarithmic
derivative on a zero-free vertical line as the derivative of `log |xi|`.
The fundamental theorem of calculus turns the remaining signed main integral
into an exact endpoint difference.  Functional-equation and conjugation
symmetry then place those endpoints at completed-zeta coordinates
`3/2 + I*T` and `1/2 + I*T`.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology
  RealInnerProductSpace

namespace RiemannGaussian

noncomputable section

/-- The real vertical derivative of spectral xi is `I` times its complex
derivative. -/
theorem hasDerivAt_riemannXiSpectral_vertical (T y : ℝ) :
    HasDerivAt
      (fun u : ℝ ↦ riemannXiSpectral
        ((T : ℂ) + (u : ℂ) * Complex.I))
      (Complex.I * deriv riemannXiSpectral
        ((T : ℂ) + (y : ℂ) * Complex.I)) y := by
  let w : ℂ := (T : ℂ) + (y : ℂ) * Complex.I
  let a : ℂ → ℂ := fun u ↦ (T : ℂ) + u * Complex.I
  have ha : HasDerivAt a Complex.I (y : ℂ) := by
    simpa [a] using
      ((hasDerivAt_id (𝕜 := ℂ) (y : ℂ)).mul_const Complex.I).const_add
        (T : ℂ)
  have hf : HasDerivAt riemannXiSpectral
      (deriv riemannXiSpectral w) w :=
    (differentiable_riemannXiSpectral w).hasDerivAt
  have hcomp : HasDerivAt (riemannXiSpectral ∘ a)
      (deriv riemannXiSpectral w * Complex.I) (y : ℂ) := by
    simpa [w, a] using hf.comp (y : ℂ) ha
  have hreal := hcomp.comp_ofReal
  simpa only [Function.comp_apply, a, w, mul_comm] using hreal

/-- Away from a spectral xi zero, the vertical derivative is the negative
spectral logarithmic derivative times spectral xi itself. -/
theorem hasDerivAt_riemannXiSpectral_vertical_eq_logDerivative
    {T y : ℝ}
    (hne : riemannXiSpectral
      ((T : ℂ) + (y : ℂ) * Complex.I) ≠ 0) :
    HasDerivAt
      (fun u : ℝ ↦ riemannXiSpectral
        ((T : ℂ) + (u : ℂ) * Complex.I))
      (xiSpectralNegativeLogDerivative
          ((T : ℂ) + (y : ℂ) * Complex.I) *
        riemannXiSpectral
          ((T : ℂ) + (y : ℂ) * Complex.I)) y := by
  have hcurve := hasDerivAt_riemannXiSpectral_vertical T y
  apply hcurve.congr_deriv
  rw [xiSpectralNegativeLogDerivative_eq_I_mul_logDeriv,
    logDeriv_apply]
  have hne' : riemannXiSpectral
      ((T : ℂ) + Complex.I * (y : ℂ)) ≠ 0 := by
    simpa [mul_comm] using hne
  field_simp [hne']

/-- Logarithmic modulus of spectral xi along the right vertical line. -/
def xiSpectralVerticalLogNorm (T y : ℝ) : ℝ :=
  Real.log ‖riemannXiSpectral
    ((T : ℂ) + (y : ℂ) * Complex.I)‖

/-- On a zero-free vertical line, the derivative of `log |xi|` is the real
part of the spectral-xi negative logarithmic derivative. -/
theorem hasDerivAt_xiSpectralVerticalLogNorm
    {T y : ℝ}
    (hne : riemannXiSpectral
      ((T : ℂ) + (y : ℂ) * Complex.I) ≠ 0) :
    HasDerivAt (xiSpectralVerticalLogNorm T)
      (xiSpectralNegativeLogDerivative
        ((T : ℂ) + (y : ℂ) * Complex.I)).re y := by
  let g : ℝ → ℂ := fun u ↦ riemannXiSpectral
    ((T : ℂ) + (u : ℂ) * Complex.I)
  let D : ℂ := xiSpectralNegativeLogDerivative
    ((T : ℂ) + (y : ℂ) * Complex.I)
  let q : ℝ → ℝ := fun u ↦ ‖g u‖ ^ 2
  have hg : HasDerivAt g (D * g y) y := by
    simpa [g, D] using
      hasDerivAt_riemannXiSpectral_vertical_eq_logDerivative hne
  have hinner : inner ℝ (g y) (D * g y) = q y * D.re := by
    rw [Complex.inner]
    dsimp [q]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [mul_re, mul_im, conj_re, conj_im]
    ring
  have hq : HasDerivAt q (2 * q y * D.re) y := by
    have hraw := hg.norm_sq
    simpa [q, hinner, mul_assoc] using hraw
  have hqpos : 0 < q y := by
    dsimp [q, g]
    exact sq_pos_of_pos (norm_pos_iff.mpr hne)
  have hlog := hq.log hqpos.ne'
  have hhalf := hlog.const_mul (1 / 2 : ℝ)
  have hhalf' : HasDerivAt
      (fun u ↦ (1 / 2 : ℝ) * Real.log (q u)) D.re y := by
    apply hhalf.congr_deriv
    field_simp [hqpos.ne']
  have heq : (fun u ↦ (1 / 2 : ℝ) * Real.log (q u)) =
      xiSpectralVerticalLogNorm T := by
    funext u
    simp [q, g, xiSpectralVerticalLogNorm, Real.log_pow]
  rw [← heq]
  exact hhalf'

/-- The signed real logarithmic-derivative integral on a quantitative
zero-free segment is exactly the endpoint log-modulus difference. -/
theorem intervalIntegral_xiSpectralNegativeLogDerivative_re_quantitative_eq_logNorm_sub
    (n : ℕ) :
    (∫ y : ℝ in (0 : ℝ)..1,
      (xiSpectralNegativeLogDerivative
        ((quantitativeSpectralBoundaryTruncation n : ℂ) +
          (y : ℂ) * Complex.I)).re) =
      xiSpectralVerticalLogNorm
          (quantitativeSpectralBoundaryTruncation n) 1 -
        xiSpectralVerticalLogNorm
          (quantitativeSpectralBoundaryTruncation n) 0 := by
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let D : ℝ → ℂ := fun y ↦ xiSpectralNegativeLogDerivative
    ((T : ℂ) + (y : ℂ) * Complex.I)
  have hT : 0 < T :=
    (Nat.cast_nonneg n).trans_lt
      (by simpa [T] using (quantitativeSpectralBoundaryTruncation_spec n).1)
  have hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T := by
    simpa [T] using quantitativeSpectralBoundaryTruncation_zeroFree n
  have hDfull : IntervalIntegrable D volume (-1) 1 := by
    simpa [D, T] using
      intervalIntegrable_xiSpectralNegativeLogDerivative_quantitative n
  have hDupper : IntervalIntegrable D volume 0 1 :=
    hDfull.mono_set (by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
        uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      exact Icc_subset_Icc (by norm_num) le_rfl)
  have hDre : IntervalIntegrable (fun y ↦ (D y).re) volume 0 1 :=
    ⟨by
      simpa [Function.comp_def] using
        Complex.reCLM.integrableOn_comp hDupper.1,
    by simp⟩
  have hderiv (y : ℝ) (_hy : y ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt (xiSpectralVerticalLogNorm T) (D y).re y := by
    apply hasDerivAt_xiSpectralVerticalLogNorm
    apply riemannXiSpectral_ne_zero_of_abs_re_ne hboundary
    simp [abs_of_pos hT]
  simpa [T, D] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hDre

/-- The lower vertical endpoint is completed xi at `1/2 + I*T`. -/
theorem xiSpectralVerticalLogNorm_zero (T : ℝ) :
    xiSpectralVerticalLogNorm T 0 =
      Real.log ‖riemannXi
        (((1 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I)‖ := by
  unfold xiSpectralVerticalLogNorm riemannXiSpectral
    completedSpectralCoordinate
  rw [show
      (1 / 2 : ℂ) + Complex.I *
          ((T : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) =
        (((1 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I) by
      push_cast
      ring]

/-- Functional-equation and conjugation symmetry move the upper vertical
endpoint to completed xi at `3/2 + I*T`. -/
theorem xiSpectralVerticalLogNorm_one (T : ℝ) :
    xiSpectralVerticalLogNorm T 1 =
      Real.log ‖riemannXi
        (((3 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I)‖ := by
  let slow : ℂ := ((-1 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I
  let shigh : ℂ := ((3 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I
  have hspectral : completedSpectralCoordinate
      ((T : ℂ) + ((1 : ℝ) : ℂ) * Complex.I) = slow := by
    dsimp [slow, completedSpectralCoordinate]
    apply Complex.ext
    · norm_num
    · simp
  have hreflect : 1 - slow = starRingEnd ℂ shigh := by
    dsimp [slow, shigh]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  unfold xiSpectralVerticalLogNorm riemannXiSpectral
  rw [hspectral, ← riemannXi_one_sub slow, hreflect,
    riemannXi_conj]
  simp [shigh]

/-- The signed real logarithmic-derivative integral is the completed-xi
log-modulus difference between the safe line and the critical line. -/
theorem intervalIntegral_xiSpectralNegativeLogDerivative_re_quantitative_eq_completedXi_logNorm_sub
    (n : ℕ) :
    (∫ y : ℝ in (0 : ℝ)..1,
      (xiSpectralNegativeLogDerivative
        ((quantitativeSpectralBoundaryTruncation n : ℂ) +
          (y : ℂ) * Complex.I)).re) =
      Real.log ‖riemannXi
          (((3 / 2 : ℝ) : ℂ) +
            (quantitativeSpectralBoundaryTruncation n : ℂ) * Complex.I)‖ -
        Real.log ‖riemannXi
          (((1 / 2 : ℝ) : ℂ) +
            (quantitativeSpectralBoundaryTruncation n : ℂ) * Complex.I)‖ := by
  rw [intervalIntegral_xiSpectralNegativeLogDerivative_re_quantitative_eq_logNorm_sub,
    xiSpectralVerticalLogNorm_one,
    xiSpectralVerticalLogNorm_zero]

/-- The static vertical boundary is asymptotic to the negative of its
spectral endpoint log-modulus main term. -/
theorem tendsto_neg_I_mul_xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_imaginary_add_logNormEndpoint_main_quantitative_zero
    {v : ℝ} (hv : 1 < v) :
    Tendsto
      (fun n : ℕ ↦
        -Complex.I *
            xiSpectralBlaschkeSignedVerticalRemainderWindow
              (quantitativeSpectralBoundaryTruncation n) 0
              ((v : ℂ) * Complex.I) +
          (((4 / quantitativeSpectralBoundaryTruncation n) *
            (xiSpectralVerticalLogNorm
                (quantitativeSpectralBoundaryTruncation n) 1 -
              xiSpectralVerticalLogNorm
                (quantitativeSpectralBoundaryTruncation n) 0) : ℝ) : ℂ))
      atTop (nhds 0) := by
  simpa only [
    intervalIntegral_xiSpectralNegativeLogDerivative_re_quantitative_eq_logNorm_sub]
    using
      tendsto_neg_I_mul_xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_imaginary_add_logDerivative_main_quantitative_zero
        hv

/-- In completed-zeta coordinates, the static vertical boundary is
asymptotic to `-(4 / T)` times the safe-line minus critical-line log-modulus
difference.  Proving this difference is `o(T)` is the remaining vertical
cancellation obligation. -/
theorem tendsto_neg_I_mul_xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_imaginary_add_completedXi_logNorm_main_quantitative_zero
    {v : ℝ} (hv : 1 < v) :
    Tendsto
      (fun n : ℕ ↦
        -Complex.I *
            xiSpectralBlaschkeSignedVerticalRemainderWindow
              (quantitativeSpectralBoundaryTruncation n) 0
              ((v : ℂ) * Complex.I) +
          (((4 / quantitativeSpectralBoundaryTruncation n) *
            (Real.log ‖riemannXi
                (((3 / 2 : ℝ) : ℂ) +
                  (quantitativeSpectralBoundaryTruncation n : ℂ) *
                    Complex.I)‖ -
              Real.log ‖riemannXi
                (((1 / 2 : ℝ) : ℂ) +
                  (quantitativeSpectralBoundaryTruncation n : ℂ) *
                    Complex.I)‖) : ℝ) : ℂ))
      atTop (nhds 0) := by
  simpa only [
    intervalIntegral_xiSpectralNegativeLogDerivative_re_quantitative_eq_completedXi_logNorm_sub]
    using
      tendsto_neg_I_mul_xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_imaginary_add_logDerivative_main_quantitative_zero
        hv

end

end RiemannGaussian
