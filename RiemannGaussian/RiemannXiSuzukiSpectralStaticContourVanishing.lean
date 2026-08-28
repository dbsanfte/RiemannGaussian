import RiemannGaussian.RiemannXiSuzukiSpectralStaticContourCriticalZetaSublinear

/-!
# Vanishing of the selected static signed vertical remainder

The checked static-contour reduction expresses the selected signed vertical
remainder, after multiplication by `-I`, as the negative of a normalized
critical-zeta negative logarithm plus a term tending to zero.  The newly
proved `o(T)` critical-zeta estimate makes that correction vanish.  This
module removes it and proves that the signed vertical remainder itself tends
to zero at every fixed purely imaginary observation point above the strip.
-/

open Complex Filter Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The normalized critical-zeta negative-log correction in the static
contour theorem tends to zero as a complex-valued sequence. -/
lemma tendsto_criticalZeta_log_negativePart_main_quantitative_zero :
    Tendsto
      (fun n : ℕ =>
        (((4 / quantitativeSpectralBoundaryTruncation n) *
          max 0 (-Real.log ‖riemannZeta
            (staticContourCriticalEndpoint
              (quantitativeSpectralBoundaryTruncation n))‖) : ℝ) : ℂ))
      atTop (nhds 0) := by
  let T : ℕ → ℝ := quantitativeSpectralBoundaryTruncation
  let N : ℕ → ℝ := fun n =>
    max 0 (-Real.log
      ‖riemannZeta (staticContourCriticalEndpoint (T n))‖)
  have hbase : Tendsto (fun n : ℕ => N n / T n) atTop (nhds 0) := by
    simpa [N, T] using
      tendsto_criticalZeta_log_negativePart_div_quantitative_zero
  have hscaled : Tendsto (fun n : ℕ => 4 * (N n / T n))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hbase
  have hreal : Tendsto (fun n : ℕ => (4 / T n) * N n)
      atTop (nhds 0) := by
    refine hscaled.congr' (Eventually.of_forall fun n => ?_)
    ring
  simpa [N, T] using hreal.ofReal

/-- After multiplication by `-I`, the selected zero-height signed vertical
remainder tends to zero. -/
theorem tendsto_neg_I_mul_xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_imaginary_quantitative_zero
    {v : ℝ} (hv : 1 < v) :
    Tendsto
      (fun n : ℕ =>
        -Complex.I *
          xiSpectralBlaschkeSignedVerticalRemainderWindow
            (quantitativeSpectralBoundaryTruncation n) 0
            ((v : ℂ) * Complex.I))
      atTop (nhds 0) := by
  let V : ℕ → ℂ := fun n =>
    -Complex.I *
      xiSpectralBlaschkeSignedVerticalRemainderWindow
        (quantitativeSpectralBoundaryTruncation n) 0
        ((v : ℂ) * Complex.I)
  let C : ℕ → ℂ := fun n =>
    (((4 / quantitativeSpectralBoundaryTruncation n) *
      max 0 (-Real.log ‖riemannZeta
        (staticContourCriticalEndpoint
          (quantitativeSpectralBoundaryTruncation n))‖) : ℝ) : ℂ)
  have hsum : Tendsto (fun n : ℕ => V n + C n) atTop (nhds 0) := by
    simpa [V, C] using
      tendsto_neg_I_mul_xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_imaginary_add_criticalZeta_log_negativePart_main_quantitative_zero
        hv
  have hcorrection : Tendsto C atTop (nhds 0) := by
    simpa [C] using
      tendsto_criticalZeta_log_negativePart_main_quantitative_zero
  have hdifference : Tendsto
      (fun n : ℕ => (V n + C n) - C n) atTop (nhds 0) := by
    simpa using hsum.sub hcorrection
  refine hdifference.congr' (Eventually.of_forall fun n => ?_)
  dsimp [V, C]
  ring

/-- The selected zero-height signed vertical remainder itself tends to zero
at every fixed purely imaginary observation point above the strip. -/
theorem tendsto_xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_imaginary_quantitative_zero
    {v : ℝ} (hv : 1 < v) :
    Tendsto
      (fun n : ℕ =>
        xiSpectralBlaschkeSignedVerticalRemainderWindow
          (quantitativeSpectralBoundaryTruncation n) 0
          ((v : ℂ) * Complex.I))
      atTop (nhds 0) := by
  have hbase :=
    tendsto_neg_I_mul_xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_imaginary_quantitative_zero
      hv
  have hI : Tendsto (fun _ : ℕ => Complex.I) atTop (nhds Complex.I) :=
    tendsto_const_nhds
  have hscaled := hI.mul hbase
  have hscaledZero : Tendsto
      (fun n : ℕ => Complex.I *
        (-Complex.I *
          xiSpectralBlaschkeSignedVerticalRemainderWindow
            (quantitativeSpectralBoundaryTruncation n) 0
            ((v : ℂ) * Complex.I))) atTop (nhds 0) := by
    simpa only [mul_zero] using hscaled
  refine hscaledZero.congr' (Eventually.of_forall fun n => ?_)
  rw [← mul_assoc, mul_neg, Complex.I_mul_I]
  simp

end

end RiemannGaussian
