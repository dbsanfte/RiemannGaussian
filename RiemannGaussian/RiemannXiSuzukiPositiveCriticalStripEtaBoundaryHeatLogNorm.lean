import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaBoundaryHeatFluxDiagonal

/-!
# Logarithmic radial transport of the paired-eta heat flux

The divisor-preserving paired-eta detector is expressed upstream as a radial
flux of the singular quotient `D / E`. This module removes that quotient from
the finite-circle integrand without erasing its divisor mass.

On every zero-free circle in the positive eta half-plane, Lean differentiates
the squared norm of the literal convergent paired-eta series and proves

`d/dr log |E(rho + r * exp (I * theta))|^2
  = 2 * Re (exp (I * theta) * D / E)`.

Consequently the normalized heat-weighted eta flux is exactly a scaled
interval integral of this radial logarithmic derivative. The refined
diagonal radii from the preceding module keep every selected circle in the
valid zero-free region and in the simultaneous `L¹` regime. The resulting
single sequence of genuine logarithmic-variation integrals converges to
`2 * pi` times the complete boundary-heat detector.

This identity does not estimate the logarithmic variation. It replaces the
open quotient cancellation problem by an exact transport problem for the log
norm of an absolutely convergent arithmetic series while retaining every
zero contribution.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Away from the paired-eta divisor in the positive half-plane, the radial
derivative of its log squared norm is twice the radial component of the
literal convergent logarithmic quotient. -/
theorem hasDerivAt_log_pairedEtaCoreNormSq_circleRadius
    {rho : ℂ} {r theta : ℝ}
    (hs : 0 < (circleMap rho r theta).re)
    (hne : pairedEtaCore (circleMap rho r theta) ≠ 0) :
    HasDerivAt
      (fun u : ℝ =>
        Real.log (pairedEtaCoreNormSq (circleMap rho u theta)))
      (2 * (Complex.exp ((theta : ℂ) * Complex.I) *
        (pairedEtaArithmeticDerivativeValue (circleMap rho r theta) /
          pairedEtaCore (circleMap rho r theta))).re)
      r := by
  let s : ℂ := circleMap rho r theta
  let e : ℂ := Complex.exp ((theta : ℂ) * Complex.I)
  let g : ℝ → ℂ := fun u => pairedEtaCore (circleMap rho u theta)
  let affine : ℂ → ℂ := fun z => rho + z * e
  have haffine : HasDerivAt affine e (r : ℂ) := by
    simpa [affine] using
      ((hasDerivAt_id (x := (r : ℂ))).mul_const e).const_add rho
  have hsAffine : affine (r : ℂ) = s := by
    simp [affine, s, e, circleMap]
  have heta := hasDerivAt_pairedEtaCore_arithmeticDerivativeValue hs
  have hcomp : HasDerivAt (pairedEtaCore ∘ affine)
      (pairedEtaArithmeticDerivativeValue s * e) (r : ℂ) := by
    exact heta.comp_of_eq (r : ℂ) haffine hsAffine.symm
  have hg : HasDerivAt g
      (pairedEtaArithmeticDerivativeValue s * e) r := by
    simpa [g, affine, s, e, circleMap] using hcomp.comp_ofReal
  have hnorm := hg.norm_sq
  have hnorm' : HasDerivAt
      (fun u : ℝ => pairedEtaCoreNormSq (circleMap rho u theta))
      (2 * (pairedEtaArithmeticDerivativeValue s * e *
        starRingEnd ℂ (pairedEtaCore s)).re) r := by
    convert hnorm using 1
    · funext u
      simp [pairedEtaCoreNormSq, g, Complex.normSq_eq_norm_sq]
    · simp only [Complex.inner, g]
      ring
  have hnormNe : pairedEtaCoreNormSq s ≠ 0 := by
    intro hzero
    apply hne
    simpa [pairedEtaCoreNormSq, s] using
      Complex.normSq_eq_zero.mp hzero
  have hlog := (Real.hasDerivAt_log hnormNe).comp r hnorm'
  change HasDerivAt
      (fun u : ℝ =>
        Real.log (pairedEtaCoreNormSq (circleMap rho u theta)))
      ((pairedEtaCoreNormSq s)⁻¹ *
        (2 * (pairedEtaArithmeticDerivativeValue s * e *
          starRingEnd ℂ (pairedEtaCore s)).re)) r at hlog
  have hnormSqNe : Complex.normSq (pairedEtaCore s) ≠ 0 := by
    simpa [pairedEtaCoreNormSq] using hnormNe
  have hderiv :
      2 * (e * (pairedEtaArithmeticDerivativeValue s /
          pairedEtaCore s)).re =
        (pairedEtaCoreNormSq s)⁻¹ *
          (2 * (pairedEtaArithmeticDerivativeValue s * e *
            starRingEnd ℂ (pairedEtaCore s)).re) := by
    rw [Complex.mul_re, pairedEtaArithmeticQuotient_re,
      pairedEtaArithmeticQuotient_im]
    unfold pairedEtaLogDerivativeRealNumerator
      pairedEtaLogDerivativeImaginaryNumerator pairedEtaCoreNormSq
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im]
    field_simp [hnormSqNe]
    ring
  rw [show Complex.exp ((theta : ℂ) * Complex.I) = e by rfl]
  rw [show circleMap rho r theta = s by rfl]
  rw [hderiv]
  exact hlog

/-- The heat-weighted radial derivative of the log squared norm of the
literal paired-eta series on one circle. -/
def pairedEtaBoundaryHeatLogNormRadialIntegrand
    (x tau : ℝ) (rho : NontrivialZetaZero) (r theta : ℝ) : ℝ :=
  (suzukiChebyshevLaplaceBoundaryHeatKernel x tau
      (circleMap rho.1 r theta - 1 / 2)).re *
    deriv
      (fun u : ℝ =>
        Real.log
          (pairedEtaCoreNormSq (circleMap rho.1 u theta))) r

/-- The logarithmic radial flux is the circle integral of the log-norm
radial derivative with the exact `r / 2` scaling. -/
def pairedEtaBoundaryHeatLogNormRadialFlux
    (x tau : ℝ) (rho : NontrivialZetaZero) (r : ℝ) : ℝ :=
  (r / 2) * ∫ theta : ℝ in 0..2 * Real.pi,
    pairedEtaBoundaryHeatLogNormRadialIntegrand x tau rho r theta

/-- Pointwise on a valid circle, the scaled log-norm radial derivative is
exactly the normalized-bilinear paired-eta heat-flux integrand. -/
theorem pairedEtaBoundaryHeatLogNormRadialIntegrand_scaled_eq_normalized
    (x tau : ℝ) (rho : NontrivialZetaZero) {r theta : ℝ}
    (hs : 0 < (circleMap rho.1 r theta).re)
    (hne : pairedEtaCore (circleMap rho.1 r theta) ≠ 0) :
    (r / 2) *
        pairedEtaBoundaryHeatLogNormRadialIntegrand
          x tau rho r theta =
      let s := circleMap rho.1 r theta
      (suzukiChebyshevLaplaceBoundaryHeatKernel x tau
          (s - 1 / 2)).re *
        ((circleMap 0 r theta).re *
            (pairedEtaLogDerivativeRealNumerator s /
              pairedEtaCoreNormSq s) -
          (circleMap 0 r theta).im *
            (pairedEtaLogDerivativeImaginaryNumerator s /
              pairedEtaCoreNormSq s)) := by
  unfold pairedEtaBoundaryHeatLogNormRadialIntegrand
  rw [(hasDerivAt_log_pairedEtaCoreNormSq_circleRadius hs hne).deriv]
  dsimp only
  rw [← pairedEtaArithmeticQuotient_re,
    ← pairedEtaArithmeticQuotient_im]
  rw [circleMap_zero]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- On any circle with legitimate positive-half-plane and zero-free
geometry, the logarithmic radial flux is exactly the normalized-bilinear
paired-eta heat flux. -/
theorem pairedEtaBoundaryHeatLogNormRadialFlux_eq_normalized
    (x tau : ℝ) (rho : NontrivialZetaZero) {r : ℝ}
    (hgeometry : ∀ theta : ℝ,
      0 < (circleMap rho.1 r theta).re ∧
        pairedEtaCore (circleMap rho.1 r theta) ≠ 0) :
    pairedEtaBoundaryHeatLogNormRadialFlux x tau rho r =
      pairedEtaBoundaryHeatNormalizedNumeratorRadialFlux
        x tau rho r := by
  unfold pairedEtaBoundaryHeatLogNormRadialFlux
    pairedEtaBoundaryHeatNormalizedNumeratorRadialFlux
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro theta _
  exact
    pairedEtaBoundaryHeatLogNormRadialIntegrand_scaled_eq_normalized
      x tau rho (hgeometry theta).1 (hgeometry theta).2

/-- If the normalized eta heat-flux integrand is `L¹` on a positive
zero-free circle, then its log-norm radial-derivative representation is also
genuinely `L¹` there. -/
theorem intervalIntegrable_pairedEtaBoundaryHeatLogNormRadialIntegrand_of_normalized
    (x tau : ℝ) (rho : NontrivialZetaZero) {r : ℝ}
    (hr : 0 < r)
    (hgeometry : ∀ theta : ℝ,
      0 < (circleMap rho.1 r theta).re ∧
        pairedEtaCore (circleMap rho.1 r theta) ≠ 0)
    (hintegrable : IntervalIntegrable
      (fun theta : ℝ =>
        let s := circleMap rho.1 r theta
        (suzukiChebyshevLaplaceBoundaryHeatKernel x tau
            (s - 1 / 2)).re *
          ((circleMap 0 r theta).re *
              (pairedEtaLogDerivativeRealNumerator s /
                pairedEtaCoreNormSq s) -
            (circleMap 0 r theta).im *
              (pairedEtaLogDerivativeImaginaryNumerator s /
                pairedEtaCoreNormSq s)))
      volume 0 (2 * Real.pi)) :
    IntervalIntegrable
      (pairedEtaBoundaryHeatLogNormRadialIntegrand x tau rho r)
      volume 0 (2 * Real.pi) := by
  have hscaled := hintegrable.const_mul (2 / r)
  apply hscaled.congr
  intro theta _
  have hpoint :=
    pairedEtaBoundaryHeatLogNormRadialIntegrand_scaled_eq_normalized
      x tau rho (hgeometry theta).1 (hgeometry theta).2
  dsimp only at hpoint ⊢
  calc
    (2 / r) *
        ((suzukiChebyshevLaplaceBoundaryHeatKernel x tau
            (circleMap rho.1 r theta - 1 / 2)).re *
          ((circleMap 0 r theta).re *
              (pairedEtaLogDerivativeRealNumerator
                  (circleMap rho.1 r theta) /
                pairedEtaCoreNormSq (circleMap rho.1 r theta)) -
            (circleMap 0 r theta).im *
              (pairedEtaLogDerivativeImaginaryNumerator
                  (circleMap rho.1 r theta) /
                pairedEtaCoreNormSq (circleMap rho.1 r theta)))) =
        (2 / r) * ((r / 2) *
          pairedEtaBoundaryHeatLogNormRadialIntegrand
            x tau rho r theta) := by
      rw [hpoint]
    _ = pairedEtaBoundaryHeatLogNormRadialIntegrand
          x tau rho r theta := by
      field_simp [hr.ne']

/-- The finite-window sum of heat-weighted paired-eta log-norm radial
fluxes at one common radius. -/
def pairedEtaBoundaryHeatLogNormRadialFluxWindow
    (x tau T r : ℝ) : ℝ :=
  ∑ rho ∈ spectralUpperZetaZeroWindow T,
    pairedEtaBoundaryHeatLogNormRadialFlux x tau rho r

/-- Under simultaneous valid circle geometry, the finite logarithmic-
variation window is exactly the normalized-bilinear eta flux window. -/
theorem pairedEtaBoundaryHeatLogNormRadialFluxWindow_eq_normalized
    (x tau T : ℝ) {r : ℝ}
    (hgeometry : ∀ rho ∈ spectralUpperZetaZeroWindow T, ∀ theta : ℝ,
      0 < (circleMap rho.1 r theta).re ∧
        pairedEtaCore (circleMap rho.1 r theta) ≠ 0) :
    pairedEtaBoundaryHeatLogNormRadialFluxWindow x tau T r =
      pairedEtaBoundaryHeatNormalizedNumeratorRadialFluxWindow
        x tau T r := by
  unfold pairedEtaBoundaryHeatLogNormRadialFluxWindow
    pairedEtaBoundaryHeatNormalizedNumeratorRadialFluxWindow
  apply Finset.sum_congr rfl
  intro rho hrho
  exact pairedEtaBoundaryHeatLogNormRadialFlux_eq_normalized
    x tau rho (hgeometry rho hrho)

/-- At every diagonal stage, each selected logarithmic radial-derivative
integrand is genuinely interval integrable. -/
theorem intervalIntegrable_pairedEtaBoundaryHeatLogNormRadialIntegrand_diagonal
    (x tau : ℝ) (n : ℕ) :
    ∀ rho ∈ spectralUpperZetaZeroWindow (n : ℝ),
      IntervalIntegrable
        (pairedEtaBoundaryHeatLogNormRadialIntegrand x tau rho
          (pairedEtaBoundaryHeatFluxDiagonalRadius x tau n))
        volume 0 (2 * Real.pi) := by
  intro rho hrho
  have hspec := pairedEtaBoundaryHeatFluxDiagonalRadius_spec x tau n
  exact
    intervalIntegrable_pairedEtaBoundaryHeatLogNormRadialIntegrand_of_normalized
      x tau rho hspec.1 (hspec.2.2.2.2 rho hrho)
        (hspec.2.2.2.1 rho hrho)

/-- A single sequence of genuine finite `L¹` log-norm radial-variation
integrals of the convergent paired-eta series converges to `2 * pi` times the
complete fixed-time boundary-heat detector. -/
theorem tendsto_pairedEtaBoundaryHeatLogNormRadialFluxDiagonal
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun n : ℕ =>
        pairedEtaBoundaryHeatLogNormRadialFluxWindow
          x tau (n : ℝ)
            (pairedEtaBoundaryHeatFluxDiagonalRadius x tau n))
      atTop
      (nhds (2 * Real.pi *
        riemannXiUpperHyperbolicBoundaryHeatTotal x tau)) := by
  have hflux :=
    tendsto_pairedEtaBoundaryHeatNormalizedNumeratorRadialFluxDiagonal
      x htau
  apply hflux.congr'
  exact Eventually.of_forall fun n =>
    (pairedEtaBoundaryHeatLogNormRadialFluxWindow_eq_normalized
      x tau (n : ℝ)
        (pairedEtaBoundaryHeatFluxDiagonalRadius_spec
          x tau n).2.2.2.2).symm

end
end RiemannGaussian
