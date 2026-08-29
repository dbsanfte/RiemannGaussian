import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFiniteArithmeticFlux

/-!
# Finite logarithmic transport of the paired-eta detector

The preceding module expresses the complete detector as a diagonal limit of
finite paired-eta logarithmic quotients. This module removes those finite
quotients from the selected integrands without taking an infinite-series
limit.

For the finite eta polynomial `E_N` and its explicit derivative `D_N`,
Lean proves on every nonvanishing circle

`d/dr log |E_N(rho + r * exp (I * theta))|^2
  = 2 * Re (exp (I * theta) * D_N / E_N)`.

The selected finite denominators are already proved uniformly nonzero, so the
identity transfers genuine `L¹` integrability and holds simultaneously across
every selected finite window. The resulting single sequence of entirely finite
log-norm radial variations converges to `2 * pi` times the complete detector.

This remains an exact transport and approximation result. It does not assert
the conjecture-strength arithmetic estimate that would force the finite
logarithmic variations to vanish.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The squared complex norm of the finite paired-eta polynomial. -/
def pairedEtaCorePartialSumNormSq (N : ℕ) (s : ℂ) : ℝ :=
  Complex.normSq (pairedEtaCorePartialSum N s)

/-- Termwise differentiation computes the derivative of every finite paired-
eta polynomial exactly. -/
theorem hasDerivAt_pairedEtaCorePartialSum
    (N : ℕ) (s : ℂ) :
    HasDerivAt (pairedEtaCorePartialSum N)
      (pairedEtaCoreDerivativePartialSum N s) s := by
  unfold pairedEtaCorePartialSum pairedEtaCoreDerivativePartialSum
  apply HasDerivAt.fun_sum
  intro n _
  exact hasDerivAt_pairedEtaCoreSummand s n

/-- At a nonzero point of a finite eta polynomial, the radial derivative of
its log squared norm is twice the radial part of its finite logarithmic
quotient. -/
theorem hasDerivAt_log_pairedEtaCorePartialSumNormSq_circleRadius
    {N : ℕ} {rho : ℂ} {r theta : ℝ}
    (hne : pairedEtaCorePartialSum N (circleMap rho r theta) ≠ 0) :
    HasDerivAt
      (fun u : ℝ =>
        Real.log
          (pairedEtaCorePartialSumNormSq N
            (circleMap rho u theta)))
      (2 * (Complex.exp ((theta : ℂ) * Complex.I) *
        pairedEtaArithmeticQuotientPartialSum N
          (circleMap rho r theta)).re)
      r := by
  let s : ℂ := circleMap rho r theta
  let e : ℂ := Complex.exp ((theta : ℂ) * Complex.I)
  let g : ℝ → ℂ := fun u =>
    pairedEtaCorePartialSum N (circleMap rho u theta)
  let affine : ℂ → ℂ := fun z => rho + z * e
  have haffine : HasDerivAt affine e (r : ℂ) := by
    simpa [affine] using
      ((hasDerivAt_id (x := (r : ℂ))).mul_const e).const_add rho
  have hsAffine : affine (r : ℂ) = s := by
    simp [affine, s, e, circleMap]
  have heta := hasDerivAt_pairedEtaCorePartialSum N s
  have hcomp : HasDerivAt (pairedEtaCorePartialSum N ∘ affine)
      (pairedEtaCoreDerivativePartialSum N s * e) (r : ℂ) := by
    exact heta.comp_of_eq (r : ℂ) haffine hsAffine.symm
  have hg : HasDerivAt g
      (pairedEtaCoreDerivativePartialSum N s * e) r := by
    simpa [g, affine, s, e, circleMap] using hcomp.comp_ofReal
  have hnorm := hg.norm_sq
  have hnorm' : HasDerivAt
      (fun u : ℝ =>
        pairedEtaCorePartialSumNormSq N (circleMap rho u theta))
      (2 * (pairedEtaCoreDerivativePartialSum N s * e *
        starRingEnd ℂ (pairedEtaCorePartialSum N s)).re) r := by
    convert hnorm using 1
    · funext u
      simp [pairedEtaCorePartialSumNormSq, g,
        Complex.normSq_eq_norm_sq]
    · simp only [Complex.inner, g]
      ring
  have hnormNe : pairedEtaCorePartialSumNormSq N s ≠ 0 := by
    intro hzero
    apply hne
    simpa [pairedEtaCorePartialSumNormSq, s] using
      Complex.normSq_eq_zero.mp hzero
  have hlog := (Real.hasDerivAt_log hnormNe).comp r hnorm'
  change HasDerivAt
      (fun u : ℝ =>
        Real.log
          (pairedEtaCorePartialSumNormSq N
            (circleMap rho u theta)))
      ((pairedEtaCorePartialSumNormSq N s)⁻¹ *
        (2 * (pairedEtaCoreDerivativePartialSum N s * e *
          starRingEnd ℂ (pairedEtaCorePartialSum N s)).re)) r at hlog
  have hnormSqNe :
      Complex.normSq (pairedEtaCorePartialSum N s) ≠ 0 := by
    simpa [pairedEtaCorePartialSumNormSq] using hnormNe
  have hderiv :
      2 * (e * (pairedEtaCoreDerivativePartialSum N s /
          pairedEtaCorePartialSum N s)).re =
        (pairedEtaCorePartialSumNormSq N s)⁻¹ *
          (2 * (pairedEtaCoreDerivativePartialSum N s * e *
            starRingEnd ℂ (pairedEtaCorePartialSum N s)).re) := by
    unfold pairedEtaCorePartialSumNormSq
    rw [Complex.mul_re, Complex.div_re, Complex.div_im]
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im]
    field_simp [hnormSqNe]
    ring
  rw [show Complex.exp ((theta : ℂ) * Complex.I) = e by rfl]
  rw [show circleMap rho r theta = s by rfl]
  rw [pairedEtaArithmeticQuotientPartialSum, hderiv]
  exact hlog

/-- The heat-weighted radial derivative of the log squared norm of one finite
paired-eta polynomial. -/
def pairedEtaBoundaryHeatFiniteLogNormRadialIntegrand
    (x tau : ℝ) (rho : NontrivialZetaZero) (r : ℝ)
    (N : ℕ) (theta : ℝ) : ℝ :=
  (suzukiChebyshevLaplaceBoundaryHeatKernel x tau
      (circleMap rho.1 r theta - 1 / 2)).re *
    deriv
      (fun u : ℝ =>
        Real.log
          (pairedEtaCorePartialSumNormSq N
            (circleMap rho.1 u theta))) r

/-- The radius-scaled interval integral of one finite eta log-norm radial
integrand. -/
def pairedEtaBoundaryHeatFiniteLogNormRadialFlux
    (x tau : ℝ) (rho : NontrivialZetaZero) (r : ℝ) (N : ℕ) : ℝ :=
  (r / 2) * ∫ theta : ℝ in 0..2 * Real.pi,
    pairedEtaBoundaryHeatFiniteLogNormRadialIntegrand
      x tau rho r N theta

/-- Pointwise off the finite eta divisor, the scaled finite log-norm integrand
is exactly the finite arithmetic quotient integrand. -/
theorem pairedEtaBoundaryHeatFiniteLogNormRadialIntegrand_scaled_eq_arithmetic
    (x tau : ℝ) (rho : NontrivialZetaZero) {r : ℝ} (N : ℕ)
    {theta : ℝ}
    (hne : pairedEtaCorePartialSum N
      (circleMap rho.1 r theta) ≠ 0) :
    (r / 2) *
        pairedEtaBoundaryHeatFiniteLogNormRadialIntegrand
          x tau rho r N theta =
      pairedEtaBoundaryHeatFiniteArithmeticRadialIntegrand
        x tau rho r N theta := by
  unfold pairedEtaBoundaryHeatFiniteLogNormRadialIntegrand
    pairedEtaBoundaryHeatFiniteArithmeticRadialIntegrand
  rw [(hasDerivAt_log_pairedEtaCorePartialSumNormSq_circleRadius
    hne).deriv]
  rw [circleMap_zero]
  unfold pairedEtaArithmeticQuotientPartialSum
  simp only [Complex.mul_re, Complex.mul_im,
    suzukiChebyshevLaplaceBoundaryHeatKernel_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- If the finite eta denominator is nonzero on the compact angular interval,
its log-norm radial flux equals its arithmetic quotient flux exactly. -/
theorem pairedEtaBoundaryHeatFiniteLogNormRadialFlux_eq_arithmetic
    (x tau : ℝ) (rho : NontrivialZetaZero) {r : ℝ} (N : ℕ)
    (hnonzero : ∀ theta ∈ Set.Icc 0 (2 * Real.pi),
      pairedEtaCorePartialSum N (circleMap rho.1 r theta) ≠ 0) :
    pairedEtaBoundaryHeatFiniteLogNormRadialFlux
        x tau rho r N =
      pairedEtaBoundaryHeatFiniteArithmeticRadialFlux
        x tau rho r N := by
  unfold pairedEtaBoundaryHeatFiniteLogNormRadialFlux
    pairedEtaBoundaryHeatFiniteArithmeticRadialFlux
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro theta htheta
  exact
    pairedEtaBoundaryHeatFiniteLogNormRadialIntegrand_scaled_eq_arithmetic
      x tau rho N (hnonzero theta (by
        rw [← uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
        exact htheta))

/-- At positive radius, genuine `L¹` integrability transfers from the finite
arithmetic integrand to its finite log-norm representation. -/
theorem intervalIntegrable_pairedEtaBoundaryHeatFiniteLogNormRadialIntegrand_of_arithmetic
    (x tau : ℝ) (rho : NontrivialZetaZero) {r : ℝ} (N : ℕ)
    (hr : 0 < r)
    (hnonzero : ∀ theta ∈ Set.Icc 0 (2 * Real.pi),
      pairedEtaCorePartialSum N (circleMap rho.1 r theta) ≠ 0)
    (hintegrable : IntervalIntegrable
      (pairedEtaBoundaryHeatFiniteArithmeticRadialIntegrand
        x tau rho r N) volume 0 (2 * Real.pi)) :
    IntervalIntegrable
      (pairedEtaBoundaryHeatFiniteLogNormRadialIntegrand
        x tau rho r N) volume 0 (2 * Real.pi) := by
  have hscaled := hintegrable.const_mul (2 / r)
  apply hscaled.congr
  intro theta htheta
  have hpoint :=
    pairedEtaBoundaryHeatFiniteLogNormRadialIntegrand_scaled_eq_arithmetic
      x tau rho N (hnonzero theta (by
        rw [← uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
        exact uIoc_subset_uIcc htheta))
  calc
    (2 / r) *
        pairedEtaBoundaryHeatFiniteArithmeticRadialIntegrand
          x tau rho r N theta =
      (2 / r) * ((r / 2) *
        pairedEtaBoundaryHeatFiniteLogNormRadialIntegrand
          x tau rho r N theta) := by rw [hpoint]
    _ = pairedEtaBoundaryHeatFiniteLogNormRadialIntegrand
          x tau rho r N theta := by field_simp [hr.ne']

/-- The finite-window sum of finite eta log-norm radial fluxes at one common
radius and arithmetic truncation. -/
def pairedEtaBoundaryHeatFiniteLogNormRadialFluxWindow
    (x tau T r : ℝ) (N : ℕ) : ℝ :=
  ∑ rho ∈ spectralUpperZetaZeroWindow T,
    pairedEtaBoundaryHeatFiniteLogNormRadialFlux
      x tau rho r N

/-- Simultaneous finite-denominator avoidance identifies the complete finite
log-norm window with the corresponding finite arithmetic quotient window. -/
theorem pairedEtaBoundaryHeatFiniteLogNormRadialFluxWindow_eq_arithmetic
    (x tau T : ℝ) {r : ℝ} (N : ℕ)
    (hnonzero : ∀ rho ∈ spectralUpperZetaZeroWindow T,
      ∀ theta ∈ Set.Icc 0 (2 * Real.pi),
        pairedEtaCorePartialSum N (circleMap rho.1 r theta) ≠ 0) :
    pairedEtaBoundaryHeatFiniteLogNormRadialFluxWindow
        x tau T r N =
      pairedEtaBoundaryHeatFiniteArithmeticRadialFluxWindow
        x tau T r N := by
  unfold pairedEtaBoundaryHeatFiniteLogNormRadialFluxWindow
    pairedEtaBoundaryHeatFiniteArithmeticRadialFluxWindow
  apply Finset.sum_congr rfl
  intro rho hrho
  exact pairedEtaBoundaryHeatFiniteLogNormRadialFlux_eq_arithmetic
    x tau rho N (hnonzero rho hrho)

/-- Every log-norm integrand chosen in the finite arithmetic diagonal is
genuinely interval integrable. -/
theorem intervalIntegrable_pairedEtaBoundaryHeatFiniteLogNormRadialIntegrand_diagonal
    (x tau : ℝ) (n : ℕ) :
    ∀ rho ∈ spectralUpperZetaZeroWindow (n : ℝ),
      IntervalIntegrable
        (pairedEtaBoundaryHeatFiniteLogNormRadialIntegrand
          x tau rho (pairedEtaBoundaryHeatFluxDiagonalRadius x tau n)
            (pairedEtaBoundaryHeatFiniteArithmeticDiagonalIndex x tau n))
        volume 0 (2 * Real.pi) := by
  intro rho hrho
  exact
    intervalIntegrable_pairedEtaBoundaryHeatFiniteLogNormRadialIntegrand_of_arithmetic
      x tau rho
        (pairedEtaBoundaryHeatFiniteArithmeticDiagonalIndex x tau n)
        (pairedEtaBoundaryHeatFluxDiagonalRadius_spec x tau n).1
        ((pairedEtaBoundaryHeatFiniteArithmeticDiagonalIndex_spec
          x tau n).2.2.2 rho hrho)
        ((pairedEtaBoundaryHeatFiniteArithmeticDiagonalIndex_spec
          x tau n).2.2.1 rho hrho)

/-- The selected diagonal sequence of entirely finite paired-eta log-norm
radial variations converges to `2 * pi` times the complete fixed-time
boundary-heat detector. -/
theorem tendsto_pairedEtaBoundaryHeatFiniteLogNormRadialFluxDiagonal
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun n : ℕ =>
        pairedEtaBoundaryHeatFiniteLogNormRadialFluxWindow
          x tau (n : ℝ)
            (pairedEtaBoundaryHeatFluxDiagonalRadius x tau n)
            (pairedEtaBoundaryHeatFiniteArithmeticDiagonalIndex x tau n))
      atTop
      (nhds (2 * Real.pi *
        riemannXiUpperHyperbolicBoundaryHeatTotal x tau)) := by
  have h :=
    tendsto_pairedEtaBoundaryHeatFiniteArithmeticRadialFluxDiagonal
      x htau
  apply h.congr'
  exact Eventually.of_forall fun n =>
    (pairedEtaBoundaryHeatFiniteLogNormRadialFluxWindow_eq_arithmetic
      x tau (n : ℝ)
        (pairedEtaBoundaryHeatFiniteArithmeticDiagonalIndex x tau n)
        (pairedEtaBoundaryHeatFiniteArithmeticDiagonalIndex_spec
          x tau n).2.2.2).symm

end
end RiemannGaussian
